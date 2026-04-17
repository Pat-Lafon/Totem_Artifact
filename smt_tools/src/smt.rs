use std::io;
use std::path::Path;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct Assertion {
    pub qid: Option<String>,
    pub text: String,
}

#[derive(Debug, Clone)]
pub struct SmtFile {
    pub preamble: String,
    pub assertions: Vec<Assertion>,
    pub postlude: String,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Z3Result {
    Unsat,
    Sat,
    Unknown,
    Error(String),
}

impl std::fmt::Display for Z3Result {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Z3Result::Unsat => write!(f, "unsat"),
            Z3Result::Sat => write!(f, "sat"),
            Z3Result::Unknown => write!(f, "unknown"),
            Z3Result::Error(e) => write!(f, "error: {e}"),
        }
    }
}

// ---------------------------------------------------------------------------
// SMT2 file parsing
// ---------------------------------------------------------------------------

pub fn parse_smt_file(path: &Path) -> io::Result<SmtFile> {
    let content = std::fs::read_to_string(path)?;
    let mut preamble = String::new();
    let mut assertions = Vec::new();
    let mut postlude = String::new();

    let mut pos = 0;
    let mut found_assert = false;
    let mut past_last_assert = false;

    while pos < content.len() {
        while pos < content.len() && content[pos..].starts_with(|c: char| c.is_whitespace()) {
            pos += 1;
        }
        if pos >= content.len() {
            break;
        }

        if content.as_bytes()[pos] == b'(' {
            let start = pos;
            let mut depth = 0;
            let mut in_string = false;
            let bytes = content.as_bytes();
            let mut i = pos;
            while i < bytes.len() {
                match bytes[i] {
                    b'"' => in_string = !in_string,
                    b'(' if !in_string => depth += 1,
                    b')' if !in_string => {
                        depth -= 1;
                        if depth == 0 {
                            i += 1;
                            break;
                        }
                    }
                    _ => {}
                }
                i += 1;
            }
            let form = &content[start..i];
            pos = i;

            if form.starts_with("(assert ") || form.starts_with("(assert\n") {
                found_assert = true;
                assertions.push(Assertion {
                    qid: extract_qid(form),
                    text: form.to_string(),
                });
            } else if !found_assert {
                preamble.push_str(form);
                preamble.push('\n');
            } else {
                past_last_assert = true;
                postlude.push_str(form);
                postlude.push('\n');
            }
        } else {
            let start = pos;
            while pos < content.len() && content.as_bytes()[pos] != b'(' {
                pos += 1;
            }
            let text = &content[start..pos];
            if !found_assert || past_last_assert {
                if found_assert {
                    postlude.push_str(text);
                } else {
                    preamble.push_str(text);
                }
            }
        }
    }

    Ok(SmtFile {
        preamble,
        assertions,
        postlude,
    })
}

fn extract_qid(text: &str) -> Option<String> {
    let pos = text.find(":qid ")?;
    let rest = &text[pos + 5..];
    let name: String = rest
        .chars()
        .take_while(|c| !c.is_whitespace() && *c != ')')
        .collect();
    if name.is_empty() { None } else { Some(name) }
}

// ---------------------------------------------------------------------------
// Z3 runner — manages parallelism for all Z3 invocations
// ---------------------------------------------------------------------------

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

pub struct Z3Runner {
    pool: rayon::ThreadPool,
}

impl Z3Runner {
    pub fn new() -> Self {
        let workers = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4);
        Z3Runner {
            pool: rayon::ThreadPoolBuilder::new()
                .num_threads(workers)
                .build()
                .expect("failed to create rayon thread pool"),
        }
    }

    pub fn run_z3(smt_content: &str) -> (Z3Result, String) {
        let id = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
        let tmp = std::env::temp_dir().join(format!("smt_tools_{}.smt2", id));
        if let Err(e) = std::fs::write(&tmp, smt_content) {
            return (Z3Result::Error(format!("write: {e}")), String::new());
        }

        match Command::new("z3").arg("-smt2").arg(&tmp).output() {
            Ok(out) => {
                let stdout = String::from_utf8_lossy(&out.stdout).to_string();
                let first_line = stdout.lines().next().unwrap_or("").trim();
                let result = match first_line {
                    "unsat" => Z3Result::Unsat,
                    "sat" => Z3Result::Sat,
                    _ => Z3Result::Unknown,
                };
                (result, stdout)
            }
            Err(e) => (Z3Result::Error(format!("exec: {e}")), String::new()),
        }
    }

    pub fn eval(&self, smt_content: &str) -> Z3Result {
        Self::run_z3(smt_content).0
    }

    /// Run a closure on this runner's thread pool.
    pub fn install<R: Send>(&self, f: impl FnOnce() -> R + Send) -> R {
        self.pool.install(f)
    }
}

// ---------------------------------------------------------------------------
// Query builders
// ---------------------------------------------------------------------------

pub fn build_query_with_timeout(
    file: &SmtFile,
    assertion_indices: &[usize],
    timeout_ms: u32,
) -> String {
    let mut out = String::new();
    for line in file.preamble.lines() {
        out.push_str(line);
        out.push('\n');
        if line.starts_with("(set-option :rlimit") {
            out.push_str(&format!("(set-option :timeout {})\n", timeout_ms));
        }
    }
    for &idx in assertion_indices {
        out.push_str(&file.assertions[idx].text);
        out.push('\n');
    }
    out.push_str(&file.postlude);
    out
}

pub fn build_model_query(
    file: &SmtFile,
    assertion_indices: &[usize],
    timeout_ms: u32,
) -> String {
    let mut query = build_query_with_timeout(file, assertion_indices, timeout_ms);
    if let Some(pos) = query.find("(check-sat)") {
        query.truncate(pos);
    }
    query.push_str("(check-sat)\n(get-model)\n");
    query
}

pub fn assertion_name(file: &SmtFile, idx: usize) -> &str {
    file.assertions[idx].qid.as_deref().unwrap_or("(unnamed)")
}

pub fn format_names(file: &SmtFile, indices: &[usize]) -> String {
    indices
        .iter()
        .map(|&i| assertion_name(file, i))
        .collect::<Vec<_>>()
        .join(", ")
}

// ---------------------------------------------------------------------------
// Model extraction helpers
// ---------------------------------------------------------------------------

pub fn extract_model(output: &str) -> Option<String> {
    let after_sat = output
        .strip_prefix("sat\n")
        .or_else(|| output.strip_prefix("sat\r\n"))?;
    let trimmed = after_sat.trim();
    if !trimmed.starts_with('(') {
        return None;
    }
    let mut depth = 0;
    for (i, ch) in trimmed.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(trimmed[..i + 1].to_string());
                }
            }
            _ => {}
        }
    }
    None
}

pub fn preamble_with_model(preamble: &str, model: &str) -> String {
    let defined: Vec<String> = model
        .lines()
        .filter_map(|line| {
            line.trim()
                .strip_prefix("(define-fun ")
                .and_then(|rest| rest.split_whitespace().next())
                .map(|s| s.to_string())
        })
        .collect();

    let mut result = String::new();
    for line in preamble.lines() {
        let is_replaced = line.trim().starts_with("(declare-fun ")
            && line
                .trim()
                .strip_prefix("(declare-fun ")
                .and_then(|rest| rest.split_whitespace().next())
                .is_some_and(|name| defined.iter().any(|d| d == name));

        if !is_replaced {
            result.push_str(line);
            result.push('\n');
        }
    }

    let inner = model
        .trim()
        .strip_prefix('(')
        .and_then(|s| s.strip_suffix(')'))
        .unwrap_or(model);
    result.push_str(inner);
    result.push('\n');
    result
}

pub fn check_axiom_against_model(
    file: &SmtFile,
    ax_idx: usize,
    model_preamble: &str,
    timeout_ms: u32,
) -> Z3Result {
    let axiom_text = &file.assertions[ax_idx].text;
    let inner = axiom_text
        .strip_prefix("(assert ")
        .and_then(|s| s.strip_suffix(')'))
        .unwrap_or(axiom_text);

    let mut query = model_preamble.to_string();
    query.push_str(&format!("(set-option :timeout {})\n", timeout_ms));
    query.push_str(&format!("(assert (not {}))\n", inner));
    query.push_str("(check-sat)\n");
    Z3Runner::run_z3(&query).0
}
