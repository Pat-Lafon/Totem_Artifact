use std::collections::HashMap;
use std::io;
use std::path::Path;

use memmap2::Mmap;

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/// Compact quantifier index.
type QIdx = u32;
const UNKNOWN_QUANT: QIdx = u32::MAX;

/// A quantifier definition from the trace log.
struct QuantDef {
    qid: String,
}

/// An [mk-app] entry for datatype axiom resolution.
struct MkApp {
    func: String,
    args: Vec<String>,
}

/// Per-quantifier instantiation stats.
#[derive(Debug)]
pub struct QuantStats {
    pub qid: String,
    pub term_id: String,
    pub count: u64,
}

/// An edge in the trigger graph: quantifier A triggers quantifier B.
pub struct TriggerEdge {
    pub from_qid: String,
    pub to_qid: String,
    pub count: u64,
}

/// Full profiling result.
pub struct ProfileResult {
    pub stats: Vec<QuantStats>,
    pub triggers: Vec<TriggerEdge>,
}

// ---------------------------------------------------------------------------
// Intern table for quantifier IDs: string term_id <-> QIdx
// ---------------------------------------------------------------------------

struct QuantIntern {
    to_idx: HashMap<Box<str>, QIdx>,
    to_str: Vec<Box<str>>,
}

impl QuantIntern {
    fn new() -> Self {
        Self {
            to_idx: HashMap::new(),
            to_str: Vec::new(),
        }
    }

    fn intern(&mut self, s: &str) -> QIdx {
        if let Some(&idx) = self.to_idx.get(s) {
            return idx;
        }
        let idx = self.to_str.len() as QIdx;
        let boxed: Box<str> = s.into();
        self.to_idx.insert(boxed.clone(), idx);
        self.to_str.push(boxed);
        idx
    }

    fn name(&self, idx: QIdx) -> &str {
        &self.to_str[idx as usize]
    }
}

// ---------------------------------------------------------------------------
// Fast line iteration over mmap
// ---------------------------------------------------------------------------

struct LineIter<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> LineIter<'a> {
    fn new(data: &'a [u8]) -> Self {
        Self { data, pos: 0 }
    }
}

impl<'a> Iterator for LineIter<'a> {
    type Item = &'a [u8];

    #[inline]
    fn next(&mut self) -> Option<&'a [u8]> {
        if self.pos >= self.data.len() {
            return None;
        }
        let start = self.pos;
        // Use memchr for SIMD-accelerated newline search
        match memchr::memchr(b'\n', &self.data[start..]) {
            Some(offset) => {
                self.pos = start + offset + 1;
                Some(&self.data[start..start + offset])
            }
            None => {
                self.pos = self.data.len();
                Some(&self.data[start..])
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Inline helpers for fast byte-slice parsing
// ---------------------------------------------------------------------------

/// Skip past a known prefix, returning the rest.
#[inline]
fn after_prefix<'a>(line: &'a [u8], prefix: &[u8]) -> Option<&'a [u8]> {
    if line.starts_with(prefix) {
        Some(&line[prefix.len()..])
    } else {
        None
    }
}

/// Return the next whitespace-delimited token starting at `pos`,
/// advancing `pos` past it and the following whitespace.
#[inline]
fn next_token<'a>(data: &'a [u8], pos: &mut usize) -> Option<&'a [u8]> {
    // skip leading whitespace
    while *pos < data.len() && data[*pos] == b' ' {
        *pos += 1;
    }
    if *pos >= data.len() {
        return None;
    }
    let start = *pos;
    while *pos < data.len() && data[*pos] != b' ' && data[*pos] != b'\n' && data[*pos] != b'\r' {
        *pos += 1;
    }
    Some(&data[start..*pos])
}

/// Convert a byte-slice token to a str (assumes valid UTF-8 from Z3 trace).
#[inline]
fn tok_str(tok: &[u8]) -> &str {
    unsafe { std::str::from_utf8_unchecked(tok) }
}

/// Strip leading '#' from a term id token.
#[inline]
fn strip_hash(tok: &[u8]) -> &str {
    if tok.first() == Some(&b'#') {
        tok_str(&tok[1..])
    } else {
        tok_str(tok)
    }
}

/// Fast u64 parse from ASCII decimal digits.
#[inline]
fn parse_u64(bytes: &[u8]) -> u64 {
    let mut val: u64 = 0;
    for &b in bytes {
        if b < b'0' || b > b'9' {
            break;
        }
        val = val.wrapping_mul(10).wrapping_add((b - b'0') as u64);
    }
    val
}

// ---------------------------------------------------------------------------
// Datatype axiom resolution (same logic as before)
// ---------------------------------------------------------------------------

fn resolve_datatype_axiom(
    quant_id: &str,
    qid: &str,
    mk_apps: &HashMap<String, MkApp>,
) -> Option<String> {
    if qid != "constructor_accessor_axiom" {
        return None;
    }

    let mut constructors: HashMap<String, String> = HashMap::new();
    for (tid, app) in mk_apps {
        if app.func == "pattern" && app.args.len() == 1 {
            if let Some(ctor_app) = mk_apps.get(&app.args[0]) {
                constructors.insert(app.args[0].clone(), ctor_app.func.clone());
                constructors.insert(tid.clone(), format!("pattern({})", ctor_app.func));
            }
        }
    }

    let ctor_names: Vec<String> = constructors.values().cloned().collect();
    let skip = ["=", "pattern"];

    let mut selector_info: Vec<(String, String, String)> = Vec::new();
    for (tid, app) in mk_apps {
        if !tid.starts_with("datatype#") {
            continue;
        }
        if skip.contains(&app.func.as_str()) || ctor_names.iter().any(|c| c == &app.func) {
            continue;
        }
        if app.args.len() == 1 {
            if let Some(ctor_name) = constructors.get(&app.args[0]) {
                if !ctor_name.starts_with("pattern(") {
                    selector_info.push((tid.clone(), app.func.clone(), ctor_name.clone()));
                }
            }
        }
    }

    let quant_num: Option<usize> = quant_id
        .strip_prefix("datatype#")
        .and_then(|n| n.parse().ok());

    if let Some(qn) = quant_num {
        let mut best: Option<(usize, &str, &str)> = None;
        for (tid, sel, ctor) in &selector_info {
            if let Some(n) = tid
                .strip_prefix("datatype#")
                .and_then(|n| n.parse::<usize>().ok())
            {
                if n < qn {
                    let dist = qn - n;
                    if best.is_none() || dist < best.unwrap().0 {
                        best = Some((dist, sel, ctor));
                    }
                }
            }
        }
        if let Some((_, sel, ctor)) = best {
            return Some(format!("{sel}({ctor}(..))"));
        }
    }

    None
}

// ---------------------------------------------------------------------------
// Core parser: mmap + memchr, with trigger tracking
// ---------------------------------------------------------------------------

/// Parse a Z3 trace log and return instantiation counts + trigger graph.
///
/// Trace format (from `z3 trace=true proof=true`):
///   [mk-app]       #ID <func> <arg-ids...>
///   [mk-quant]     ID <qid> <num-vars> <pattern-ids...>
///   [new-match]    <fingerprint> QUANT_ID <pattern-id> <bound-terms> ; <blamed-enodes>
///   [instance]     <fingerprint> ...
///   [end-of-instance]
///
/// Trigger tracking:
///   - After [instance], any [mk-app] #ID ... lines create terms "yielded" by
///     that instance's quantifier.
///   - term_id -> producing quantifier is stored in `term_producer`.
///   - On [new-match], the blamed e-nodes (after ;) are looked up in term_producer
///     to find which quantifier triggered this match.
pub fn profile_trace(path: &Path) -> io::Result<ProfileResult> {
    let file = std::fs::File::open(path)?;
    let mmap = unsafe { Mmap::map(&file)? };
    let lines = LineIter::new(&mmap);

    // Quantifier intern table
    let mut qi = QuantIntern::new();
    // term_id (interned string) -> QuantDef
    let mut quant_defs: HashMap<QIdx, QuantDef> = HashMap::new();
    // datatype# mk-app entries for resolving constructor_accessor_axioms
    let mut datatype_apps: HashMap<String, MkApp> = HashMap::new();
    // fingerprint (parsed as u64) -> quant index
    let mut fingerprint_to_quant: HashMap<u64, QIdx> = HashMap::new();
    // quant index -> instance count
    let mut inst_counts: Vec<u64> = Vec::new();
    // term_id (#NNN) -> producing quant index
    let mut term_producer: HashMap<u64, QIdx> = HashMap::new();
    // trigger edges: (from_qidx, to_qidx) -> count
    let mut trigger_counts: HashMap<(QIdx, QIdx), u64> = HashMap::new();
    // The quantifier of the most recent [instance]
    let mut current_inst_quant: QIdx = UNKNOWN_QUANT;

    // Prefixes as byte slices for fast matching
    const P_MK_APP: &[u8] = b"[mk-app] ";
    const P_MK_QUANT: &[u8] = b"[mk-quant] ";
    const P_NEW_MATCH: &[u8] = b"[new-match] ";
    const P_INSTANCE: &[u8] = b"[instance] ";
    const P_END_INST: &[u8] = b"[end-of-instance]";

    for line in lines {
        // Fast dispatch on the first byte after '['
        if line.len() < 4 || line[0] != b'[' {
            continue;
        }

        match line[1] {
            b'm' => {
                if let Some(rest) = after_prefix(line, P_MK_APP) {
                    // [mk-app] #ID func args...
                    let mut pos = 0;
                    let Some(id_tok) = next_token(rest, &mut pos) else {
                        continue;
                    };

                    // Track datatype# entries for axiom resolution
                    if id_tok.starts_with(b"datatype#") {
                        let id_str = tok_str(id_tok).to_string();
                        let Some(func_tok) = next_token(rest, &mut pos) else {
                            continue;
                        };
                        let func = tok_str(func_tok).to_string();
                        let mut args = Vec::new();
                        while let Some(arg_tok) = next_token(rest, &mut pos) {
                            args.push(tok_str(arg_tok).to_string());
                        }
                        datatype_apps.insert(id_str, MkApp { func, args });
                        continue;
                    }

                    // Track term_id -> producing quantifier for trigger analysis
                    if current_inst_quant != UNKNOWN_QUANT && id_tok.starts_with(b"#") {
                        let num = parse_u64(&id_tok[1..]);
                        term_producer.insert(num, current_inst_quant);
                    }
                } else if let Some(rest) = after_prefix(line, P_MK_QUANT) {
                    // [mk-quant] ID qid num-vars patterns...
                    let mut pos = 0;
                    let Some(id_tok) = next_token(rest, &mut pos) else {
                        continue;
                    };
                    let Some(qid_tok) = next_token(rest, &mut pos) else {
                        continue;
                    };
                    let id_str = strip_hash(id_tok);
                    let qidx = qi.intern(id_str);
                    // Ensure inst_counts is large enough
                    if qidx as usize >= inst_counts.len() {
                        inst_counts.resize(qidx as usize + 1, 0);
                    }
                    quant_defs.insert(
                        qidx,
                        QuantDef {
                            qid: tok_str(qid_tok).to_string(),
                        },
                    );
                }
            }
            b'n' => {
                if let Some(rest) = after_prefix(line, P_NEW_MATCH) {
                    // [new-match] fingerprint QUANT_ID pattern bound... ; blamed...
                    let mut pos = 0;
                    let Some(fp_tok) = next_token(rest, &mut pos) else {
                        continue;
                    };
                    let Some(quant_tok) = next_token(rest, &mut pos) else {
                        continue;
                    };
                    let quant_str = strip_hash(quant_tok);
                    let qidx = qi.intern(quant_str);
                    if qidx as usize >= inst_counts.len() {
                        inst_counts.resize(qidx as usize + 1, 0);
                    }

                    fingerprint_to_quant.insert(parse_u64(fp_tok), qidx);

                    // Parse blamed e-nodes after ';' for trigger analysis
                    // Find the semicolon
                    if let Some(semi_pos) = memchr::memchr(b';', rest) {
                        let blamed_part = &rest[semi_pos + 1..];
                        let mut bpos = 0;
                        while let Some(blamed_tok) = next_token(blamed_part, &mut bpos) {
                            if blamed_tok.starts_with(b"#") {
                                let num = parse_u64(&blamed_tok[1..]);
                                if let Some(&producer) = term_producer.get(&num) {
                                    if producer != qidx {
                                        *trigger_counts
                                            .entry((producer, qidx))
                                            .or_insert(0) += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            b'i' => {
                if let Some(rest) = after_prefix(line, P_INSTANCE) {
                    // [instance] fingerprint ...
                    let mut pos = 0;
                    let Some(fp_tok) = next_token(rest, &mut pos) else {
                        continue;
                    };
                    let fp_val = parse_u64(fp_tok);

                    if let Some(&qidx) = fingerprint_to_quant.get(&fp_val) {
                        inst_counts[qidx as usize] += 1;
                        current_inst_quant = qidx;
                    } else {
                        // 0x0 fingerprint: axiom/theory instance
                        if let Some(term_tok) = next_token(rest, &mut pos) {
                            let term_str = strip_hash(term_tok);
                            let qidx = qi.intern(term_str);
                            if qidx as usize >= inst_counts.len() {
                                inst_counts.resize(qidx as usize + 1, 0);
                            }
                            inst_counts[qidx as usize] += 1;
                            current_inst_quant = qidx;
                        }
                    }
                }
            }
            b'e' => {
                if line.starts_with(P_END_INST) {
                    current_inst_quant = UNKNOWN_QUANT;
                }
            }
            _ => {}
        }
    }

    // Build stats
    let mut stats: Vec<QuantStats> = inst_counts
        .iter()
        .enumerate()
        .filter(|&(_, count)| *count > 0)
        .map(|(idx, &count)| {
            let term_id = qi.name(idx as QIdx).to_string();
            let qid = quant_defs
                .get(&(idx as QIdx))
                .map(|def| {
                    if def.qid == "constructor_accessor_axiom" {
                        let resolved =
                            resolve_datatype_axiom(&term_id, &def.qid, &datatype_apps);
                        match resolved {
                            Some(desc) => format!("{} [{}]", def.qid, desc),
                            None => def.qid.clone(),
                        }
                    } else {
                        def.qid.clone()
                    }
                })
                .unwrap_or_else(|| format!("#{term_id}"));
            QuantStats {
                qid,
                term_id: format!("#{term_id}"),
                count,
            }
        })
        .collect();
    stats.sort_by(|a, b| b.count.cmp(&a.count));

    // Build trigger edges
    let mut triggers: Vec<TriggerEdge> = trigger_counts
        .into_iter()
        .map(|((from, to), count)| {
            let from_name = qi.name(from);
            let to_name = qi.name(to);
            let from_qid = quant_defs
                .get(&from)
                .map(|d| d.qid.clone())
                .unwrap_or_else(|| format!("#{from_name}"));
            let to_qid = quant_defs
                .get(&to)
                .map(|d| d.qid.clone())
                .unwrap_or_else(|| format!("#{to_name}"));
            TriggerEdge {
                from_qid,
                to_qid,
                count,
            }
        })
        .collect();
    triggers.sort_by(|a, b| b.count.cmp(&a.count));

    Ok(ProfileResult { stats, triggers })
}

// ---------------------------------------------------------------------------
// Z3 runner
// ---------------------------------------------------------------------------

fn run_z3_with_trace(
    smt_file: &Path,
    trace_output: &Path,
) -> io::Result<std::process::ExitStatus> {
    std::process::Command::new("z3")
        .arg("trace=true")
        .arg("proof=true")
        .arg(format!("trace-file-name={}", trace_output.display()))
        .arg("-smt2")
        .arg(smt_file)
        .status()
}

pub fn profile_smt_file(smt_file: &Path) -> io::Result<ProfileResult> {
    let trace_path = smt_file.with_extension("z3trace.log");

    eprintln!("Running Z3 with tracing on {}...", smt_file.display());
    let status = run_z3_with_trace(smt_file, &trace_path)?;
    eprintln!("Z3 exited with: {status}");

    eprintln!("Parsing trace log {}...", trace_path.display());
    profile_trace(&trace_path)
}

// ---------------------------------------------------------------------------
// Display
// ---------------------------------------------------------------------------

pub fn print_stats(stats: &[QuantStats]) {
    if stats.is_empty() {
        println!("No quantifier instantiations found.");
        return;
    }
    let total: u64 = stats.iter().map(|s| s.count).sum();
    let qid_width = stats.iter().map(|s| s.qid.len()).max().unwrap_or(20).max(3);
    let rule_len = 14 + qid_width + 20;
    println!("\n{:<12} {:<qid_width$} {}", "Count", "QID", "Term ID");
    println!("{}", "-".repeat(rule_len));
    for s in stats {
        let pct = (s.count as f64 / total as f64) * 100.0;
        println!(
            "{:<12} {:<qid_width$} {} ({:.1}%)",
            s.count, s.qid, s.term_id, pct
        );
    }
    println!("{}", "-".repeat(rule_len));
    println!("Total (shown): {total}");
}

pub fn print_triggers(triggers: &[TriggerEdge], top_n: usize) {
    if triggers.is_empty() {
        println!("\nNo trigger edges found.");
        return;
    }

    let shown: Vec<&TriggerEdge> = triggers.iter().take(top_n).collect();
    let from_width = shown
        .iter()
        .map(|e| e.from_qid.len())
        .max()
        .unwrap_or(10)
        .max(4);
    let to_width = shown
        .iter()
        .map(|e| e.to_qid.len())
        .max()
        .unwrap_or(10)
        .max(4);

    let rule_len = 14 + from_width + 4 + to_width;
    println!(
        "\n{:<12} {:<from_width$} -> {}",
        "Count", "From", "To"
    );
    println!("{}", "-".repeat(rule_len));
    for e in &shown {
        println!(
            "{:<12} {:<from_width$} -> {}",
            e.count, e.from_qid, e.to_qid
        );
    }
    println!("{}", "-".repeat(rule_len));

    // Also print per-quantifier trigger summary for the hottest quantifiers
    let mut triggered_by: HashMap<&str, Vec<(&str, u64)>> = HashMap::new();
    let mut triggers_to: HashMap<&str, Vec<(&str, u64)>> = HashMap::new();
    for e in triggers {
        triggered_by
            .entry(&e.to_qid)
            .or_default()
            .push((&e.from_qid, e.count));
        triggers_to
            .entry(&e.from_qid)
            .or_default()
            .push((&e.to_qid, e.count));
    }

    // Show top triggered-by for the hottest targets
    println!("\n--- Triggered-by summary (top targets) ---");
    let mut by_total: Vec<(&str, u64)> = triggered_by
        .iter()
        .map(|(k, v)| (*k, v.iter().map(|(_, c)| c).sum()))
        .collect();
    by_total.sort_by(|a, b| b.1.cmp(&a.1));

    for (target, _total) in by_total.iter().take(10) {
        let sources = triggered_by.get(target).unwrap();
        let mut sorted = sources.clone();
        sorted.sort_by(|a, b| b.1.cmp(&a.1));
        println!("\n  {} triggered by:", target);
        for (src, count) in sorted.iter().take(5) {
            println!("    {:<12} {}", count, src);
        }
    }
}
