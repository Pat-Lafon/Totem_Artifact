use std::io;
use std::process::Command;
use std::str::FromStr;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    Unsat,
    Sat,
    Unknown,
}

/// Returned by `<Verdict as FromStr>::from_str` for any input that isn't
/// one of the three SMT-LIB check-sat tokens. The error carries the
/// offending input so callers can surface it without re-stringifying.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseVerdictError(pub String);

impl std::fmt::Display for ParseVerdictError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "unrecognized z3 verdict {:?}", self.0)
    }
}

impl std::error::Error for ParseVerdictError {}

impl FromStr for Verdict {
    type Err = ParseVerdictError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "unsat" => Ok(Verdict::Unsat),
            "sat" => Ok(Verdict::Sat),
            "unknown" => Ok(Verdict::Unknown),
            other => Err(ParseVerdictError(other.to_string())),
        }
    }
}

pub type Z3Result = Result<Verdict, Z3Error>;

/// Failure modes for `run_z3`. Per root `CLAUDE.md`, every variant is
/// "fatal before verdict": the query is malformed, the binary is
/// missing, or Z3 bailed out before producing a recognized first-line
/// answer.
#[derive(Debug)]
#[non_exhaustive]
pub enum Z3Error {
    /// `smt_tools::validate` rejected the query before we touched Z3.
    ValidatorRejected(String),
    /// An IO operation surrounding the Z3 invocation failed — either
    /// writing the query to the scratch file or spawning the binary.
    /// `op` is the operation name for messages; callers can inspect
    /// `source.kind()` (e.g. `ErrorKind::NotFound` from a spawn means
    /// z3 is missing from PATH) if they need finer discrimination.
    Io {
        op: &'static str,
        source: io::Error,
    },
    /// Z3 ran but did not produce a usable verdict: `(error …)` on
    /// stdout, anything on stderr, empty stdout, or an unrecognized
    /// first line. `detail` carries the specific cause.
    Z3Misbehaved {
        detail: String,
        exit_code: Option<i32>,
    },
}

impl std::fmt::Display for Verdict {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Verdict::Unsat => write!(f, "unsat"),
            Verdict::Sat => write!(f, "sat"),
            Verdict::Unknown => write!(f, "unknown"),
        }
    }
}

impl std::fmt::Display for Z3Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Z3Error::ValidatorRejected(msg) => write!(f, "{msg}"),
            Z3Error::Io { op, source } => write!(f, "{op}: {source}"),
            Z3Error::Z3Misbehaved { detail, exit_code } => {
                write!(f, "{detail} (exit status {exit_code:?})")
            }
        }
    }
}

impl std::error::Error for Z3Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Z3Error::Io { source, .. } => Some(source),
            _ => None,
        }
    }
}

pub fn run_z3(smt_content: &str) -> Z3Result {
    // Validate before invocation — catches the malformed-query class of
    // bugs (e.g. model entries with forward references) at construction
    // time rather than letting Z3 emit `(error ...)` on stdout.
    crate::validate::validate_or_err(smt_content, "run_z3").map_err(Z3Error::ValidatorRejected)?;

    // `TempPath` deletes the file on drop, so /tmp doesn't accumulate
    // `smt_tools_*.smt2` files across runs.
    let tmp_path = tempfile::Builder::new()
        .prefix("smt_tools_")
        .suffix(".smt2")
        .tempfile()
        .map_err(|source| Z3Error::Io {
            op: "creating scratch tempfile",
            source,
        })?
        .into_temp_path();
    std::fs::write(&tmp_path, smt_content).map_err(|source| Z3Error::Io {
        op: "writing query to scratch file",
        source,
    })?;

    let out = Command::new("z3")
        .arg("-smt2")
        .arg(&tmp_path)
        .output()
        .map_err(|source| Z3Error::Io {
            op: "spawning z3",
            source,
        })?;

    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    let exit_code = out.status.code();
    let misbehaved = |detail: String| Z3Error::Z3Misbehaved { detail, exit_code };

    if let Some(err_line) = stdout
        .lines()
        .find(|l| l.trim_start().starts_with("(error "))
    {
        return Err(misbehaved(format!(
            "z3 emitted error on stdout: {}",
            err_line.trim()
        )));
    }
    if !stderr.trim().is_empty() {
        return Err(misbehaved(format!("z3 wrote to stderr: {}", stderr.trim())));
    }

    // Empty / whitespace-only stdout is a distinct failure mode from
    // "unrecognized token"; surface it before handing the line to
    // `FromStr` so the diagnostic stays specific.
    stdout
        .lines()
        .next()
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .ok_or_else(|| misbehaved("z3 produced no output".to_string()))?
        .parse::<Verdict>()
        .map_err(|e| misbehaved(format!("z3 produced unrecognized first line {:?}", e.0)))
}
