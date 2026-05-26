//! Encoding parity test: Cobb-direct SMT vs Lean-elaborated SMT.
//!
//! For every `integration_tests/<bench>/subtyping_tests/*.ml` Cobb's
//! `subtype-check` writes `subtyping_temp_file.smt2` and dumps one or
//! more `/tmp/subtyping_failed_<i>.lean` files (paths announced on
//! stderr). The patched Lean file is elaborated, which re-emits SMT-LIB,
//! and Z3 is run on both encodings. Verdicts must match (`Sat`/`Sat` or
//! `Unsat`/`Unsat`); any `Unknown` is reported as a failure.

use serial_test::serial;
use smt_tools::smt::{run_z3, Verdict};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Duration;

mod common;
use common::{wait_with_timeout, WaitOutcome};

const COBB_TIMEOUT: Duration = Duration::from_secs(90);
const LEAN_TIMEOUT: Duration = Duration::from_secs(180);

#[derive(Clone)]
struct Case {
    name: String,
    test_file: PathBuf,
    meta_config: PathBuf,
    output_dir: PathBuf,
}

fn discover_cases(repo_root: &Path) -> Vec<Case> {
    let mut cases = Vec::new();
    let it_dir = repo_root.join("integration_tests");
    let benches = fs::read_dir(&it_dir)
        .unwrap_or_else(|e| panic!("read_dir {}: {e}", it_dir.display()));
    for entry in benches.flatten() {
        let bench_dir = entry.path();
        if !bench_dir.is_dir() {
            continue;
        }
        let bench_name = bench_dir.file_name().unwrap().to_str().unwrap().to_string();
        let meta_config = bench_dir.join("meta-config.json");
        if !meta_config.exists() {
            continue;
        }
        let st_dir = bench_dir.join("subtyping_tests");
        if !st_dir.is_dir() {
            continue;
        }
        let mut entries: Vec<_> = fs::read_dir(&st_dir)
            .unwrap_or_else(|e| panic!("read_dir {}: {e}", st_dir.display()))
            .flatten()
            .collect();
        entries.sort_by_key(|e| e.path());
        for ml in entries {
            let path = ml.path();
            if path.extension().and_then(|e| e.to_str()) != Some("ml") {
                continue;
            }
            let stem = path.file_stem().unwrap().to_str().unwrap().to_string();
            cases.push(Case {
                name: format!("{bench_name}::{stem}"),
                test_file: path,
                meta_config: meta_config.clone(),
                output_dir: bench_dir.join("encoding_dumps").join(&stem),
            });
        }
    }
    cases.sort_by(|a, b| a.name.cmp(&b.name));
    cases
}

struct CobbArtifacts {
    smt: PathBuf,
    lean_dumps: Vec<(usize, PathBuf)>,
}

fn parse_dump_line(line: &str) -> Option<(usize, PathBuf)> {
    let path = line.strip_prefix("Dumped failed subtyping query to ")?.trim();
    let idx = Path::new(path)
        .file_stem()?
        .to_str()?
        .strip_prefix("subtyping_failed_")?
        .parse()
        .ok()?;
    Some((idx, PathBuf::from(path)))
}

fn run_cobb_subtype(underapprox_dir: &Path, case: &Case) -> Result<CobbArtifacts, String> {
    let cobb_smt = underapprox_dir.join("subtyping_temp_file.smt2");
    let _ = fs::remove_file(&cobb_smt);
    if case.output_dir.exists() {
        fs::remove_dir_all(&case.output_dir)
            .map_err(|e| format!("remove {}: {e}", case.output_dir.display()))?;
    }
    fs::create_dir_all(&case.output_dir)
        .map_err(|e| format!("create {}: {e}", case.output_dir.display()))?;

    let child = Command::new("opam")
        .args(["exec", "--", "dune", "exec", "--", "bin/main.exe", "subtype-check"])
        .arg(&case.meta_config)
        .arg(&case.test_file)
        .current_dir(underapprox_dir)
        .env("TOTEM_DUMP_LEAN", "1")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("dune exec spawn: {e}"))?;
    let stderr = match wait_with_timeout(child, COBB_TIMEOUT)
        .map_err(|e| format!("dune exec wait: {e}"))?
    {
        WaitOutcome::Exited(o) => String::from_utf8_lossy(&o.stderr).into_owned(),
        WaitOutcome::TimedOut { stderr, .. } => {
            return Err(format!(
                "dune exec timed out after {}s; stderr:\n{}",
                COBB_TIMEOUT.as_secs(),
                String::from_utf8_lossy(&stderr)
            ));
        }
    };

    if !cobb_smt.exists() {
        return Err(format!(
            "Cobb did not produce {}. stderr:\n{stderr}",
            cobb_smt.display()
        ));
    }
    let smt_dest = case.output_dir.join("query.cobb.smt2");
    fs::copy(&cobb_smt, &smt_dest)
        .map_err(|e| format!("copy {} -> {}: {e}", cobb_smt.display(), smt_dest.display()))?;

    let mut lean_dumps = Vec::new();
    for line in stderr.lines() {
        let Some((idx, src)) = parse_dump_line(line) else { continue };
        let dest = case.output_dir.join(format!("query_{idx}.lean"));
        fs::copy(&src, &dest)
            .map_err(|e| format!("copy {} -> {}: {e}", src.display(), dest.display()))?;
        lean_dumps.push((idx, dest));
    }
    if lean_dumps.is_empty() {
        return Err(format!("Cobb produced no Lean dumps. stderr:\n{stderr}"));
    }
    Ok(CobbArtifacts { smt: smt_dest, lean_dumps })
}

fn run_lean_leg(
    repo_root: &Path,
    case_dir: &Path,
    idx: usize,
    lean_path: &Path,
) -> Result<PathBuf, String> {
    let theorem = format!("failed_subtyping_{idx}");
    let original = fs::read_to_string(lean_path)
        .map_err(|e| format!("read {}: {e}", lean_path.display()))?;
    let patched = format!("{original}\n\nz3_auto? {theorem}\n");
    let patched_path = case_dir.join(format!("query_{idx}.patched.lean"));
    fs::write(&patched_path, &patched)
        .map_err(|e| format!("write {}: {e}", patched_path.display()))?;

    let child = Command::new("lake")
        .args(["env", "lean"])
        .arg(&patched_path)
        .current_dir(repo_root)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("lake env lean spawn: {e}"))?;
    let (success, combined) = match wait_with_timeout(child, LEAN_TIMEOUT)
        .map_err(|e| format!("lake wait: {e}"))?
    {
        WaitOutcome::Exited(o) => (
            o.status.success(),
            format!(
                "{}\n{}",
                String::from_utf8_lossy(&o.stdout),
                String::from_utf8_lossy(&o.stderr)
            ),
        ),
        WaitOutcome::TimedOut { stdout, stderr } => {
            return Err(format!(
                "lake env lean timed out after {}s; output:\n{}\n{}",
                LEAN_TIMEOUT.as_secs(),
                String::from_utf8_lossy(&stdout),
                String::from_utf8_lossy(&stderr)
            ));
        }
    };

    let smt_src = combined
        .lines()
        .find_map(|l| l.split_once("SMT-LIB query written to ").map(|(_, r)| r.trim()))
        .map(PathBuf::from)
        .ok_or_else(|| {
            format!(
                "Lean did not emit `SMT-LIB query written to ...` (success={success}). \
                 Output:\n{combined}"
            )
        })?;
    if !smt_src.exists() {
        return Err(format!(
            "Lean reported {} but file missing. Output:\n{combined}",
            smt_src.display()
        ));
    }
    let dest = case_dir.join(format!("query_{idx}.lean.smt2"));
    fs::copy(&smt_src, &dest)
        .map_err(|e| format!("copy {} -> {}: {e}", smt_src.display(), dest.display()))?;
    Ok(dest)
}

#[derive(Debug)]
struct Failure {
    case: String,
    stage: &'static str,
    detail: String,
}

fn z3_verdict(path: &Path) -> Result<Verdict, String> {
    let content = fs::read_to_string(path).map_err(|e| format!("read {}: {e}", path.display()))?;
    run_z3(&content).map_err(|e| e.to_string())
}

fn check_case(repo_root: &Path, case: &Case, cobb: &CobbArtifacts) -> Vec<Failure> {
    let mut fails = Vec::new();
    let verdict_a = match z3_verdict(&cobb.smt) {
        Ok(v) => v,
        Err(e) => {
            fails.push(Failure { stage: "cobb-z3", case: case.name.clone(), detail: e });
            return fails;
        }
    };
    for (idx, lean_path) in &cobb.lean_dumps {
        let case_id = format!("{}#{idx}", case.name);
        let lean_smt = match run_lean_leg(repo_root, &case.output_dir, *idx, lean_path) {
            Ok(p) => p,
            Err(e) => {
                fails.push(Failure { stage: "lean", case: case_id, detail: e });
                continue;
            }
        };
        let verdict_b = match z3_verdict(&lean_smt) {
            Ok(v) => v,
            Err(e) => {
                fails.push(Failure { stage: "lean-z3", case: case_id, detail: e });
                continue;
            }
        };
        let agree = matches!(
            (verdict_a, verdict_b),
            (Verdict::Sat, Verdict::Sat) | (Verdict::Unsat, Verdict::Unsat)
        );
        if !agree {
            fails.push(Failure {
                stage: "verdict",
                case: case_id,
                detail: format!("cobb={verdict_a:?} lean={verdict_b:?}"),
            });
        }
    }
    fails
}

#[test]
#[serial]
fn encoding_verdict() {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("CARGO_MANIFEST_DIR has no parent")
        .to_path_buf();
    let underapprox_dir = repo_root.join("Cobb").join("underapproximation_type");
    let cases = discover_cases(&repo_root);
    assert!(
        !cases.is_empty(),
        "no integration_tests/<bench>/subtyping_tests/*.ml cases discovered"
    );
    eprintln!("encoding_verdict: {} cases", cases.len());

    let mut failures: Vec<Failure> = Vec::new();
    for case in &cases {
        match run_cobb_subtype(&underapprox_dir, case) {
            Ok(art) => failures.extend(check_case(&repo_root, case, &art)),
            Err(e) => failures.push(Failure {
                stage: "cobb",
                case: case.name.clone(),
                detail: e,
            }),
        }
    }

    if !failures.is_empty() {
        let mut report = format!(
            "\n{} encoding-parity failures across {} cases:\n\n",
            failures.len(),
            cases.len()
        );
        for f in &failures {
            report.push_str(&format!("  [{}] {}\n    {}\n", f.stage, f.case, f.detail));
        }
        panic!("{report}");
    }
}
