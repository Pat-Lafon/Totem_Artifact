use serial_test::serial;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, SystemTime};

mod common;
use common::{wait_with_timeout, WaitOutcome};

const ERROR_OUTPUT_LINES: usize = 200;
const COMMAND_TIMEOUT_SECS: u64 = 30; // 30 seconds

struct TestEnv {
    repo_root: PathBuf,
    cobb_dir: PathBuf,
    cobb_totem_dir: PathBuf,
}

struct DumpEntry {
    path: PathBuf,
    name: String,
    mtime: Option<SystemTime>,
}

impl TestEnv {
    fn new() -> Self {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .to_path_buf();

        Self {
            cobb_dir: repo_root.join("Cobb"),
            cobb_totem_dir: repo_root.join("Cobb_Totem"),
            repo_root,
        }
    }

    fn wait_with_timeout(
        child: std::process::Child,
        timeout_secs: u64,
        cmd_debug: &str,
    ) -> Result<std::process::Output, String> {
        let start_system = SystemTime::now();
        let outcome = wait_with_timeout(child, Duration::from_secs(timeout_secs))
            .map_err(|e| format!("Failed to wait for child: {}", e))?;
        let (stdout, stderr) = match outcome {
            WaitOutcome::Exited(output) => return Ok(output),
            WaitOutcome::TimedOut { stdout, stderr } => (stdout, stderr),
        };

        let header = format!(
            "Command timeout after {} seconds\nCommand: {}",
            timeout_secs, cmd_debug
        );

        let dumps = Self::collect_dumps();
        let latest = dumps
            .iter()
            .filter(|d| d.mtime.map_or(false, |t| t >= start_system))
            .max_by_key(|d| d.mtime);

        match latest {
            // Happy path: the in-flight Lean dump tells the whole story —
            // suppress the noisy stdout/stderr type-check spam and surface
            // the actual subtyping goal Z3 was stuck on.
            Some(d) => {
                let goal = Self::extract_failed_theorem(&d.path)
                    .unwrap_or_else(|| "<could not extract theorem from dump>".to_string());
                Err(format!(
                    "{}\nLast Lean dump from this run: {}\n--- failed subtyping goal ---\n{}",
                    header,
                    d.path.display(),
                    goal
                ))
            }
            // Cobb didn't dump anything for this run. Show the child's output
            // plus an inventory of every dump in the temp dir so we can tell
            // a real harness bug ("never reached SMT") from a clock/race issue
            // ("dump exists but mtime < start_system").
            None => Err(format!(
                "{}\nNo subtyping_failed_*.lean dumps found in {} created after run start.\n\
                 --- child stdout (last {} lines) ---\n{}\n\
                 --- child stderr (last {} lines) ---\n{}\n\
                 --- temp dir inventory ---\n{}",
                header,
                std::env::temp_dir().display(),
                ERROR_OUTPUT_LINES,
                Self::format_output(&String::from_utf8_lossy(&stdout)),
                ERROR_OUTPUT_LINES,
                Self::format_output(&String::from_utf8_lossy(&stderr)),
                Self::format_inventory(&dumps, start_system),
            )),
        }
    }

    /// Scan the system temp dir for every `subtyping_failed_*.lean` file.
    /// Returns the raw list — callers filter by mtime.
    fn collect_dumps() -> Vec<DumpEntry> {
        let temp_dir = std::env::temp_dir();
        let entries = match fs::read_dir(&temp_dir) {
            Ok(e) => e,
            Err(_) => return Vec::new(),
        };
        let mut out = Vec::new();
        for entry in entries.flatten() {
            let path = entry.path();
            let Some(name) = path.file_name().map(|n| n.to_string_lossy().into_owned()) else {
                continue;
            };
            if !name.starts_with("subtyping_failed_") || !name.ends_with(".lean") {
                continue;
            }
            let mtime = entry.metadata().and_then(|m| m.modified()).ok();
            out.push(DumpEntry { path, name, mtime });
        }
        out
    }

    /// Human-readable listing of every dump in the temp dir, flagging which
    /// ones belong to this run. Used only when no fresh dump was found.
    fn format_inventory(dumps: &[DumpEntry], since: SystemTime) -> String {
        let temp_dir = std::env::temp_dir();
        if dumps.is_empty() {
            return match fs::read_dir(&temp_dir) {
                Ok(_) => "  <no subtyping_failed_*.lean files in temp dir>".to_string(),
                Err(e) => format!("  <could not read {}: {}>", temp_dir.display(), e),
            };
        }
        let mut lines: Vec<String> = dumps
            .iter()
            .map(|d| match d.mtime {
                Some(t) => {
                    let cmp = if t >= since { "AFTER start" } else { "before start" };
                    format!("  {} mtime={:?} ({})", d.name, t, cmp)
                }
                None => format!("  {} <mtime unavailable>", d.name),
            })
            .collect();
        lines.sort();
        lines.join("\n")
    }

    /// Pull the `theorem failed_subtyping_N : <goal> := by sorry` block out
    /// of a dump file — the rest is shared preamble + axioms.
    fn extract_failed_theorem(path: &Path) -> Option<String> {
        let contents = fs::read_to_string(path).ok()?;
        let start = contents.rfind("theorem failed_subtyping_")?;
        Some(contents[start..].trim_end().to_string())
    }

    fn format_output(output: &str) -> String {
        let max_lines = ERROR_OUTPUT_LINES;
        let lines: Vec<&str> = output.lines().collect();
        // Keep the full text whenever the elision would save fewer than
        // max_lines — otherwise we'd print "0 lines omitted" boilerplate.
        if lines.len() <= max_lines * 3 {
            return output.to_string();
        }
        let head = lines[..max_lines].join("\n");
        let tail = lines[lines.len() - max_lines..].join("\n");
        let omitted = lines.len() - max_lines * 2;
        format!("{head}\n... ({omitted} lines omitted) ...\n{tail}")
    }

    fn print_debug_command(&self, cmd: &str, args: &[&str], cwd: &Path) {
        eprintln!("\n❌ To debug, run:");
        eprintln!("cd {} && {} {}", cwd.display(), cmd, args.join(" "));
    }

    fn run_generate(&self, program_file: &Path) -> Result<(), String> {
        let output_path = program_file.parent().unwrap().join("program_axioms.ml");

        // Clean up any previous axioms
        let _ = fs::remove_file(&output_path);

        let output = Command::new("cargo")
            .arg("run")
            .arg("--release")
            .arg("--")
            .arg("--export-axioms")
            .arg(&output_path)
            .arg(&program_file)
            .current_dir(&self.cobb_totem_dir)
            .output()
            .map_err(|e| format!("Failed to run cargo: {}", e))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            let formatted_err = Self::format_output(&stderr);
            eprintln!("Axiom generation failed:\n{}", formatted_err);
            self.print_debug_command(
                "cargo",
                &[
                    "run",
                    "--release",
                    "--",
                    "--export-axioms",
                    &output_path.to_string_lossy(),
                    &program_file.to_string_lossy(),
                ],
                &self.cobb_totem_dir,
            );
            return Err("Axiom generation failed (see output above)".to_string());
        }

        if !output_path.exists() {
            return Err("Axiom output file not created".to_string());
        }
        Ok(())
    }

    fn run_typecheck(&self, program_file: &Path, meta_config: &Path) -> Result<(), String> {
        use std::process::Stdio;

        let underapprox_dir = self.cobb_dir.join("underapproximation_type");

        let cmd_debug = format!(
            "cd {} && opam exec -- dune exec -- bin/main.exe type-check {} {}",
            underapprox_dir.display(),
            meta_config.display(),
            program_file.display()
        );

        let child = Command::new("opam")
            .arg("exec")
            .arg("--")
            .arg("dune")
            .arg("exec")
            .arg("--")
            .arg("bin/main.exe")
            .arg("type-check")
            .arg(&meta_config)
            .arg(&program_file)
            .current_dir(&underapprox_dir)
            .env("TOTEM_DUMP_LEAN", "1")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| {
                format!(
                    "Failed to run dune via opam: {} (cwd: {}, config: {}, program: {})",
                    e,
                    underapprox_dir.display(),
                    meta_config.display(),
                    program_file.display()
                )
            })?;

        let output = Self::wait_with_timeout(child, COMMAND_TIMEOUT_SECS, &cmd_debug)?;

        if !output.status.success() {
            let stdout = String::from_utf8_lossy(&output.stdout).to_string();
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            let formatted_out = Self::format_output(&stdout);
            let formatted_err = Self::format_output(&stderr);
            if !formatted_out.trim().is_empty() {
                eprintln!("Type checking stdout:\n{}", formatted_out);
            }
            eprintln!("Type checking failed:\n{}", formatted_err);
            self.print_debug_command(
                "opam",
                &[
                    "exec",
                    "--",
                    "dune",
                    "exec",
                    "--",
                    "bin/main.exe",
                    "type-check",
                    &meta_config.to_string_lossy(),
                    &program_file.to_string_lossy(),
                ],
                &underapprox_dir,
            );
            return Err("Type checking failed (see output above)".to_string());
        }

        Ok(())
    }

    fn run_subtypecheck(&self, program_file: &Path, meta_config: &Path) -> Result<(), String> {
        use std::process::Stdio;

        let underapprox_dir = self.cobb_dir.join("underapproximation_type");

        let cmd_debug = format!(
            "cd {} && opam exec -- dune exec -- bin/main.exe subtype-check {} {}",
            underapprox_dir.display(),
            meta_config.display(),
            program_file.display()
        );

        let child = Command::new("opam")
            .arg("exec")
            .arg("--")
            .arg("dune")
            .arg("exec")
            .arg("--")
            .arg("bin/main.exe")
            .arg("subtype-check")
            .arg(&meta_config)
            .arg(&program_file)
            .current_dir(&underapprox_dir)
            .env("TOTEM_DUMP_LEAN", "1")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| {
                format!(
                    "Failed to run dune via opam: {} (cwd: {}, config: {}, program: {})",
                    e,
                    underapprox_dir.display(),
                    meta_config.display(),
                    program_file.display()
                )
            })?;

        let output = Self::wait_with_timeout(child, COMMAND_TIMEOUT_SECS, &cmd_debug)?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            let formatted_err = Self::format_output(&stderr);
            eprintln!("Subtype checking failed:\n{}", formatted_err);
            self.print_debug_command(
                "opam",
                &[
                    "exec",
                    "--",
                    "dune",
                    "exec",
                    "--",
                    "bin/main.exe",
                    "subtype-check",
                    &meta_config.to_string_lossy(),
                    &program_file.to_string_lossy(),
                ],
                &underapprox_dir,
            );
            return Err("Subtype checking failed (see output above)".to_string());
        }

        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();

        if !stdout.contains("Result: true") && !stderr.contains("Result: true") {
            eprintln!("Subtype check passed but 'Result: true' not found in output");
            eprintln!("stdout:\n{}", Self::format_output(&stdout));
            eprintln!("stderr:\n{}", Self::format_output(&stderr));
            self.print_debug_command(
                "opam",
                &[
                    "exec",
                    "--",
                    "dune",
                    "exec",
                    "--",
                    "bin/main.exe",
                    "subtype-check",
                    &meta_config.to_string_lossy(),
                    &program_file.to_string_lossy(),
                ],
                &underapprox_dir,
            );
            return Err("Subtype check missing expected 'Result: true' output".to_string());
        }

        Ok(())
    }

    fn run_abduction(&self, test_name: &str, variant_num: u32) -> Result<(), String> {
        let test_dir = self
            .repo_root
            .join(format!("integration_tests/{}", test_name));
        let variant_file = test_dir.join(format!("{}_gen_synth_prog{}.ml", test_name, variant_num));

        if !variant_file.exists() {
            return Err(format!(
                "Abduction variant not found: {}",
                variant_file.display()
            ));
        }

        let output = Command::new("cargo")
            .arg("run")
            .arg("--manifest-path")
            .arg(self.repo_root.join("totem_runner/Cargo.toml"))
            .arg("--")
            .arg("abduction")
            .arg(&variant_file)
            .current_dir(&self.repo_root)
            .output()
            .map_err(|e| format!("Failed to run cargo: {}", e))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            let formatted_err = Self::format_output(&stderr);
            eprintln!(
                "Abduction failed for variant {}:\n{}",
                variant_num, formatted_err
            );
            self.print_debug_command(
                "cargo",
                &[
                    "run",
                    "--manifest-path",
                    "totem_runner/Cargo.toml",
                    "--",
                    "abduction",
                    &variant_file.to_string_lossy(),
                ],
                &self.repo_root,
            );
            return Err(format!(
                "Abduction failed for variant {} (see output above)",
                variant_num
            ));
        }

        Ok(())
    }

    fn run_synthesis(&self, test_name: &str, variant_num: u32) -> Result<(), String> {
        let test_dir = self
            .repo_root
            .join(format!("integration_tests/{}", test_name));
        let variant_file = test_dir.join(format!("{}_gen_synth_prog{}.ml", test_name, variant_num));

        if !variant_file.exists() {
            return Err(format!(
                "Synthesis variant not found: {}",
                variant_file.display()
            ));
        }

        let output = Command::new("cargo")
            .arg("run")
            .arg("--manifest-path")
            .arg(self.repo_root.join("totem_runner/Cargo.toml"))
            .arg("--")
            .arg("synthesis")
            .arg(&variant_file)
            .current_dir(&self.repo_root)
            .output()
            .map_err(|e| format!("Failed to run cargo: {}", e))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            let formatted_err = Self::format_output(&stderr);
            eprintln!(
                "Synthesis failed for variant {}:\n{}",
                variant_num, formatted_err
            );
            self.print_debug_command(
                "cargo",
                &[
                    "run",
                    "--manifest-path",
                    "totem_runner/Cargo.toml",
                    "--",
                    "synthesis",
                    &variant_file.to_string_lossy(),
                ],
                &self.repo_root,
            );
            return Err(format!(
                "Synthesis failed for variant {} (see output above)",
                variant_num
            ));
        }

        Ok(())
    }
}

#[test]
#[serial]
fn test_sizedlist() -> Result<(), String> {
    let env = TestEnv::new();
    let test_dir = env.repo_root.join("integration_tests/sizedlist");
    let program_file = test_dir.join("program.ml");
    let typecheck_file = test_dir.join("sizedlist_gen.ml");
    let meta_config = test_dir.join("meta-config.json");

    env.run_generate(&program_file)?;
    env.run_typecheck(&typecheck_file, &meta_config)?;

    env.run_synthesis("sizedlist", 1)?;
    env.run_synthesis("sizedlist", 2)?;

    env.run_abduction("sizedlist", 3)?;
    env.run_synthesis("sizedlist", 3)?;
    env.run_synthesis("sizedlist", 4)?;
    env.run_synthesis("sizedlist", 5)?;
    env.run_synthesis("sizedlist", 6)?;
    env.run_synthesis("sizedlist", 7)?;
    env.run_synthesis("sizedlist", 8)?;
    env.run_synthesis("sizedlist", 9)?;

    Ok(())
}

#[test]
#[serial]
fn test_sortedlist() -> Result<(), String> {
    let env = TestEnv::new();
    let test_dir = env.repo_root.join("integration_tests/sortedlist");
    let program_file = test_dir.join("program.ml");
    let typecheck_file = test_dir.join("sortedlist_gen.ml");
    let meta_config = test_dir.join("meta-config.json");

    env.run_generate(&program_file)?;
    env.run_typecheck(&typecheck_file, &meta_config)?;

    // Subtyping tests
    let subtyping_dir = test_dir.join("subtyping_tests");
    env.run_subtypecheck(&subtyping_dir.join("sorted_non_emp.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("sorted_non_emp_rev.ml"), &meta_config)?;

    env.run_abduction("sortedlist", 1)?;
    env.run_synthesis("sortedlist", 1)?;
    env.run_synthesis("sortedlist", 2)?;
    env.run_abduction("sortedlist", 3)?;
    env.run_synthesis("sortedlist", 3)?;

    Ok(())
}

#[test]
#[serial]
fn test_uniquelist() -> Result<(), String> {
    let env = TestEnv::new();
    let test_dir = env.repo_root.join("integration_tests/uniquelist");
    let _program_file = test_dir.join("program.ml");
    let typecheck_file = test_dir.join("uniquelist_gen.ml");
    let meta_config = test_dir.join("meta-config.json");

    // env.run_generate(&_program_file)?;
    env.run_typecheck(&typecheck_file, &meta_config)?;

    // Subtyping tests
    let subtyping_dir = test_dir.join("subtyping_tests");
    env.run_subtypecheck(&subtyping_dir.join("unique_emp.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("unique_emp_rev.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("unique_non_emp.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("unique_non_emp_rev.ml"), &meta_config)?;
    env.run_subtypecheck(
        &subtyping_dir.join("unique_localization_error.ml"),
        &meta_config,
    )?;

    env.run_abduction("uniquelist", 1)?;
    env.run_synthesis("uniquelist", 1)?;
    env.run_abduction("uniquelist", 2)?;
    env.run_synthesis("uniquelist", 2)?;
    env.run_abduction("uniquelist", 3)?;
    env.run_synthesis("uniquelist", 3)?;

    Ok(())
}

#[test]
#[serial]
fn test_duplicate_list() -> Result<(), String> {
    let env = TestEnv::new();
    let test_dir = env.repo_root.join("integration_tests/duplicate_list");
    let program_file = test_dir.join("program.ml");
    let typecheck_file = test_dir.join("duplicate_list_gen.ml");
    let meta_config = test_dir.join("meta-config.json");

    env.run_generate(&program_file)?;

    // Subtyping tests
    let subtyping_dir = test_dir.join("subtyping_tests");
    env.run_subtypecheck(&subtyping_dir.join("duplicate_emp.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("duplicate_emp_rev.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("duplicate_non_emp.ml"), &meta_config)?;
    env.run_subtypecheck(
        &subtyping_dir.join("duplicate_non_emp_rev.ml"),
        &meta_config,
    )?;

    env.run_typecheck(&typecheck_file, &meta_config)?;

    env.run_abduction("duplicate_list", 1)?;
    env.run_synthesis("duplicate_list", 1)?;
    env.run_abduction("duplicate_list", 2)?;
    env.run_synthesis("duplicate_list", 2)?;
    env.run_synthesis("duplicate_list", 3)?;

    Ok(())
}

#[test]
#[serial]
fn test_even_list() -> Result<(), String> {
    let env = TestEnv::new();
    let test_dir = env.repo_root.join("integration_tests/even_list");
    let _program_file = test_dir.join("program.ml");
    let typecheck_file = test_dir.join("even_list_gen.ml");
    let meta_config = test_dir.join("meta-config.json");

    // env.run_generate(&_program_file)?;

    // Subtyping tests
    let subtyping_dir = test_dir.join("subtyping_tests");
    env.run_subtypecheck(&subtyping_dir.join("even_list_empty.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("even_list_empty_rev.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("even_list_singleton.ml"), &meta_config)?;
    env.run_subtypecheck(
        &subtyping_dir.join("even_list_singleton_rev.ml"),
        &meta_config,
    )?;

    env.run_typecheck(&typecheck_file, &meta_config)?;

    env.run_abduction("even_list", 1)?;
    env.run_synthesis("even_list", 1)?;
    env.run_synthesis("even_list", 2)?;
    env.run_abduction("even_list", 3)?;
    env.run_synthesis("even_list", 3)?;
    // env.run_synthesis("even_list", 4)?;
    // env.run_synthesis("even_list", 5)?;
    // env.run_synthesis("even_list", 6)?;
    // env.run_synthesis("even_list", 7)?;

    Ok(())
}

#[test]
#[serial]
fn test_depth_tree() -> Result<(), String> {
    let env = TestEnv::new();
    let test_dir = env.repo_root.join("integration_tests/depth_tree");
    let _program_file = test_dir.join("program.ml");
    let typecheck_file = test_dir.join("depth_tree_gen.ml");
    let meta_config = test_dir.join("meta-config.json");

    // env.run_generate(&_program_file)?;

    // Subtyping tests
    let subtyping_dir = test_dir.join("subtyping_tests");
    env.run_subtypecheck(&subtyping_dir.join("leaf.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("leaf_rev.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("depth_type_check.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("depth_gen_spec.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("depth_node_bound.ml"), &meta_config)?;

    env.run_typecheck(&typecheck_file, &meta_config)?;

    env.run_abduction("depth_tree", 1)?;
    env.run_synthesis("depth_tree", 1)?;
    env.run_synthesis("depth_tree", 2)?;
    env.run_abduction("depth_tree", 3)?;
    env.run_synthesis("depth_tree", 3)?;
    // env.run_synthesis("depth_tree", 4)?;

    Ok(())
}

#[test]
#[serial]
fn test_rbtree() -> Result<(), String> {
    let env = TestEnv::new();
    let test_dir = env.repo_root.join("integration_tests/rbtree");
    let _program_file = test_dir.join("program.ml");
    let typecheck_file = test_dir.join("rbtree_gen.ml");
    let meta_config = test_dir.join("meta-config.json");

    // env.run_generate(&_program_file)?;

    // Subtyping tests
    let subtyping_dir = test_dir.join("subtyping_tests");
    env.run_subtypecheck(&subtyping_dir.join("rbleaf.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("rbleaf_rev.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("rbleaf2.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("rbleaf2_rev.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("rbnode_color_true.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("rbnode_color_true_rev.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("rbnode_color_false_node.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("rbnode_color_false_node_rev.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("rbnode_color_false_node_true.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("rbnode_color_false_node_true_rev.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("rbnode_color_false_node_false.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("rbnode_color_false_node_false_rev.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("rbnode_single.ml"), &meta_config)?;
    // env.run_subtypecheck(&subtyping_dir.join("rbnode_single_rev.ml"), &meta_config)?;

    env.run_typecheck(&typecheck_file, &meta_config)?;

    env.run_abduction("rbtree", 1)?;
    env.run_synthesis("rbtree", 1)?;
    env.run_synthesis("rbtree", 2)?;
    env.run_synthesis("rbtree", 3)?;
    env.run_abduction("rbtree", 4)?;
    env.run_synthesis("rbtree", 4)?;
    env.run_synthesis("rbtree", 5)?;
    env.run_synthesis("rbtree", 6)?;
    env.run_synthesis("rbtree", 7)?;

    Ok(())
}
