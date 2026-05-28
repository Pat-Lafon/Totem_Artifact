use serial_test::serial;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Duration;

mod common;
use common::{wait_with_timeout, WaitOutcome};

const ERROR_OUTPUT_LINES: usize = 200;
const COMMAND_TIMEOUT_SECS: u64 = 30; // 30 seconds

struct TestEnv {
    repo_root: PathBuf,
    cobb_dir: PathBuf,
    cobb_totem_dir: PathBuf,
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

        let stderr_str = String::from_utf8_lossy(&stderr);
        let latest_dump = Self::latest_lean_dump_from_stderr(&stderr_str);

        match latest_dump {
            // The in-flight Lean dump tells the whole story — suppress the
            // noisy stdout/stderr type-check spam and surface the actual
            // subtyping goal Z3 was stuck on.
            Some(path) => {
                let goal = Self::extract_failed_theorem(&path)
                    .unwrap_or_else(|| "<could not extract theorem from dump>".to_string());
                Err(format!(
                    "{}\nLast Lean dump from this run: {}\n--- failed subtyping goal ---\n{}",
                    header,
                    path.display(),
                    goal
                ))
            }
            // Cobb didn't announce a dump on stderr — show the child's
            // output so we can diagnose whether it never reached SMT.
            None => Err(format!(
                "{}\nNo `Dumped failed subtyping query to ...` line found on child stderr.\n\
                 --- child stdout (last {} lines) ---\n{}\n\
                 --- child stderr (last {} lines) ---\n{}",
                header,
                ERROR_OUTPUT_LINES,
                Self::format_output(&String::from_utf8_lossy(&stdout)),
                ERROR_OUTPUT_LINES,
                Self::format_output(&stderr_str),
            )),
        }
    }

    /// Cobb prints `Dumped failed subtyping query to <path>` on stderr for
    /// each dumped query (see `Cobb/underapproximation_type/subtyping/lean_dump.ml`).
    /// Return the path from the last such line, which corresponds to the
    /// query Cobb was working on when it was killed.
    fn latest_lean_dump_from_stderr(stderr: &str) -> Option<PathBuf> {
        stderr
            .lines()
            .rev()
            .find_map(|line| line.strip_prefix("Dumped failed subtyping query to "))
            .map(|p| PathBuf::from(p.trim()))
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

    fn debug_hint(program: &str, args: &[&str], cwd: &Path) -> String {
        format!("cd {} && {} {}", cwd.display(), program, args.join(" "))
    }

    fn run_generate(&self, program_file: &Path) -> Result<(), String> {
        let output_path = program_file.parent().unwrap().join("program_axioms.ml");
        let _ = fs::remove_file(&output_path);

        let output_str = output_path.to_string_lossy();
        let prog_str = program_file.to_string_lossy();
        let args: Vec<&str> = vec![
            "run", "--release", "--", "--export-axioms", &output_str, &prog_str,
        ];
        let cmd_debug = Self::debug_hint("cargo", &args, &self.cobb_totem_dir);

        let output = Command::new("cargo")
            .args(&args)
            .current_dir(&self.cobb_totem_dir)
            .output()
            .map_err(|e| format!("Failed to run cargo: {}", e))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            eprintln!("Axiom generation failed:\n{}", Self::format_output(&stderr));
            eprintln!("\n❌ To debug, run:\n{}", cmd_debug);
            return Err("Axiom generation failed (see output above)".to_string());
        }

        if !output_path.exists() {
            return Err("Axiom output file not created".to_string());
        }
        Ok(())
    }

    /// Run `opam exec -- dune exec -- bin/main.exe <subcommand> <meta_config> <program_file>`
    /// inside Cobb's `underapproximation_type/`. If `success_marker` is set, the
    /// subcommand exiting 0 isn't enough — its stdout or stderr must also contain
    /// that string (used to distinguish `subtype-check` true vs. false verdicts).
    fn run_cobb_subcommand(
        &self,
        subcommand: &str,
        meta_config: &Path,
        program_file: &Path,
        success_marker: Option<&str>,
    ) -> Result<(), String> {
        let underapprox_dir = self.cobb_dir.join("underapproximation_type");
        let meta_str = meta_config.to_string_lossy();
        let prog_str = program_file.to_string_lossy();
        let args: Vec<&str> = vec![
            "exec", "--", "dune", "exec", "--", "bin/main.exe",
            subcommand, &meta_str, &prog_str,
        ];
        let cmd_debug = Self::debug_hint("opam", &args, &underapprox_dir);

        let child = Command::new("opam")
            .args(&args)
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
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        if !output.status.success() {
            let formatted_out = Self::format_output(&stdout);
            if !formatted_out.trim().is_empty() {
                eprintln!("{} stdout:\n{}", subcommand, formatted_out);
            }
            eprintln!("{} failed:\n{}", subcommand, Self::format_output(&stderr));
            eprintln!("\n❌ To debug, run:\n{}", cmd_debug);
            return Err(format!("{} failed (see output above)", subcommand));
        }

        if let Some(marker) = success_marker {
            if !stdout.contains(marker) && !stderr.contains(marker) {
                eprintln!(
                    "{} exited 0 but '{}' not found in output",
                    subcommand, marker
                );
                eprintln!("stdout:\n{}", Self::format_output(&stdout));
                eprintln!("stderr:\n{}", Self::format_output(&stderr));
                eprintln!("\n❌ To debug, run:\n{}", cmd_debug);
                return Err(format!(
                    "{} missing expected '{}' output",
                    subcommand, marker
                ));
            }
        }

        Ok(())
    }

    fn run_typecheck(&self, program_file: &Path, meta_config: &Path) -> Result<(), String> {
        self.run_cobb_subcommand("type-check", meta_config, program_file, None)
    }

    fn run_subtypecheck(&self, program_file: &Path, meta_config: &Path) -> Result<(), String> {
        self.run_cobb_subcommand(
            "subtype-check",
            meta_config,
            program_file,
            Some("Result: true"),
        )
    }

    /// Run `cargo run --manifest-path totem_runner/Cargo.toml -- <subcommand> <variant>`
    /// from the repo root against the conventional
    /// `integration_tests/<test_name>/<test_name>_gen_synth_prog<n>.ml` variant.
    fn run_totem_subcommand(
        &self,
        subcommand: &str,
        test_name: &str,
        variant_num: u32,
    ) -> Result<(), String> {
        let test_dir = self
            .repo_root
            .join(format!("integration_tests/{}", test_name));
        let variant_file =
            test_dir.join(format!("{}_gen_synth_prog{}.ml", test_name, variant_num));

        if !variant_file.exists() {
            return Err(format!(
                "{} variant not found: {}",
                subcommand,
                variant_file.display()
            ));
        }

        let manifest = self.repo_root.join("totem_runner/Cargo.toml");
        let manifest_str = manifest.to_string_lossy();
        let variant_str = variant_file.to_string_lossy();
        let args: Vec<&str> = vec![
            "run", "--manifest-path", &manifest_str, "--", subcommand, &variant_str,
        ];
        let cmd_debug = Self::debug_hint("cargo", &args, &self.repo_root);

        let output = Command::new("cargo")
            .args(&args)
            .current_dir(&self.repo_root)
            .output()
            .map_err(|e| format!("Failed to run cargo: {}", e))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            eprintln!(
                "{} failed for variant {}:\n{}",
                subcommand,
                variant_num,
                Self::format_output(&stderr)
            );
            eprintln!("\n❌ To debug, run:\n{}", cmd_debug);
            return Err(format!(
                "{} failed for variant {} (see output above)",
                subcommand, variant_num
            ));
        }

        Ok(())
    }

    fn run_abduction(&self, test_name: &str, variant_num: u32) -> Result<(), String> {
        self.run_totem_subcommand("abduction", test_name, variant_num)
    }

    fn run_synthesis(&self, test_name: &str, variant_num: u32) -> Result<(), String> {
        self.run_totem_subcommand("synthesis", test_name, variant_num)
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
