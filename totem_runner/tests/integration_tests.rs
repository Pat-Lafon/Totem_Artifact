use serial_test::serial;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::thread;
use std::time::{Duration, Instant};

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
        mut child: std::process::Child,
        timeout_secs: u64,
        cmd_debug: &str,
    ) -> Result<std::process::Output, String> {
        use std::io::Read;

        let timeout = Duration::from_secs(timeout_secs);
        let start = Instant::now();

        while start.elapsed() < timeout {
            match child.try_wait() {
                Ok(Some(status)) => {
                    let mut stdout = Vec::new();
                    let mut stderr = Vec::new();

                    if let Some(mut out) = child.stdout.take() {
                        let _ = out.read_to_end(&mut stdout);
                    }
                    if let Some(mut err) = child.stderr.take() {
                        let _ = err.read_to_end(&mut stderr);
                    }

                    return Ok(std::process::Output {
                        status,
                        stdout,
                        stderr,
                    });
                }
                Ok(None) => {
                    thread::sleep(Duration::from_millis(100));
                }
                Err(e) => return Err(format!("Failed to wait for child: {}", e)),
            }
        }

        let _ = child.kill();
        Err(format!(
            "Command timeout after {} seconds\nCommand: {}",
            timeout_secs, cmd_debug
        ))
    }

    fn format_output(output: &str) -> String {
        let max_lines = ERROR_OUTPUT_LINES;
        let lines: Vec<&str> = output.lines().collect();
        if lines.len() <= max_lines * 2 {
            return output.to_string();
        }

        let mut result = String::new();
        let first_lines = lines.iter().take(max_lines).map(|s| *s).collect::<Vec<_>>();
        let last_lines = lines
            .iter()
            .skip(lines.len() - max_lines)
            .map(|s| *s)
            .collect::<Vec<_>>();

        result.push_str(&first_lines.join("\n"));
        result.push_str(&format!(
            "\n... ({} lines omitted) ...\n",
            lines.len() - max_lines * 2
        ));
        result.push_str(&last_lines.join("\n"));
        result
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
        let underapprox_dir = self.cobb_dir.join("underapproximation_type");

        let output = Command::new("opam")
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
            .output()
            .map_err(|e| format!("Failed to run dune via opam: {} (cwd: {}, config: {}, program: {})", e, underapprox_dir.display(), meta_config.display(), program_file.display()))?;

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
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| format!("Failed to run dune via opam: {} (cwd: {}, config: {}, program: {})", e, underapprox_dir.display(), meta_config.display(), program_file.display()))?;

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
    let program_file = test_dir.join("program.ml");
    let typecheck_file = test_dir.join("even_list_gen.ml");
    let meta_config = test_dir.join("meta-config.json");

    // env.run_generate(&program_file)?;

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
    let program_file = test_dir.join("program.ml");
    let typecheck_file = test_dir.join("depth_tree_gen.ml");
    let meta_config = test_dir.join("meta-config.json");

    // env.run_generate(&program_file)?;

    // Subtyping tests
    let subtyping_dir = test_dir.join("subtyping_tests");
    env.run_subtypecheck(&subtyping_dir.join("leaf.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("leaf_rev.ml"), &meta_config)?;
    env.run_subtypecheck(&subtyping_dir.join("depth_type_check.ml"), &meta_config)?;

    env.run_typecheck(&typecheck_file, &meta_config)?;

    env.run_abduction("depth_tree", 1)?;
    env.run_synthesis("depth_tree", 1)?;
    // env.run_synthesis("depth_tree", 2)?;
    // env.run_synthesis("depth_tree", 3)?;
    // env.run_synthesis("depth_tree", 4)?;

    Ok(())
}
