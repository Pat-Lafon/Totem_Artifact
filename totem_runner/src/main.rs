use clap::{Parser, Subcommand};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Parser)]
#[command(name = "totem_runner", about = "Connecting all of the Totem parts")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Generate axioms from program.ml using Cobb_Totem
    Generate {
        /// Program file to test (relative to repo root, e.g., integration_tests/list_length/program.ml)
        program: PathBuf,
    },
    /// Run abduction to infer missing coverage
    Abduction {
        /// Program file to test (relative to repo root, e.g., integration_tests/list_length/program.ml)
        program: PathBuf,
    },
    /// Run type-check test with axioms
    Typecheck {
        /// Program file to test (relative to repo root, e.g., integration_tests/list_length/program.ml)
        program: PathBuf,
    },
    /// Run synthesis test with axioms
    Synthesis {
        /// Program file to test (relative to repo root, e.g., integration_tests/list_length/program.ml)
        program: PathBuf,
    },
    /// Remove generated axiom file
    Clean {
        /// Program file to test (relative to repo root, e.g., integration_tests/list_length/program.ml)
        program: PathBuf,
    },
}

struct Config {
    cobb_dir: PathBuf,
    cobb_totem_dir: PathBuf,
    program_file: PathBuf,
    meta_config_path: PathBuf,
}

fn main() {
    let cli = Cli::parse();
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .to_path_buf();

    let cobb_dir = repo_root.join("Cobb");
    let cobb_totem_dir = repo_root.join("Cobb_Totem");

    assert!(
        cobb_dir.exists(),
        "Cobb submodule not found. Initialize with: git submodule update --init --recursive"
    );
    assert!(
        cobb_totem_dir.exists(),
        "Cobb_Totem submodule not found. Initialize with: git submodule update --init --recursive"
    );

    // Check dune is available
    Command::new("which")
        .arg("dune")
        .output()
        .ok()
        .filter(|o| o.status.success())
        .ok_or_else(|| panic!("dune not found. Please install OCaml and dune."))
        .unwrap();

    let program_file = match &cli.command {
        Commands::Generate { program }
        | Commands::Abduction { program }
        | Commands::Typecheck { program }
        | Commands::Synthesis { program }
        | Commands::Clean { program } => program,
    };

    let program_file = if program_file.is_absolute() {
        program_file.clone()
    } else {
        repo_root.join(program_file)
    };

    if !program_file.exists() {
        panic!("Program file not found: {}", program_file.display());
    }

    let meta_config_path = program_file.parent().unwrap().join("meta-config.json");
    if matches!(
        cli.command,
        Commands::Typecheck { .. } | Commands::Synthesis { .. }
    ) && !meta_config_path.exists()
    {
        panic!("meta-config.json not found: {}", meta_config_path.display());
    }

    let config = Config {
        cobb_dir,
        cobb_totem_dir,
        program_file,
        meta_config_path,
    };

    let result = match cli.command {
        Commands::Generate { .. } => generate_axioms(&config),
        Commands::Abduction { .. } => abduction(&config),
        Commands::Typecheck { .. } => type_check_test(&config),
        Commands::Synthesis { .. } => synthesis_test(&config),
        Commands::Clean { .. } => clean(&config),
    };

    match result {
        Ok(()) => println!("✅ Success!"),
        Err(e) => panic!("{}", e),
    }
}

fn run_cmd(cmd: &str, args: &[&str], cwd: &Path) -> Result<(), String> {
    let output = Command::new(cmd)
        .args(args)
        .current_dir(cwd)
        .output()
        .map_err(|e| format!("Failed to run {}: {}", cmd, e))?;

    if output.status.success() {
        println!("{}", String::from_utf8_lossy(&output.stdout));
        Ok(())
    } else {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        Err(format!(
            "{} failed:\nstdout:\n{}\nstderr:\n{}",
            cmd, stdout, stderr
        ))
    }
}

fn generate_axioms(config: &Config) -> Result<(), String> {
    println!("Generating axioms...");

    let output_path = config
        .program_file
        .with_extension("")
        .with_extension("axioms.ml");

    run_cmd(
        "cargo",
        &[
            "run",
            "--release",
            "--",
            "--export-axioms",
            &output_path.to_string_lossy(),
            &config.program_file.to_string_lossy(),
        ],
        &config.cobb_totem_dir,
    )?;

    assert!(
        output_path.exists(),
        "Axiom output file not created: {}",
        output_path.display()
    );

    Ok(())
}

fn abduction(config: &Config) -> Result<(), String> {
    println!("Running abduction to infer missing coverage...");

    let underapprox_dir = config.cobb_dir.join("underapproximation_type");

    run_cmd(
        "dune",
        &[
            "exec",
            "--root",
            "..",
            "--",
            "bin/main.exe",
            "abduction",
            &config.program_file.to_string_lossy(),
        ],
        &underapprox_dir,
    )
}

fn type_check_test(config: &Config) -> Result<(), String> {
    println!("Running underapproximation type checking test with axioms...");

    let underapprox_dir = config.cobb_dir.join("underapproximation_type");

    run_cmd(
        "dune",
        &[
            "exec",
            "--",
            "bin/main.exe",
            "type-check",
            &config.meta_config_path.to_string_lossy(),
            &config.program_file.to_string_lossy(),
        ],
        &underapprox_dir,
    )
}

fn synthesis_test(config: &Config) -> Result<(), String> {
    println!("Running synthesis test with axioms...");

    let underapprox_dir = config.cobb_dir.join("underapproximation_type");

    run_cmd(
        "dune",
        &[
            "exec",
            "--root",
            "..",
            "--",
            "bin/main.exe",
            "synthesis",
            &config.program_file.to_string_lossy(),
        ],
        &underapprox_dir,
    )
}

fn clean(config: &Config) -> Result<(), String> {
    let axioms_file = config
        .program_file
        .with_extension("")
        .with_extension("axioms.ml");
    if axioms_file.exists() {
        fs::remove_file(&axioms_file)
            .map_err(|e| format!("Failed to delete {}: {}", axioms_file.display(), e))?;
        println!("Cleaned: {}", axioms_file.display());
    } else {
        println!("No axioms file to clean");
    }
    Ok(())
}
