mod cegar;
mod check;
mod smt;
mod trace_profile;

use std::path::PathBuf;
use std::process;

use clap::{Parser, Subcommand};

// ---------------------------------------------------------------------------
// CLI
// ---------------------------------------------------------------------------

#[derive(Parser)]
#[command(name = "smt-tools")]
#[command(about = "SMT-LIB2 analysis utilities for Totem")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Check an SMT2 file for ungated accessors and quantifier alternation
    Check {
        file: PathBuf,
    },
    /// Profile quantifier instantiations from a Z3 trace log
    TraceProfile {
        file: PathBuf,
        #[arg(short = 'n', long, default_value_t = 20)]
        top: usize,
    },
    /// CEGAR axiom selection (beam_width=1 for greedy with backtracking, >1 for beam search)
    Cegar {
        file: PathBuf,
        #[arg(short = 't', long, default_value_t = 10000)]
        timeout_ms: u32,
        #[arg(short = 'd', long, default_value_t = 20)]
        max_depth: usize,
        #[arg(short = 'b', long, default_value_t = 1)]
        beam_width: usize,
    },
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn load_smt_file(file: &PathBuf) -> smt::SmtFile {
    match smt::parse_smt_file(file.as_path()) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Error parsing {}: {e}", file.display());
            process::exit(3);
        }
    }
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    let cli = Cli::parse();
    match &cli.command {
        Commands::Check { file } => {
            let errors = check::run_check(file.as_path());
            for e in &errors {
                eprintln!("  ERROR: {e}");
            }
            if !errors.is_empty() {
                eprintln!("\n  {} error(s)", errors.len());
                process::exit(2);
            }
        }
        Commands::TraceProfile { file, top } => {
            let is_log = file.extension().is_some_and(|ext| ext == "log");
            let result = if is_log {
                trace_profile::profile_trace(file.as_path())
            } else {
                trace_profile::profile_smt_file(file.as_path())
            };
            match result {
                Ok(r) => {
                    let stats: Vec<_> = r.stats.into_iter().take(*top).collect();
                    trace_profile::print_stats(&stats);
                    trace_profile::print_triggers(&r.triggers, *top);
                }
                Err(e) => {
                    eprintln!("Error: {e}");
                    process::exit(3);
                }
            }
        }
        Commands::Cegar {
            file,
            timeout_ms,
            max_depth,
            beam_width,
        } => {
            let smt = load_smt_file(file);
            cegar::cegar_search(&smt, *timeout_ms, *max_depth, *beam_width);
        }
    }
}
