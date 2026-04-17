use std::collections::{HashMap, HashSet};
use std::time::Instant;

use rayon::prelude::*;

use crate::smt::*;
use crate::trace_profile;

// ---------------------------------------------------------------------------
// Unified CEGAR search
//
// beam_width=1: greedy mode with conflict-clause learning on timeout
// beam_width>1: beam search, timeout branches are pruned
//
// TODO: Evaluate beam_width sensitivity — currently default is 30 but we have
//       no data on how this affects solution quality vs. Z3 call budget. Run
//       experiments across benchmarks to find a good default or make it adaptive.
// TODO: Branch pruning only ranks by (sat > timeout, then fastest). Consider
//       richer heuristics: number of violated axioms, axiom coverage of UF
//       symbols, or trace-profile cost to prefer branches less likely to loop.
// TODO: Detect re-convergence — `visited` deduplicates exact axiom sets, but
//       different branches can become semantically equivalent (same solving
//       power, different axiom subsets). Could hash on Z3 model or violated-set
//       fingerprint to prune redundant branches earlier.
// ---------------------------------------------------------------------------

struct Branch {
    selected: Vec<usize>,
}

impl Branch {
    fn new() -> Self {
        Branch {
            selected: Vec::new(),
        }
    }

    fn sorted_key(&self) -> Vec<usize> {
        let mut k = self.selected.clone();
        k.sort();
        k
    }

    fn with_axiom(&self, ax: usize) -> Self {
        let mut selected = self.selected.clone();
        selected.push(ax);
        Branch { selected }
    }

    /// Check if adding `ax` to this branch would violate any conflict clause.
    fn would_conflict(&self, ax: usize, conflicts: &[Vec<usize>]) -> bool {
        conflicts.iter().any(|clause| {
            clause.iter().all(|&c| c == ax || self.selected.contains(&c))
        })
    }

    /// Check if this branch already violates a conflict clause.
    fn violates_conflict(&self, conflicts: &[Vec<usize>]) -> bool {
        conflicts.iter().any(|clause| {
            clause.iter().all(|&c| self.selected.contains(&c))
        })
    }
}

fn find_violated_axioms(
    file: &SmtFile,
    branch: &[usize],
    all_axioms: &[usize],
    model: &str,
    timeout_ms: u32,
) -> Vec<usize> {
    let model_preamble = preamble_with_model(&file.preamble, model);
    all_axioms
        .iter()
        .filter(|i| !branch.contains(i))
        .filter(|&&ax| {
            check_axiom_against_model(file, ax, &model_preamble, timeout_ms / 4) == Z3Result::Sat
        })
        .copied()
        .collect()
}

pub fn cegar_search(
    file: &SmtFile,
    timeout_ms: u32,
    max_depth: usize,
    beam_width: usize,
) {
    let z3 = Z3Runner::new();
    let n = file.assertions.len();
    let vc_idx = n - 1;
    let all_axioms: Vec<usize> = (0..vc_idx).collect();

    let mode = if beam_width <= 1 { "greedy" } else { "beam" };
    println!(
        "CEGAR axiom selection ({} axioms, max depth {}, beam width {}, mode: {})\n",
        all_axioms.len(),
        max_depth,
        beam_width,
        mode,
    );

    let mut frontier: Vec<Branch> = vec![Branch::new()];
    let mut visited: HashSet<Vec<usize>> = HashSet::new();
    visited.insert(vec![]);

    // Conflict clauses: each is a set of axiom indices that together cause timeout.
    // Any branch whose selected set is a superset of a clause will be rejected.
    let mut conflict_clauses: Vec<Vec<usize>> = Vec::new();

    for depth in 0..max_depth {
        if frontier.is_empty() {
            println!("Depth {}: no branches left.", depth);
            return;
        }

        println!("=== Depth {} ({} branch(es)) ===", depth, frontier.len());

        // --- Evaluate all branches (parallel when beam_width > 1) -----------
        let eval_branch = |branch: &Branch| {
            let mut indices = branch.selected.clone();
            indices.push(vc_idx);
            let query = build_model_query(file, &indices, timeout_ms);
            let start = Instant::now();
            let (result, output) = Z3Runner::run_z3(&query);
            (result, output, start.elapsed().as_secs_f64())
        };

        let eval_results: Vec<(Z3Result, String, f64)> = if beam_width <= 1 {
            frontier.iter().map(eval_branch).collect()
        } else {
            z3.install(|| frontier.par_iter().map(eval_branch).collect())
        };

        // --- Process results ------------------------------------------------
        let mut next_frontier: Vec<Branch> = Vec::new();

        for (branch, (result, output, elapsed)) in
            frontier.iter_mut().zip(eval_results.into_iter())
        {
            println!(
                "  [{}] => {} ({:.1}s)",
                format_names(file, &branch.selected),
                result,
                elapsed,
            );

            match result {
                Z3Result::Unsat => {
                    println!(
                        "\n  SOLVED with {} axioms! [{}]",
                        branch.selected.len(),
                        format_names(file, &branch.selected),
                    );
                    return;
                }
                Z3Result::Unknown if beam_width <= 1 => {
                    // Trace-profile to find hot axioms + trigger cycles
                    let mut indices = branch.selected.clone();
                    indices.push(vc_idx);
                    let diag_query = build_query_with_timeout(file, &indices, timeout_ms);
                    let profile = trace_profile::diagnose_query(&diag_query, 3_000_000, 10)
                        .unwrap_or_else(|_| trace_profile::ProfileResult {
                            stats: vec![],
                            triggers: vec![],
                        });

                    // Build QID -> axiom index lookup for selected axioms
                    let qid_to_idx: HashMap<&str, usize> = branch
                        .selected
                        .iter()
                        .map(|&idx| (assertion_name(file, idx), idx))
                        .collect();

                    if !profile.stats.is_empty() {
                        println!("  Timeout — hot axioms:");
                        for s in &profile.stats {
                            let in_selected = qid_to_idx.contains_key(s.qid.as_str());
                            println!(
                                "    {} ({} instantiations){}",
                                s.qid,
                                s.count,
                                if in_selected { " [SELECTED]" } else { "" }
                            );
                        }
                    }

                    // Try to learn a conflict clause from trigger cycles
                    let cycles = find_trigger_cycles(&profile.triggers, &qid_to_idx);
                    let mut learned_clause = false;

                    for cycle in &cycles {
                        let names: Vec<&str> = cycle
                            .axioms
                            .iter()
                            .map(|&i| assertion_name(file, i))
                            .collect();
                        println!(
                            "  Trigger cycle ({} axioms, weight {}): [{}]",
                            cycle.axioms.len(),
                            cycle.total_weight,
                            names.join(", "),
                        );
                        for (from, to, count) in &cycle.edges {
                            println!(
                                "    {} -> {} ({})",
                                assertion_name(file, *from),
                                assertion_name(file, *to),
                                count,
                            );
                        }

                        // Validate: does just this cycle + VC still timeout?
                        let mut cycle_indices = cycle.axioms.clone();
                        cycle_indices.push(vc_idx);
                        let start = Instant::now();
                        let cycle_result = z3.eval(
                            &build_query_with_timeout(file, &cycle_indices, timeout_ms),
                        );
                        let cycle_elapsed = start.elapsed().as_secs_f64();

                        if cycle_result == Z3Result::Unknown {
                            // Minimize the conflict clause
                            let minimal = minimize_conflict(
                                file, &z3, &cycle.axioms, vc_idx, timeout_ms,
                            );
                            let minimal_names: Vec<&str> = minimal
                                .iter()
                                .map(|&i| assertion_name(file, i))
                                .collect();
                            println!(
                                "    CONFIRMED ({:.1}s) — minimal conflict: [{}]",
                                cycle_elapsed,
                                minimal_names.join(", "),
                            );
                            conflict_clauses.push(minimal);
                            learned_clause = true;
                            break;
                        } else {
                            println!(
                                "    not confirmed: {} ({:.1}s)",
                                cycle_result, cycle_elapsed,
                            );
                        }
                    }

                    if !learned_clause {
                        // No cycle confirmed — fall back: learn the full selected set
                        // as a conflict clause (conservative but correct)
                        println!(
                            "  No cycle confirmed. Learning full selected set as conflict: [{}]",
                            format_names(file, &branch.selected),
                        );
                        conflict_clauses.push(branch.selected.clone());
                    }

                    // Backtrack: remove axioms involved in the newest conflict
                    // and re-add the branch without them
                    let clause = conflict_clauses.last().unwrap();
                    let mut new_selected: Vec<usize> = branch
                        .selected
                        .iter()
                        .filter(|ax| !clause.contains(ax))
                        .copied()
                        .collect();

                    // If removing all clause axioms leaves us empty or unchanged,
                    // try removing just one (the hottest)
                    if new_selected.len() == branch.selected.len() || new_selected.is_empty() {
                        let hottest = profile.stats.iter().find_map(|s| {
                            qid_to_idx.get(s.qid.as_str()).copied()
                        });
                        if let Some(hot) = hottest {
                            new_selected = branch
                                .selected
                                .iter()
                                .filter(|&&x| x != hot)
                                .copied()
                                .collect();
                        }
                    }

                    println!(
                        "  Backtracking to: [{}]",
                        format_names(file, &new_selected),
                    );
                    println!(
                        "  Conflict clauses: {}",
                        conflict_clauses.len(),
                    );

                    let new_branch = Branch { selected: new_selected };
                    if !new_branch.violates_conflict(&conflict_clauses) {
                        next_frontier.push(new_branch);
                    } else {
                        println!("  Backtracked state also violates a conflict — pruned.");
                    }
                }
                Z3Result::Unknown => {
                    // Beam mode: just prune timeout branches
                    println!("    pruned (timeout)");
                }
                Z3Result::Sat => {
                    let model = match extract_model(&output) {
                        Some(m) => m,
                        None => {
                            println!("  No model extracted.");
                            if let Some(&ax) = all_axioms.iter().find(|&&i| {
                                !branch.selected.contains(&i)
                                    && !branch.would_conflict(i, &conflict_clauses)
                            }) {
                                println!("    + {}", assertion_name(file, ax));
                                next_frontier.push(branch.with_axiom(ax));
                            }
                            continue;
                        }
                    };

                    let violated: Vec<usize> = find_violated_axioms(
                        file,
                        &branch.selected,
                        &all_axioms,
                        &model,
                        timeout_ms,
                    )
                    .into_iter()
                    .filter(|&ax| !branch.would_conflict(ax, &conflict_clauses))
                    .collect();

                    if violated.is_empty() {
                        println!("  No axioms violated by model (after conflict filtering).");
                        if let Some(&ax) = all_axioms.iter().find(|&&i| {
                            !branch.selected.contains(&i)
                                && !branch.would_conflict(i, &conflict_clauses)
                        }) {
                            println!("    + {}", assertion_name(file, ax));
                            next_frontier.push(branch.with_axiom(ax));
                        }
                        continue;
                    }

                    println!(
                        "  {} violated: [{}]",
                        violated.len(),
                        format_names(file, &violated),
                    );

                    if beam_width <= 1 {
                        let chosen = greedy_rank_violated(
                            file,
                            &z3,
                            &branch.selected,
                            &violated,
                            vc_idx,
                            timeout_ms,
                            &conflict_clauses,
                        );
                        if let Some(ax) = chosen {
                            next_frontier.push(branch.with_axiom(ax));
                        }
                    } else {
                        for &ax_idx in &violated {
                            let new_branch = branch.with_axiom(ax_idx);
                            let key = new_branch.sorted_key();
                            if !visited.contains(&key)
                                && !new_branch.violates_conflict(&conflict_clauses)
                            {
                                visited.insert(key);
                                next_frontier.push(new_branch);
                            }
                        }
                    }
                }
                Z3Result::Error(e) => {
                    println!("  Error: {e}");
                    return;
                }
            }
        }

        // --- Prune to beam width --------------------------------------------
        if beam_width > 1 && next_frontier.len() > beam_width {
            println!(
                "\n  {} candidates, pruning to beam width {}...",
                next_frontier.len(),
                beam_width
            );

            let scored: Vec<(Z3Result, f64)> = z3.install(|| {
                next_frontier
                    .par_iter()
                    .map(|branch| {
                        let mut indices = branch.selected.clone();
                        indices.push(vc_idx);
                        let query = build_query_with_timeout(file, &indices, timeout_ms);
                        let start = Instant::now();
                        let result = Z3Runner::run_z3(&query).0;
                        (result, start.elapsed().as_secs_f64())
                    })
                    .collect()
            });

            for (i, (result, elapsed)) in scored.iter().enumerate() {
                if *result == Z3Result::Unsat {
                    println!(
                        "\n  SOLVED! [{}] ({:.1}s)",
                        format_names(file, &next_frontier[i].selected),
                        elapsed,
                    );
                    return;
                }
            }

            let mut indexed: Vec<(usize, &Z3Result, f64)> = scored
                .iter()
                .enumerate()
                .map(|(i, (r, e))| (i, r, *e))
                .collect();
            indexed.sort_by(|a, b| {
                let a_sat = *a.1 == Z3Result::Sat;
                let b_sat = *b.1 == Z3Result::Sat;
                b_sat.cmp(&a_sat).then(a.2.partial_cmp(&b.2).unwrap())
            });

            let keep: HashSet<usize> = indexed.iter().take(beam_width).map(|x| x.0).collect();
            let mut pruned = Vec::new();
            for (i, branch) in next_frontier.into_iter().enumerate() {
                if keep.contains(&i) {
                    pruned.push(branch);
                }
            }
            next_frontier = pruned;
        }

        frontier = next_frontier;
    }

    println!("\nReached max depth ({}).", max_depth);
    if !frontier.is_empty() {
        println!("  {} branch(es) remaining:", frontier.len());
        for branch in &frontier {
            println!("    [{}]", format_names(file, &branch.selected));
        }
    }
    if !conflict_clauses.is_empty() {
        println!("\n  Learned {} conflict clause(s):", conflict_clauses.len());
        for clause in &conflict_clauses {
            println!("    [{}]", format_names(file, clause));
        }
    }
}

/// Greedy ranking: try each violated axiom, prefer ones that keep the query sat
/// (avoids matching loops). Returns the best axiom to add, or None.
fn greedy_rank_violated(
    file: &SmtFile,
    z3: &Z3Runner,
    selected: &[usize],
    violated: &[usize],
    vc_idx: usize,
    timeout_ms: u32,
    conflict_clauses: &[Vec<usize>],
) -> Option<usize> {
    println!("  Ranking by solver behavior...");
    let mut sat_candidates = Vec::new();
    let mut unknown_candidates = Vec::new();

    // Build a temp branch to check conflicts
    let branch = Branch { selected: selected.to_vec() };

    for &ax_idx in violated {
        if branch.would_conflict(ax_idx, conflict_clauses) {
            println!(
                "    {} — skipped (conflict clause)",
                assertion_name(file, ax_idx),
            );
            continue;
        }
        let mut try_indices = selected.to_vec();
        try_indices.push(ax_idx);
        try_indices.push(vc_idx);
        let start = Instant::now();
        let try_result = z3.eval(&build_query_with_timeout(file, &try_indices, timeout_ms));
        println!(
            "    {} => {} ({:.1}s)",
            assertion_name(file, ax_idx),
            try_result,
            start.elapsed().as_secs_f64()
        );
        match try_result {
            Z3Result::Unsat => {
                println!("    => ADDING {} (solves it!)", assertion_name(file, ax_idx));
                return Some(ax_idx);
            }
            Z3Result::Sat => sat_candidates.push(ax_idx),
            _ => unknown_candidates.push(ax_idx),
        }
    }

    if let Some(&ax) = sat_candidates.first() {
        println!("  Adding {} (stays sat)", assertion_name(file, ax));
        Some(ax)
    } else if let Some(&ax) = unknown_candidates.first() {
        println!("  Adding {} (causes timeout)", assertion_name(file, ax));
        Some(ax)
    } else {
        None
    }
}

/// Minimize a confirmed conflict: try removing each axiom to find the smallest
/// subset that still times out.
fn minimize_conflict(
    file: &SmtFile,
    z3: &Z3Runner,
    axioms: &[usize],
    vc_idx: usize,
    timeout_ms: u32,
) -> Vec<usize> {
    let mut minimal = axioms.to_vec();

    // Try removing each axiom one at a time
    let mut i = 0;
    while i < minimal.len() {
        if minimal.len() <= 2 {
            break; // 2 is the smallest useful conflict
        }
        let removed = minimal.remove(i);
        let mut test_indices = minimal.clone();
        test_indices.push(vc_idx);
        let result = z3.eval(&build_query_with_timeout(file, &test_indices, timeout_ms));
        if result == Z3Result::Unknown {
            // Still times out without this axiom — it wasn't needed
            println!(
                "      {} not needed in conflict",
                assertion_name(file, removed),
            );
            // don't increment i — next element shifted into this position
        } else {
            // Need this axiom — put it back
            minimal.insert(i, removed);
            i += 1;
        }
    }

    minimal
}

/// A strongly connected component of axioms with total trigger weight.
struct TriggerCycle {
    /// Axiom indices in this SCC.
    axioms: Vec<usize>,
    /// Total trigger count across all edges within this SCC.
    total_weight: u64,
    /// Individual edges within this SCC: (from, to, count).
    edges: Vec<(usize, usize, u64)>,
}

/// Find trigger cycles among selected axioms using Tarjan's SCC algorithm.
/// Returns SCCs of size >= 2, sorted by total weight (heaviest first).
fn find_trigger_cycles(
    triggers: &[trace_profile::TriggerEdge],
    qid_to_idx: &HashMap<&str, usize>,
) -> Vec<TriggerCycle> {
    // Build adjacency list restricted to selected axioms
    let mut adj: HashMap<usize, Vec<(usize, u64)>> = HashMap::new();
    let mut edge_weights: HashMap<(usize, usize), u64> = HashMap::new();
    let mut nodes: HashSet<usize> = HashSet::new();

    for e in triggers {
        if let (Some(&from), Some(&to)) = (
            qid_to_idx.get(e.from_qid.as_str()),
            qid_to_idx.get(e.to_qid.as_str()),
        ) {
            if from != to {
                *edge_weights.entry((from, to)).or_insert(0) += e.count;
                nodes.insert(from);
                nodes.insert(to);
            }
        }
    }

    for (&(from, to), &count) in &edge_weights {
        adj.entry(from).or_default().push((to, count));
    }

    // Tarjan's SCC
    let sccs = tarjan_scc(&nodes, &adj);

    // Filter to SCCs with 2+ nodes and compute weights
    let mut cycles: Vec<TriggerCycle> = sccs
        .into_iter()
        .filter(|scc| scc.len() >= 2)
        .map(|scc| {
            let scc_set: HashSet<usize> = scc.iter().copied().collect();
            let mut total_weight = 0u64;
            let mut edges = Vec::new();
            for &a in &scc {
                for &(b, count) in adj.get(&a).unwrap_or(&vec![]) {
                    if scc_set.contains(&b) {
                        total_weight += count;
                        edges.push((a, b, count));
                    }
                }
            }
            edges.sort_by(|a, b| b.2.cmp(&a.2));
            TriggerCycle {
                axioms: scc,
                total_weight,
                edges,
            }
        })
        .collect();

    cycles.sort_by(|a, b| b.total_weight.cmp(&a.total_weight));
    cycles
}

fn tarjan_scc(
    nodes: &HashSet<usize>,
    adj: &HashMap<usize, Vec<(usize, u64)>>,
) -> Vec<Vec<usize>> {
    struct State {
        index_counter: usize,
        stack: Vec<usize>,
        on_stack: HashSet<usize>,
        index: HashMap<usize, usize>,
        lowlink: HashMap<usize, usize>,
        result: Vec<Vec<usize>>,
    }

    fn strongconnect(
        v: usize,
        adj: &HashMap<usize, Vec<(usize, u64)>>,
        state: &mut State,
    ) {
        state.index.insert(v, state.index_counter);
        state.lowlink.insert(v, state.index_counter);
        state.index_counter += 1;
        state.stack.push(v);
        state.on_stack.insert(v);

        for &(w, _) in adj.get(&v).unwrap_or(&vec![]) {
            if !state.index.contains_key(&w) {
                strongconnect(w, adj, state);
                let wl = state.lowlink[&w];
                let vl = state.lowlink.get_mut(&v).unwrap();
                if wl < *vl {
                    *vl = wl;
                }
            } else if state.on_stack.contains(&w) {
                let wi = state.index[&w];
                let vl = state.lowlink.get_mut(&v).unwrap();
                if wi < *vl {
                    *vl = wi;
                }
            }
        }

        if state.lowlink[&v] == state.index[&v] {
            let mut scc = Vec::new();
            loop {
                let w = state.stack.pop().unwrap();
                state.on_stack.remove(&w);
                scc.push(w);
                if w == v {
                    break;
                }
            }
            state.result.push(scc);
        }
    }

    let mut state = State {
        index_counter: 0,
        stack: Vec::new(),
        on_stack: HashSet::new(),
        index: HashMap::new(),
        lowlink: HashMap::new(),
        result: Vec::new(),
    };

    for &v in nodes {
        if !state.index.contains_key(&v) {
            strongconnect(v, adj, &mut state);
        }
    }

    state.result
}
