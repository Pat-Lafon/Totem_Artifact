use smtlib_lowlevel::ast;
use smtlib_lowlevel::lexicon::Symbol as Sym;
use smtlib_lowlevel::Storage;
use std::collections::{HashMap, HashSet};
use std::path::Path;

use ast::{Command, DatatypeDec, Identifier, Index, QualIdentifier, Script, SortedVar, Term};

// ---------------------------------------------------------------------------
// Datatype info extraction
// ---------------------------------------------------------------------------

struct DtInfo {
    selector_to_ctor: HashMap<String, String>,
    ctor_to_recognizer: HashMap<String, String>,
    datatype_sorts: HashSet<String>,
}

impl DtInfo {
    fn from_commands(commands: &[Command]) -> Self {
        let mut dt = DtInfo {
            selector_to_ctor: HashMap::new(),
            ctor_to_recognizer: HashMap::new(),
            datatype_sorts: HashSet::new(),
        };
        for cmd in commands {
            let Command::DeclareDatatypes(sort_decs, dt_decs) = cmd else {
                continue;
            };
            for (sort_dec, dt_dec) in sort_decs.iter().zip(dt_decs.iter()) {
                dt.datatype_sorts.insert(sort_dec.0 .0.to_string());
                let ctors = match dt_dec {
                    DatatypeDec::DatatypeDec(cs) | DatatypeDec::Par(_, cs) => cs,
                };
                for ctor in *ctors {
                    let name = ctor.0 .0.to_string();
                    dt.ctor_to_recognizer
                        .insert(name.clone(), format!("is_{name}"));
                    for sel in ctor.1 {
                        dt.selector_to_ctor
                            .insert(sel.0 .0.to_string(), name.clone());
                    }
                }
            }
        }
        dt
    }
}

// ---------------------------------------------------------------------------
// AST helpers
// ---------------------------------------------------------------------------

fn qual_id_name<'a>(qid: &'a QualIdentifier<'a>) -> Option<&'a str> {
    match qid {
        QualIdentifier::Identifier(Identifier::Simple(Sym(s)))
        | QualIdentifier::Sorted(Identifier::Simple(Sym(s)), _) => Some(s),
        _ => None,
    }
}

fn recognizer_ctor<'a>(qid: &'a QualIdentifier<'a>) -> Option<&'a str> {
    let id = match qid {
        QualIdentifier::Identifier(id) | QualIdentifier::Sorted(id, _) => id,
    };
    if let Identifier::Indexed(Sym("is"), [Index::Symbol(Sym(ctor))]) = id {
        Some(ctor)
    } else {
        None
    }
}

fn var_name<'a>(term: &'a Term<'a>) -> Option<&'a str> {
    if let Term::Identifier(qid) = term {
        qual_id_name(qid)
    } else {
        None
    }
}

fn unwrap<'a>(term: &'a Term<'a>) -> &'a Term<'a> {
    match term {
        Term::Annotation(inner, _) => unwrap(inner),
        _ => term,
    }
}

fn app_args<'a>(term: &'a Term<'a>, name: &str) -> Option<&'a [&'a Term<'a>]> {
    if let Term::Application(qid, args) = unwrap(term) {
        if qual_id_name(qid) == Some(name) {
            return Some(args);
        }
    }
    None
}

fn for_each_child<'a>(term: &'a Term<'a>, f: &mut impl FnMut(&'a Term<'a>)) {
    match unwrap(term) {
        Term::SpecConstant(_) | Term::Identifier(_) => {}
        Term::Application(_, args) => args.iter().for_each(|a| f(a)),
        Term::Let(bindings, body) => {
            bindings.iter().for_each(|b| f(b.1));
            f(body);
        }
        Term::Forall(_, body) | Term::Exists(_, body) => f(body),
        Term::Match(t, cases) => {
            f(t);
            cases.iter().for_each(|c| f(c.1));
        }
        Term::Annotation(inner, _) => f(inner),
    }
}

fn term_constructor<'a>(term: &'a Term<'a>, dt: &DtInfo) -> Option<&'a str> {
    match unwrap(term) {
        Term::Identifier(qid) | Term::Application(qid, _) => {
            let name = qual_id_name(qid)?;
            dt.ctor_to_recognizer.contains_key(name).then_some(name)
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Ungated accessor checks
// ---------------------------------------------------------------------------

type Guards = HashSet<(String, String)>;

fn extract_guards(term: &Term) -> Guards {
    let mut gs = Guards::new();
    match unwrap(term) {
        Term::Application(qid, [arg]) if recognizer_ctor(qid).is_some() => {
            if let Some(v) = var_name(arg) {
                gs.insert((recognizer_ctor(qid).unwrap().to_string(), v.to_string()));
            }
        }
        _ if app_args(term, "and").is_some() => {
            for a in app_args(term, "and").unwrap() {
                gs.extend(extract_guards(a));
            }
        }
        _ => {}
    }
    gs
}

fn check_accessors(term: &Term, guards: &Guards, dt: &DtInfo, errors: &mut Vec<String>) {
    let term = unwrap(term);

    if let Term::Application(qid, [arg]) = term {
        if let Some(sel) = qual_id_name(qid) {
            if let Some(ctor) = dt.selector_to_ctor.get(sel) {
                if let Some(arg_ctor) = term_constructor(arg, dt) {
                    if arg_ctor != ctor {
                        errors.push(format!(
                            "Selector '{sel}' applied to '{arg_ctor}' — belongs to '{ctor}'"
                        ));
                    }
                } else if let Some(v) = var_name(arg) {
                    if !guards.contains(&(ctor.clone(), v.to_string())) {
                        let rec = &dt.ctor_to_recognizer[ctor];
                        errors.push(format!(
                            "Ungated selector '{sel}' on '{v}' — needs ({rec} {v})"
                        ));
                    }
                }
            }
        }
    }

    if let Some(children) = app_args(term, "and") {
        let mut ext = guards.clone();
        for c in children {
            ext.extend(extract_guards(c));
        }
        for c in children {
            check_accessors(c, &ext, dt, errors);
        }
        return;
    }
    if let Some([ante, body]) = app_args(term, "=>") {
        check_accessors(ante, guards, dt, errors);
        let mut ext = guards.clone();
        ext.extend(extract_guards(ante));
        check_accessors(body, &ext, dt, errors);
        return;
    }
    if let Some([cond, then_br, else_br]) = app_args(term, "ite") {
        check_accessors(cond, guards, dt, errors);
        let mut ext = guards.clone();
        ext.extend(extract_guards(cond));
        check_accessors(then_br, &ext, dt, errors);
        check_accessors(else_br, guards, dt, errors);
        return;
    }

    for_each_child(term, &mut |c| check_accessors(c, guards, dt, errors));
}

// ---------------------------------------------------------------------------
// Quantifier alternation checks
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq)]
enum Q {
    A,
    E,
}

impl std::fmt::Display for Q {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", if *self == Q::A { "A" } else { "E" })
    }
}

#[derive(Clone)]
struct QStep {
    eff: Q,
    has_dt: bool,
    desc: Vec<String>,
}

fn collect_qpaths(
    term: &Term,
    positive: bool,
    path: &mut Vec<QStep>,
    dt: &DtInfo,
    out: &mut Vec<Vec<QStep>>,
) {
    let term = unwrap(term);
    match term {
        Term::Forall(vars, body) | Term::Exists(vars, body) => {
            let is_forall = matches!(term, Term::Forall(..));
            path.push(QStep {
                eff: if is_forall == positive { Q::A } else { Q::E },
                has_dt: vars
                    .iter()
                    .any(|SortedVar(_, s)| dt.datatype_sorts.contains(&format!("{s}"))),
                desc: vars
                    .iter()
                    .map(|SortedVar(Sym(n), s)| format!("{n}:{s}"))
                    .collect(),
            });
            collect_qpaths(body, true, path, dt, out);
            path.pop();
        }
        Term::SpecConstant(_) | Term::Identifier(_) => {
            if !path.is_empty() {
                out.push(path.clone());
            }
        }
        _ => {
            if let Some([inner]) = app_args(term, "not") {
                collect_qpaths(inner, !positive, path, dt, out);
                return;
            }
            if let Some([ante, body]) = app_args(term, "=>") {
                collect_qpaths(ante, !positive, path, dt, out);
                collect_qpaths(body, positive, path, dt, out);
                return;
            }
            for_each_child(term, &mut |c| collect_qpaths(c, positive, path, dt, out));
        }
    }
}

fn check_quantifiers(assertions: &[&Term], dt: &DtInfo, errors: &mut Vec<String>) {
    let mut all_paths = Vec::new();
    for term in assertions {
        collect_qpaths(term, true, &mut Vec::new(), dt, &mut all_paths);
    }

    let worst = all_paths
        .iter()
        .map(|p| {
            let (alt, has_dt) = {
                let mut alt = 0;
                let mut has_dt = false;
                for w in p.windows(2) {
                    if w[0].eff != w[1].eff {
                        alt += 1;
                        if w[0].has_dt || w[1].has_dt {
                            has_dt = true;
                        }
                    }
                }
                (alt, has_dt)
            };
            (alt, has_dt, p)
        })
        .max_by_key(|&(alt, has_dt, _)| (alt, has_dt));

    if let Some((alt, true, path)) = worst {
        if alt >= 1 {
            let pattern: String = {
                let mut s = String::new();
                for (i, step) in path.iter().enumerate() {
                    if i == 0 || step.eff != path[i - 1].eff {
                        s.push_str(&format!("{}", step.eff));
                    }
                }
                s
            };
            let detail: String = path
                .iter()
                .map(|s| format!("{}({})", s.eff, s.desc.join(", ")))
                .collect::<Vec<_>>()
                .join(" -> ");
            errors.push(format!(
                "Quantifier alternation depth {alt} ({pattern}) with datatype-sorted vars\n    Path: {detail}",
            ));
        }
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub fn run_check(file: &Path) -> Vec<String> {
    let input = std::fs::read_to_string(file).unwrap_or_else(|e| {
        panic!("Error reading {}: {e}", file.display());
    });
    check_str(&input)
}

pub fn check_str(input: &str) -> Vec<String> {
    let storage = Storage::new();
    let script = Script::parse(&storage, input).unwrap_or_else(|e| {
        panic!("Parse error: {e}");
    });
    let dt = DtInfo::from_commands(script.0);
    let mut errors = Vec::new();
    let assertions: Vec<&Term> = script
        .0
        .iter()
        .filter_map(|cmd| {
            if let Command::Assert(term) = cmd {
                Some(*term)
            } else {
                None
            }
        })
        .collect();
    for term in &assertions {
        check_accessors(term, &Guards::new(), &dt, &mut errors);
    }
    check_quantifiers(&assertions, &dt, &mut errors);
    errors
}

#[cfg(test)]
mod tests {
    use super::*;

    const LIST_PREAMBLE: &str = "\
(declare-datatypes ((ilist 0)) (((Nil) (Cons (head Int) (tail ilist)))))
(declare-fun len (ilist) Int)
";

    const TREE_PREAMBLE: &str = "\
(declare-datatypes ((itree 0)) (((Leaf) (Node (value Int) (left itree) (right itree)))))
(declare-fun size (itree) Int)
";

    // -----------------------------------------------------------------------
    // Ungated accessor checks
    // -----------------------------------------------------------------------

    #[test]
    fn guarded_selector_no_error() {
        let smt = format!(
            "{LIST_PREAMBLE}\
            (assert (forall ((l ilist)) (=> ((_ is Cons) l) (> (head l) 0))))\n\
            (check-sat)\n"
        );
        let errors = check_str(&smt);
        assert!(errors.is_empty(), "expected no errors, got: {errors:?}");
    }

    #[test]
    fn ungated_selector_error() {
        let smt = format!(
            "{LIST_PREAMBLE}\
            (assert (forall ((l ilist)) (> (head l) 0)))\n\
            (check-sat)\n"
        );
        let errors = check_str(&smt);
        assert_eq!(errors.len(), 1);
        assert!(errors[0].contains("Ungated selector 'head'"));
    }

    #[test]
    fn ungated_nested_selector_not_tracked() {
        // head applied to (tail l) — (tail l) is not a variable, so the checker
        // can't track its constructor. This is a known limitation: the checker
        // only flags ungated selectors on *variables*, not on compound expressions.
        let smt = format!(
            "{LIST_PREAMBLE}\
            (assert (forall ((l ilist)) (=> ((_ is Cons) l) (> (head (tail l)) 0))))\n\
            (check-sat)\n"
        );
        let errors = check_str(&smt);
        assert!(errors.is_empty(), "checker doesn't track compound expressions: {errors:?}");
    }

    #[test]
    fn guarded_nested_selectors_no_error() {
        let smt = format!(
            "{LIST_PREAMBLE}\
            (assert (forall ((l ilist))\n\
              (=> ((_ is Cons) l)\n\
                (=> ((_ is Cons) (tail l))\n\
                  (> (head (tail l)) 0)))))\n\
            (check-sat)\n"
        );
        let errors = check_str(&smt);
        assert!(errors.is_empty(), "expected no errors, got: {errors:?}");
    }

    #[test]
    fn wrong_constructor_selector_error() {
        let smt = format!(
            "{LIST_PREAMBLE}\
            (assert (forall ((l ilist)) (=> ((_ is Nil) l) (> (head l) 0))))\n\
            (check-sat)\n"
        );
        let errors = check_str(&smt);
        assert_eq!(errors.len(), 1, "got: {errors:?}");
        assert!(errors[0].contains("Ungated selector 'head'"));
    }

    #[test]
    fn selector_on_constructor_no_error() {
        let smt = format!(
            "{LIST_PREAMBLE}\
            (assert (= (head (Cons 1 Nil)) 1))\n\
            (check-sat)\n"
        );
        let errors = check_str(&smt);
        assert!(errors.is_empty(), "expected no errors, got: {errors:?}");
    }

    #[test]
    fn guard_in_conjunction() {
        let smt = format!(
            "{LIST_PREAMBLE}\
            (assert (forall ((l ilist))\n\
              (and ((_ is Cons) l) (> (head l) 0))))\n\
            (check-sat)\n"
        );
        let errors = check_str(&smt);
        assert!(errors.is_empty(), "expected no errors, got: {errors:?}");
    }

    #[test]
    fn guard_in_ite_condition() {
        let smt = format!(
            "{LIST_PREAMBLE}\
            (assert (forall ((l ilist))\n\
              (ite ((_ is Cons) l) (> (head l) 0) true)))\n\
            (check-sat)\n"
        );
        let errors = check_str(&smt);
        assert!(errors.is_empty(), "expected no errors, got: {errors:?}");
    }

    #[test]
    fn tree_guarded_no_error() {
        let smt = format!(
            "{TREE_PREAMBLE}\
            (assert (forall ((t itree))\n\
              (=> ((_ is Node) t)\n\
                (>= (size t) (+ (size (left t)) (size (right t)))))))\n\
            (check-sat)\n"
        );
        let errors = check_str(&smt);
        assert!(errors.is_empty(), "expected no errors, got: {errors:?}");
    }

    #[test]
    fn tree_ungated_left_right() {
        let smt = format!(
            "{TREE_PREAMBLE}\
            (assert (forall ((t itree))\n\
              (>= (size t) (+ (size (left t)) (size (right t))))))\n\
            (check-sat)\n"
        );
        let errors = check_str(&smt);
        assert!(errors.len() >= 2, "expected >= 2 errors, got: {errors:?}");
    }

    #[test]
    fn multiple_ungated_selectors() {
        let smt = format!(
            "{LIST_PREAMBLE}\
            (assert (forall ((l ilist)) (> (head l) 0)))\n\
            (assert (forall ((l ilist)) (= (tail l) Nil)))\n\
            (check-sat)\n"
        );
        let errors = check_str(&smt);
        assert_eq!(errors.len(), 2, "got: {errors:?}");
    }

    // -----------------------------------------------------------------------
    // Quantifier alternation checks
    // -----------------------------------------------------------------------

    #[test]
    fn no_alternation_no_error() {
        let smt = format!(
            "{LIST_PREAMBLE}\
            (assert (forall ((l ilist)) (>= (len l) 0)))\n\
            (check-sat)\n"
        );
        let errors = check_str(&smt);
        assert!(errors.is_empty(), "expected no errors, got: {errors:?}");
    }

    #[test]
    fn forall_exists_alternation_with_datatype() {
        let smt = format!(
            "{LIST_PREAMBLE}\
            (assert (forall ((l ilist)) (exists ((m ilist)) (= (len m) (len l)))))\n\
            (check-sat)\n"
        );
        let errors = check_str(&smt);
        assert_eq!(errors.len(), 1, "got: {errors:?}");
        assert!(errors[0].contains("Quantifier alternation"));
    }

    #[test]
    fn alternation_with_int_only_no_error() {
        // Alternation over Int-sorted vars only — no datatype concern
        let smt = "\
            (assert (forall ((x Int)) (exists ((y Int)) (= y (+ x 1)))))\n\
            (check-sat)\n";
        let errors = check_str(smt);
        assert!(errors.is_empty(), "expected no errors for Int-only alternation, got: {errors:?}");
    }

    #[test]
    fn negated_exists_is_forall() {
        // (not (exists ...)) = (forall ...) — so not(exists(forall)) = forall(forall) = no alternation
        let smt = format!(
            "{LIST_PREAMBLE}\
            (assert (not (exists ((l ilist)) (forall ((m ilist)) (= (len l) (len m))))))\n\
            (check-sat)\n"
        );
        let errors = check_str(&smt);
        // not(exists) = forall, then forall inside = no alternation (AA)
        assert!(errors.is_empty(), "expected no errors, got: {errors:?}");
    }

    #[test]
    fn implication_flips_polarity() {
        // (forall l => (forall m ...)) — antecedent flips polarity,
        // so inner forall in negative position = exists. This creates AE alternation.
        let smt = format!(
            "{LIST_PREAMBLE}\
            (assert (forall ((l ilist))\n\
              (=> (forall ((m ilist)) (>= (len m) 0))\n\
                (>= (len l) 0))))\n\
            (check-sat)\n"
        );
        let errors = check_str(&smt);
        assert_eq!(errors.len(), 1, "got: {errors:?}");
        assert!(errors[0].contains("Quantifier alternation"));
    }

    #[test]
    fn clean_file_no_errors() {
        let smt = format!(
            "{LIST_PREAMBLE}\
            (assert (forall ((l ilist))\n\
              (=> ((_ is Cons) l) (>= (len l) 1))))\n\
            (assert (= (len Nil) 0))\n\
            (check-sat)\n"
        );
        let errors = check_str(&smt);
        assert!(errors.is_empty(), "expected no errors, got: {errors:?}");
    }
}
