//! Static validator for SMT-LIB2 query files. Built on `smtlib-lowlevel`'s
//! parser, which handles tokenization, paren balance, and structural
//! well-formedness — anything malformed comes back as a `ValidationError::Parse`.
//!
//! On top of parsing we run name-resolution checks (forward references,
//! duplicate `:named` annotations, `set-option` after `set-logic`) and
//! reject `:pattern` triggers and `define-funs-rec` outright — see
//! `ValidationError` for the full taxonomy.
//!
//! Always run before sending a query to Z3 — see `validate_or_err`. Failures
//! dump the offending query to `/tmp/smt_tools_invalid_<pid>.smt2` for
//! inspection.

use smtlib_lowlevel::ast::{
    self, Attribute, AttributeValue, Command, DatatypeDec, FunctionDef, Identifier, Index,
    MatchCase, Pattern, QualIdentifier, Script, Term, VarBinding,
};
use smtlib_lowlevel::lexicon::Keyword;
use smtlib_lowlevel::{ParseError, Storage};
use std::collections::HashSet;

#[derive(Debug, Clone, PartialEq)]
enum ValidationError {
    Parse(String),
    OptionAfterLogic(String),
    ForwardRef { name: String, in_def: String },
    DuplicateNamed(String),
    /// A construct the validator deliberately refuses to check (e.g.
    /// `:pattern` triggers, `define-funs-rec`). If Cobb starts emitting
    /// these, decide explicitly how to validate them rather than letting
    /// the half-handled case slip silently.
    Unsupported(String),
}

impl std::fmt::Display for ValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            ValidationError::Parse(msg) => write!(f, "parse error: {}", msg),
            ValidationError::OptionAfterLogic(snippet) => write!(
                f,
                "(set-option ...) appears after (set-logic ...). Z3 silently ignores \
                 most options once the logic is fixed. Offending form: {}",
                snippet
            ),
            ValidationError::ForwardRef { name, in_def } => write!(
                f,
                "identifier `{}` referenced in `{}` is not declared earlier in the file \
                 (forward reference or undefined symbol)",
                name, in_def
            ),
            ValidationError::DuplicateNamed(name) => write!(
                f,
                "duplicate :named annotation `{}` — Z3 will reject",
                name
            ),
            ValidationError::Unsupported(msg) => write!(f, "unsupported construct: {}", msg),
        }
    }
}

impl std::error::Error for ValidationError {}

impl From<ParseError> for ValidationError {
    fn from(e: ParseError) -> Self {
        ValidationError::Parse(format!("{e}"))
    }
}

/// Constant-for-the-recursion context threaded through `check_term`.
/// `defined` and `in_def` are read-only within a single `check_term` call;
/// `errors` and `named_first` accumulate across the whole walk.
struct Ctx<'a> {
    defined: &'a HashSet<String>,
    in_def: &'a str,
    errors: &'a mut Vec<ValidationError>,
    named_first: &'a mut HashSet<String>,
}

fn builtin(s: &str) -> bool {
    matches!(
        s,
        // Logical / core
        "true" | "false" | "not" | "and" | "or" | "=>" | "xor" | "=" | "distinct" | "ite"
        | "let" | "forall" | "exists" | "match" | "!" | "_" | "as" | "par"
        // SMT-LIB sorts
        | "Bool" | "Int" | "Real" | "String" | "Array"
        // Arith
        | "+" | "-" | "*" | "/" | "div" | "mod" | "abs"
        | "<" | "<=" | ">" | ">="
        | "to_int" | "to_real" | "is_int"
        // Indexed-id heads
        | "is" | "extract" | "divisible"
        // Arrays
        | "select" | "store" | "const"
        // BitVec
        | "bvadd" | "bvsub" | "bvmul" | "bvneg" | "bvand" | "bvor" | "bvnot" | "bvxor"
        | "bvshl" | "bvlshr" | "bvashr" | "bvult" | "bvule" | "bvugt" | "bvuge"
        | "bvslt" | "bvsle" | "bvsgt" | "bvsge" | "concat" | "BitVec"
    ) || s.chars().all(|c| c.is_ascii_digit())
}

fn check_name(name: &str, locals: &HashSet<String>, ctx: &mut Ctx) {
    if !builtin(name) && !ctx.defined.contains(name) && !locals.contains(name) {
        ctx.errors.push(ValidationError::ForwardRef {
            name: name.to_string(),
            in_def: ctx.in_def.to_string(),
        });
    }
}

fn check_ident(id: &Identifier, locals: &HashSet<String>, ctx: &mut Ctx) {
    match id {
        Identifier::Simple(s) => check_name(s.0, locals, ctx),
        Identifier::Indexed(s, indices) => {
            // Head (`is`, `extract`, ...) is typically a builtin; check anyway.
            check_name(s.0, locals, ctx);
            // Symbolic indices reference user names — e.g. `(_ is Ctor)`.
            for idx in indices.iter() {
                if let Index::Symbol(sym) = idx {
                    check_name(sym.0, locals, ctx);
                }
            }
        }
    }
}

fn check_qual(qid: &QualIdentifier, locals: &HashSet<String>, ctx: &mut Ctx) {
    let id = match qid {
        QualIdentifier::Identifier(id) | QualIdentifier::Sorted(id, _) => id,
    };
    check_ident(id, locals, ctx);
}

fn check_term(term: &Term, locals: &HashSet<String>, ctx: &mut Ctx) {
    match term {
        Term::SpecConstant(_) => {}
        Term::Identifier(qid) => check_qual(qid, locals, ctx),
        Term::Application(qid, args) => {
            check_qual(qid, locals, ctx);
            for a in args.iter() {
                check_term(a, locals, ctx);
            }
        }
        Term::Let(bindings, body) => {
            // Bound RHS expressions evaluate in outer scope.
            for VarBinding(_, e) in bindings.iter() {
                check_term(e, locals, ctx);
            }
            let mut extended = locals.clone();
            for VarBinding(v, _) in bindings.iter() {
                extended.insert(v.0.to_string());
            }
            check_term(body, &extended, ctx);
        }
        Term::Forall(vars, body) | Term::Exists(vars, body) => {
            let mut extended = locals.clone();
            for ast::SortedVar(v, _) in vars.iter() {
                extended.insert(v.0.to_string());
            }
            check_term(body, &extended, ctx);
        }
        Term::Match(scrutinee, cases) => {
            check_term(scrutinee, locals, ctx);
            for MatchCase(pat, rhs) in cases.iter() {
                let mut extended = locals.clone();
                match pat {
                    Pattern::Symbol(s) => {
                        // Bare-symbol pattern is always a fresh binder per
                        // SMT-LIB, even if a constructor of the same name exists.
                        extended.insert(s.0.to_string());
                    }
                    Pattern::Application(ctor, vars) => {
                        check_name(ctor.0, locals, ctx);
                        for v in vars.iter() {
                            extended.insert(v.0.to_string());
                        }
                    }
                }
                check_term(rhs, &extended, ctx);
            }
        }
        Term::Annotation(body, attrs) => {
            check_term(body, locals, ctx);
            for attr in attrs.iter() {
                // Keyword tokens include the leading ':'.
                match attr {
                    Attribute::WithValue(Keyword(":named"), AttributeValue::Symbol(sym)) => {
                        let name = sym.0.to_string();
                        if !ctx.named_first.insert(name.clone()) {
                            ctx.errors.push(ValidationError::DuplicateNamed(name));
                        }
                    }
                    Attribute::WithValue(Keyword(":pattern"), _) => {
                        ctx.errors.push(ValidationError::Unsupported(format!(
                            ":pattern triggers are not validated (in `{}`). Add explicit \
                             trigger support if Cobb starts emitting them.",
                            ctx.in_def
                        )));
                    }
                    _ => {}
                }
            }
        }
    }
}

fn collect_dt_names(dt: &DatatypeDec) -> Vec<String> {
    let ctors = match dt {
        DatatypeDec::DatatypeDec(cs) | DatatypeDec::Par(_, cs) => cs,
    };
    let mut names = Vec::new();
    for ast::ConstructorDec(c, selectors) in ctors.iter() {
        let ctor = c.0.to_string();
        names.push(format!("is-{}", ctor));
        names.push(ctor);
        for ast::SelectorDec(sel, _) in selectors.iter() {
            names.push(sel.0.to_string());
        }
    }
    names
}

/// Names introduced by purely-declarative top-level forms. `define-fun(-rec)`
/// and `define-funs-rec` are handled inline in `validate_smt` because they
/// also need to walk a body.
fn collect_declared(cmd: &Command) -> Vec<String> {
    let mut names = Vec::new();
    match cmd {
        Command::DeclareConst(s, _)
        | Command::DeclareFun(s, _, _)
        | Command::DeclareSort(s, _)
        | Command::DefineSort(s, _, _) => names.push(s.0.to_string()),
        Command::DeclareDatatype(s, dt) => {
            names.push(s.0.to_string());
            names.extend(collect_dt_names(dt));
        }
        Command::DeclareDatatypes(sort_decs, dt_decs) => {
            for ast::SortDec(s, _) in sort_decs.iter() {
                names.push(s.0.to_string());
            }
            for dt in dt_decs.iter() {
                names.extend(collect_dt_names(dt));
            }
        }
        _ => {}
    }
    names
}

fn check_function_def(
    fd: &FunctionDef,
    defined: &HashSet<String>,
    named_first: &mut HashSet<String>,
    errors: &mut Vec<ValidationError>,
) {
    let FunctionDef(name, params, _ret, body) = fd;
    let mut locals = HashSet::new();
    for ast::SortedVar(p, _) in params.iter() {
        locals.insert(p.0.to_string());
    }
    let mut ctx = Ctx {
        defined,
        in_def: name.0,
        errors,
        named_first,
    };
    check_term(body, &locals, &mut ctx);
}

fn validate_smt(src: &str) -> Result<(), Vec<ValidationError>> {
    let storage = Storage::new();
    let script = Script::parse(&storage, src).map_err(|e| vec![ValidationError::from(e)])?;

    let mut errors: Vec<ValidationError> = Vec::new();
    let mut defined: HashSet<String> = HashSet::new();
    let mut seen_set_logic = false;
    let mut named_first: HashSet<String> = HashSet::new();

    for cmd in script.0.iter() {
        match cmd {
            Command::SetLogic(_) => seen_set_logic = true,
            Command::SetOption(opt) => {
                if seen_set_logic {
                    errors.push(ValidationError::OptionAfterLogic(format!("{opt}")));
                }
            }
            Command::DefineFun(fd) => {
                // Body checked against names defined *so far* — name itself
                // not yet inserted, so self-references in non-rec define-fun
                // would (correctly) flag.
                check_function_def(fd, &defined, &mut named_first, &mut errors);
                defined.insert(fd.0.0.to_string());
            }
            Command::DefineFunRec(fd) => {
                defined.insert(fd.0.0.to_string());
                check_function_def(fd, &defined, &mut named_first, &mut errors);
            }
            Command::DefineFunsRec(decs, _bodies) => {
                let names = decs
                    .iter()
                    .map(|ast::FunctionDec(s, _, _)| s.0)
                    .collect::<Vec<_>>()
                    .join(", ");
                errors.push(ValidationError::Unsupported(format!(
                    "define-funs-rec is not supported by the validator (functions: {names})"
                )));
                // Still register names so downstream uses don't cascade
                // unrelated ForwardRef errors.
                for ast::FunctionDec(s, _, _) in decs.iter() {
                    defined.insert(s.0.to_string());
                }
            }
            Command::Assert(t) => {
                let mut ctx = Ctx {
                    defined: &defined,
                    in_def: "assert",
                    errors: &mut errors,
                    named_first: &mut named_first,
                };
                check_term(t, &HashSet::new(), &mut ctx);
            }
            _ => defined.extend(collect_declared(cmd)),
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

/// Convenience: format a readable summary if validation fails, dumping the
/// offending query to /tmp so the builder can be inspected. Returns `Ok(())`
/// on success, `Err(message)` on failure — callers should surface the error
/// (e.g. `Z3Error::ValidatorRejected`) rather than continue with a known-malformed query.
pub(crate) fn validate_or_err(src: &str, context: &str) -> Result<(), String> {
    let errors = match validate_smt(src) {
        Ok(()) => return Ok(()),
        Err(e) => e,
    };
    let dump_path = format!("/tmp/smt_tools_invalid_{}.smt2", std::process::id());
    let _ = std::fs::write(&dump_path, src);
    let mut msg = format!(
        "validate_or_err: {} produced an invalid SMT query ({} errors):\n",
        context,
        errors.len()
    );
    for e in &errors {
        msg.push_str(&format!("  - {}\n", e));
    }
    msg.push_str(&format!("Full query dumped to {}\n", dump_path));
    Err(msg)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn good_file_passes() {
        let src = r#"
(set-logic ALL)
(declare-datatypes ((tree 0)) (((leaf) (node (val Int) (left tree) (right tree)))))
(declare-fun height (tree) Int)
(assert (forall ((t tree)) (>= (height t) 0)))
(check-sat)
"#;
        assert!(validate_smt(src).is_ok());
    }

    #[test]
    fn forward_ref_in_define_fun_caught() {
        // The exact bug class: define-fun whose body references a function
        // declared *later* in the file.
        let src = r#"
(set-logic ALL)
(define-fun ax_2 () Bool (num_black 0))
(declare-fun num_black (Int) Bool)
"#;
        let errs = validate_smt(src).unwrap_err();
        assert!(
            errs.iter().any(|e| matches!(e, ValidationError::ForwardRef { name, .. } if name == "num_black")),
            "expected ForwardRef for num_black, got {:?}",
            errs
        );
    }

    #[test]
    fn set_option_after_set_logic_caught() {
        let src = r#"
(set-logic ALL)
(set-option :timeout 60000)
"#;
        let errs = validate_smt(src).unwrap_err();
        assert!(
            errs.iter().any(|e| matches!(e, ValidationError::OptionAfterLogic { .. })),
            "expected OptionAfterLogic, got {:?}",
            errs
        );
    }

    #[test]
    fn duplicate_named_caught() {
        let src = r#"
(set-logic ALL)
(declare-fun p () Bool)
(assert (! p :named ax_1))
(assert (! p :named ax_1))
"#;
        let errs = validate_smt(src).unwrap_err();
        assert!(
            errs.iter().any(|e| matches!(e, ValidationError::DuplicateNamed(n) if n == "ax_1")),
            "expected DuplicateNamed for ax_1, got {:?}",
            errs
        );
    }

    #[test]
    fn unbalanced_open_caught() {
        let src = "(set-logic ALL\n(declare-fun p () Bool)";
        let errs = validate_smt(src).unwrap_err();
        assert!(
            errs.iter().any(|e| matches!(e, ValidationError::Parse(_))),
            "expected Parse error, got {:?}",
            errs
        );
    }

    #[test]
    fn datatype_constructors_recognized() {
        let src = r#"
(set-logic ALL)
(declare-datatypes ((tree 0)) (((leaf) (node (val Int) (left tree) (right tree)))))
(assert (forall ((t tree)) (=> ((_ is leaf) t) (= t leaf))))
(assert (forall ((t tree)) (=> ((_ is node) t) (>= (val t) 0))))
"#;
        let res = validate_smt(src);
        assert!(res.is_ok(), "expected ok, got {:?}", res);
    }

    #[test]
    fn match_pattern_binders_in_scope() {
        let src = r#"
(set-logic ALL)
(declare-datatypes ((tree 0)) (((leaf) (node (val Int) (left tree) (right tree)))))
(define-fun root ((t tree)) Int
  (match t ((leaf 0) ((node v l r) v))))
"#;
        let res = validate_smt(src);
        assert!(res.is_ok(), "expected ok, got {:?}", res);
    }

    #[test]
    fn bool_option_parses_after_local_patch() {
        // Upstream smtlib-lowlevel 0.3.0 has `todo!()` in its `bool` parse
        // impl, which panics on `(set-option :produce-unsat-cores true)` and
        // similar. Our [patch.crates-io] fork at vendor/smtlib-rs implements
        // bool parsing — this test pins that the patch is wired up. If the
        // patch is ever removed this test will fail (with a panic from the
        // upstream parser, surfaced by cargo test as a test failure).
        let src = "(set-option :produce-unsat-cores true)\n(set-logic ALL)\n";
        let res = validate_smt(src);
        assert!(res.is_ok(), "expected ok with patched parser, got {:?}", res);
    }

    #[test]
    fn pattern_trigger_is_rejected() {
        // Cobb doesn't emit :pattern triggers today; if it ever starts, we
        // want the validator to fail loud so we can decide explicitly how
        // to handle trigger-internal terms rather than silently miss
        // forward refs inside them.
        let src = r#"
(set-logic ALL)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (! (= (f x) (f x)) :pattern ((f x)))))
"#;
        let errs = validate_smt(src).unwrap_err();
        assert!(
            errs.iter().any(|e| matches!(e, ValidationError::Unsupported(msg) if msg.contains(":pattern"))),
            "expected Unsupported(:pattern), got {:?}",
            errs
        );
    }

    #[test]
    fn define_funs_rec_is_rejected() {
        // Same shape: skip-silently is the wrong default. Reject so the
        // first occurrence is a forced design decision, not a quiet hole.
        let src = r#"
(set-logic ALL)
(define-funs-rec ((even ((n Int)) Bool) (odd ((n Int)) Bool))
  ((ite (= n 0) true (odd (- n 1)))
   (ite (= n 0) false (even (- n 1)))))
"#;
        let errs = validate_smt(src).unwrap_err();
        assert!(
            errs.iter().any(|e| matches!(e, ValidationError::Unsupported(msg) if msg.contains("define-funs-rec"))),
            "expected Unsupported(define-funs-rec), got {:?}",
            errs
        );
    }

    #[test]
    fn let_binders_in_scope() {
        let src = r#"
(set-logic ALL)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (let ((y (f x))) (> y 0))))
"#;
        let res = validate_smt(src);
        assert!(res.is_ok(), "expected ok, got {:?}", res);
    }
}
