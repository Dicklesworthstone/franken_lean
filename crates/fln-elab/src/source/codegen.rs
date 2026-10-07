//! The pin's code generator refuses a compiled declaration that applies a recursor
//! directly (bead `franken_lean-z8j.1.6.6`): "code generator does not support recursor
//! `T.rec` yet, consider using 'match ... with' and/or structural recursion".
//!
//! The pin compiles every `def`, `instance` and `example` (not a theorem). Lowering
//! (vendored `src/Lean/Compiler/LCNF/ToLCNF.lean:817`, `visitApp`) first rewrites a
//! constant through its `@[csimp]` replacement, then handles `Eq.rec`, `HEq.rec`,
//! `And.rec`/`Iff.rec`, `False.rec`/`Empty.rec`, `casesOn`, constructors, `noConfusion`
//! and projections itself. A recursor that survives is refused at `ToImpure.lean:184`.
//! Proofs and types are erased first, so a recursor application whose motive lands in
//! `Prop` or in a sort is never compiled.
//!
//! FrankenLean has no pre-definition: `match`, `cases` and structural recursion are all
//! lowered to `T.rec` here, where the pin uses `casesOn` and `brecOn`, which it compiles.
//! So only the recursors the source itself names are checked: a recursor constant the
//! source resolves (`T.rec`, `@T.rec`, `T.rec (motive := …)`) and the one an `induction`
//! tactic applies. Each relevant application of such a recursor in the elaborated value
//! is refused. Not established, and stated: a definition that names `T.rec` only in a
//! proof but also matches on `T` in data is refused here and accepted by the pin; a
//! data-valued recursor application nested inside a proof or type argument, or in code
//! the pin's simplifier deletes, is refused here and erased there.
//!
//! Executing such recursors is FrankenLean's `frontier` lane: an engine in that mode
//! sets [`SourceScope::frontier_recursors`] and this check is skipped. Its artifacts
//! carry the frontier mode, which default consumers refuse (D-18).
//!
//! The csimp set is derived, never remembered: `csimp_recursors.tsv` is generated from
//! the pinned `lean` by `scripts/extract/gen_seed_csimp.sh`. A table that does not read
//! makes no recursor compilable, so it can only refuse more, never accept a definition
//! the pin refuses.
use super::*;
use fln_env::constants::ConstantInfo;
use std::collections::{BTreeSet, HashSet};

const CSIMP_TABLE: &str = include_str!("../seed/csimp_recursors.tsv");
const CSIMP_SCHEMA: &str = "schema fln-seed-csimp-recursors/1";

/// Recursors the pin's `visitApp` lowers itself (ToLCNF.lean:824-831). Its `Eq.recOn`
/// and `Eq.ndrec` cases are definitions here, never recursor constants.
const SPECIAL_RECURSORS: [[&str; 2]; 6] = [
    ["Eq", "rec"],
    ["HEq", "rec"],
    ["And", "rec"],
    ["Iff", "rec"],
    ["False", "rec"],
    ["Empty", "rec"],
];

fn parse_csimp(table: &str) -> Option<BTreeSet<Name>> {
    let mut lines = table.lines().filter(|line| !line.starts_with('#'));
    if lines.next() != Some(CSIMP_SCHEMA) {
        return None;
    }
    let mut recursors = BTreeSet::new();
    let mut previous: Option<&str> = None;
    for line in lines {
        let (recursor, replacement) = line.split_once('\t')?;
        let valid = |text: &str| {
            !text.is_empty()
                && text
                    .split('.')
                    .all(|part| !part.is_empty() && !part.chars().any(char::is_whitespace))
        };
        // The generator sorts with `LC_ALL=C sort`: byte order, each recursor once.
        if !valid(recursor)
            || !valid(replacement)
            || previous.is_some_and(|previous| previous.as_bytes() >= recursor.as_bytes())
        {
            return None;
        }
        previous = Some(recursor);
        recursors.insert(Name::from_components(recursor.split('.')));
    }
    Some(recursors)
}

/// The recursors the pin's csimp set replaces under `import Init`.
pub(super) fn csimp_recursors() -> &'static BTreeSet<Name> {
    static RECURSORS: std::sync::OnceLock<BTreeSet<Name>> = std::sync::OnceLock::new();
    RECURSORS.get_or_init(|| parse_csimp(CSIMP_TABLE).unwrap_or_default())
}

/// Whether the pin's code generator compiles an application of the recursor `name`.
fn compiles(name: &Name) -> bool {
    SPECIAL_RECURSORS
        .iter()
        .any(|parts| *name == Name::from_components(*parts))
        || csimp_recursors().contains(name)
}

/// A motive whose body is a sort, or a function type ending in one, builds types: the
/// pin erases what it produces.
fn type_former_motive(motive: &Expr) -> bool {
    let mut body = motive;
    loop {
        match body.node() {
            ExprNode::Lam { body: inner, .. } | ExprNode::ForallE { body: inner, .. } => {
                body = inner;
            }
            ExprNode::MData { expr, .. } => body = expr,
            ExprNode::Sort { .. } => return true,
            _ => return false,
        }
    }
}

impl Context {
    /// Record a recursor the source names, for [`Self::check_compiled_recursors`].
    pub(super) fn note_source_recursor(&mut self, name: &Name) {
        if !self.source_recursors.contains(name) {
            self.source_recursors.push(name.clone());
        }
    }

    /// Refuse `value`, a compiled declaration's elaborated value, when it applies a
    /// recursor the source named that the pin's code generator does not support, in a
    /// position the pin does not erase.
    pub(super) fn check_compiled_recursors(
        &mut self,
        value: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        if self.source_scope.frontier_recursors {
            return Ok(());
        }
        let named: Vec<Name> = self
            .source_recursors
            .iter()
            .filter(|name| !compiles(name))
            .cloned()
            .collect();
        if named.is_empty() {
            return Ok(());
        }
        let mut seen = HashSet::new();
        let mut work = vec![value.clone()];
        while let Some(expr) = work.pop() {
            self.tick()?;
            if !seen.insert(expr.allocation_identity()) {
                continue;
            }
            match expr.node() {
                ExprNode::App { .. } | ExprNode::Const { .. } => {
                    let mut args = Vec::new();
                    let mut head = &expr;
                    while let ExprNode::App { f, a } = head.node() {
                        args.push(a.clone());
                        head = f;
                    }
                    args.reverse();
                    if let ExprNode::Const { name, levels } = head.node() {
                        if named.contains(name) && self.compiled_application(name, levels, &args) {
                            return Err(failure(SourceInferenceError::UnsupportedRecursor(
                                name.clone(),
                            )));
                        }
                    } else {
                        work.push(head.clone());
                    }
                    work.extend(args);
                }
                // Binder and let types are types: erased.
                ExprNode::Lam { body, .. } => work.push(body.clone()),
                ExprNode::LetE { value, body, .. } => {
                    work.push(value.clone());
                    work.push(body.clone());
                }
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                    work.push(expr.clone());
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Whether an application of the recursor `name` at `levels` to `args` produces data
    /// the pin compiles: neither a proof nor a type.
    fn compiled_application(&self, name: &Name, levels: &[Level], args: &[Expr]) -> bool {
        let Some(ConstantInfo::Rec(recursor)) = self.txn.env.find(name) else {
            return false;
        };
        let family = name.parent();
        let Some(ConstantInfo::Induct(inductive)) = self.txn.env.find(&family) else {
            return true;
        };
        // Without a universe of its own the recursor eliminates only into `Prop`.
        if recursor.base.level_params.len() <= inductive.base.level_params.len()
            || levels.first().is_some_and(Level::is_zero)
        {
            return false;
        }
        let index = recursor
            .all
            .iter()
            .position(|member| *member == family)
            .unwrap_or(0);
        match args.get(recursor.num_params as usize + index) {
            Some(motive) => !type_former_motive(motive),
            None => true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_checked_in_csimp_table_reads_and_names_the_pins_compiled_recursors() {
        let recursors = parse_csimp(CSIMP_TABLE).expect("the generated table reads");
        assert!(recursors.contains(&Name::from_components(["Nat", "rec"])));
        assert!(recursors.contains(&Name::from_components(["Acc", "rec"])));
        assert!(!recursors.contains(&Name::from_components(["List", "rec"])));
        assert_eq!(csimp_recursors(), &recursors);
    }

    #[test]
    fn a_malformed_csimp_table_reads_as_nothing() {
        assert_eq!(parse_csimp(""), None);
        assert_eq!(
            parse_csimp("schema other/1\nNat.rec\tNat.recCompiled"),
            None
        );
        assert_eq!(
            parse_csimp(&format!(
                "{CSIMP_SCHEMA}\nNat.rec\tNat.recCompiled\nAcc.rec\tAcc.recC"
            )),
            None,
            "rows out of byte order"
        );
        assert_eq!(parse_csimp(&format!("{CSIMP_SCHEMA}\nNat.rec")), None);
    }

    #[test]
    fn motives_that_build_types_are_recognized() {
        let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
        let to_type = Expr::lam(
            Name::from_components(["t"]),
            nat.clone(),
            Expr::sort(Level::one()),
            BinderInfo::Default,
        );
        let to_nat = Expr::lam(
            Name::from_components(["t"]),
            nat.clone(),
            nat.clone(),
            BinderInfo::Default,
        );
        let to_family = Expr::lam(
            Name::from_components(["t"]),
            nat.clone(),
            Expr::forall_e(
                Name::from_components(["n"]),
                nat.clone(),
                Expr::sort(Level::one()),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        assert!(type_former_motive(&to_type));
        assert!(type_former_motive(&to_family));
        assert!(!type_former_motive(&to_nat));
    }
}
