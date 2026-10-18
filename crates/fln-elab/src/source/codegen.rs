//! The pin's code generator refuses a compiled declaration that applies a recursor
//! directly (bead `franken_lean-z8j.1.6.6`): "code generator does not support recursor
//! `T.rec` yet, consider using 'match ... with' and/or structural recursion".
//!
//! The pin compiles `def`, `instance` and `example` unless marked `noncomputable`,
//! and never a theorem. Lowering
//! (vendored `src/Lean/Compiler/LCNF/ToLCNF.lean:817`, `visitApp`) first rewrites a
//! constant through its `@[csimp]` replacement, then handles `Eq.rec`, `HEq.rec`,
//! `And.rec`/`Iff.rec`, `False.rec`/`Empty.rec`, `casesOn`, constructors, `noConfusion`
//! and projections itself. A recursor that survives is refused at `ToImpure.lean:184`.
//! Proofs and types are erased first, so a recursor application whose motive lands in
//! `Prop` or in a sort is never compiled.
//!
//! FrankenLean has no pre-definition: `match`, `cases` and structural recursion are all
//! lowered to `T.rec` here, where the pin compiles its pre-definition lowering.
//! Directly naming a generated `recOn`, `brecOn`, or `brecOn.go` is different:
//! those definitions have no compiled LCNF signature in the pin.
//! So only the recursors the source itself names are checked: a recursor constant the
//! source resolves (`T.rec`, `@T.rec`, `T.rec (motive := …)`) and the one an `induction`
//! tactic applies. Each relevant application of such a recursor in the elaborated value
//! is refused. Not established, and stated: a definition that names `T.rec` only in a
//! proof but also matches on `T` in data is refused here and accepted by the pin; a
//! recursor application in code the pin's simplifier deletes can still be refused here.
//! Nested proof and type subtrees are classified before their bodies are visited, as
//! ToLCNF.visit/visitAppArg do; data computations inside those erased subtrees never
//! require an executable recursor.
//!
//! Executing such recursors is FrankenLean's `frontier` lane: an engine in that mode
//! sets [`SourceScope::frontier_recursors`] and the recursor restriction is skipped.
//! Noncomputable dependencies remain non-executable in every mode. Its artifacts
//! carry the frontier mode, which default consumers refuse (D-18).
//!
//! The csimp set is derived, never remembered: `csimp_recursors.tsv` is generated from
//! the pinned `lean` by `scripts/extract/gen_seed_csimp.sh`. A table that does not read
//! makes no recursor compilable, so it can only refuse more, never accept a definition
//! the pin refuses.
use super::*;
use fln_env::constants::ConstantInfo;
use std::collections::{BTreeSet, HashSet};

mod dependencies;
mod types;

#[cfg(test)]
mod constructor_erasure_tests;

const CSIMP_TABLE: &str = include_str!("../seed/csimp_recursors.tsv");
const CSIMP_SCHEMA: &str = "schema fln-seed-csimp-recursors/1";

/// Recursors the pin's `visitApp` lowers itself (ToLCNF.lean:824-831).
/// Eq.recOn is a tagged definition. Other generated recOn wrappers have no
/// compiled signature, even when their underlying recursor has a csimp rule.
const SPECIAL_RECURSORS: [[&str; 2]; 7] = [
    ["Eq", "rec"],
    ["Eq", "recOn"],
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

/// Return the explicit tag and underlying checked recursor for a generated
/// wrapper. The helper carries its parent's tag, not one of its own. Spelling
/// alone is never sufficient: the caller must validate that tag in the journal.
fn auxiliary_origin(name: &Name) -> Option<(Name, Name)> {
    let helper = matches!(name.leaf_view(), LeafView::Str("go"));
    let tagged = if helper { name.parent() } else { name.clone() };
    let suffix = match tagged.leaf_view() {
        LeafView::Str("recOn") if !helper => "",
        LeafView::Str("brecOn") => "",
        LeafView::Str(s) => {
            let suffix = s.strip_prefix("brecOn_")?;
            let index = suffix.parse::<u32>().ok()?;
            if index == 0 || suffix != index.to_string() {
                return None;
            }
            return Some((
                tagged.clone(),
                Name::str(tagged.parent(), format!("rec_{index}")),
            ));
        }
        _ => return None,
    };
    Some((
        tagged.clone(),
        Name::str(tagged.parent(), format!("rec{suffix}")),
    ))
}

impl Context {
    /// Deferred compilation effects must validate the admitted successor's
    /// metadata even when the original body already had a known compiler error.
    pub(super) fn validate_codegen_metadata(&mut self) -> Result<(), NatDefinitionElabError> {
        dependencies::Dependencies::read(self).map(|_| ())
    }

    /// `noncomputable section` suppresses only a known declaration compiler
    /// refusal. Parsing, typing, resource stops, malformed metadata and faults
    /// are not compiler failures and must never be converted to this effect.
    /// Evaluation calls `check_compiled_recursors` directly, so the section
    /// cannot turn a failed `#eval` into an admitted but unexecuted query.
    /// Partial batches carry this effect to their exact admitted companions.
    pub(super) fn check_definition_codegen(
        &mut self,
        term: &Typed,
    ) -> Result<bool, NatDefinitionElabError> {
        match self.check_compiled_recursors(term) {
            Ok(()) => Ok(false),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::UnsupportedRecursor(_)
                | SourceInferenceError::AuxiliaryNotCompiled(_)
                | SourceInferenceError::NoncomputableDependency(_),
            )) if self.source_scope.noncomputable_section => Ok(true),
            Err(error) => Err(error),
        }
    }

    /// Track both ordinary constants and constants with explicit universe arguments.
    /// Elaboration's own eliminations construct their recursor constants directly.
    pub(super) fn note_resolved_recursor(
        &mut self,
        name: &Name,
        info: &ConstantInfo,
    ) -> Result<(), NatDefinitionElabError> {
        let generated = if matches!(info, ConstantInfo::Defn(_)) {
            if let Some((tagged, recursor)) = auxiliary_origin(name) {
                self.is_auxiliary_recursor(&tagged)?
                    && matches!(self.txn.env.find(&recursor), Some(ConstantInfo::Rec(_)))
            } else {
                false
            }
        } else {
            false
        };
        if matches!(info, ConstantInfo::Rec(_)) || generated {
            self.note_source_recursor(name);
        }
        Ok(())
    }

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
        term: &Typed,
    ) -> Result<(), NatDefinitionElabError> {
        let named: Vec<Name> = self
            .source_recursors
            .iter()
            .filter(|name| !self.source_scope.frontier_recursors && !compiles(name))
            .cloned()
            .collect();
        let dependencies = dependencies::Dependencies::read(self)?;
        // Untagged axioms can still lack executable code. An empty registry
        // must not bypass the typed walk of a computational declaration.
        // Proof declarations and type formers have no runtime body. This is
        // also necessary for brecOn.go: its PProd result is data even with a
        // Prop-valued motive, but a projection used solely as a proof erases.
        if self.codegen_type_former(&term.type_)? {
            return Ok(());
        }
        if let Some(sort) = self.known_type(&term.type_)? {
            let sort = self.whnf(&sort)?;
            if matches!(sort.node(), ExprNode::Sort { level } if level.is_zero()) {
                return Ok(());
            }
        }
        let saved = self.txn.lctx.clone();
        let result = self.check_compiled_value(&term.value, &named, &dependencies);
        // A refusal may unwind past pending Restore tasks. Temporary binders
        // are analysis only and must never escape, including on budget stops.
        self.txn.lctx = saved;
        result
    }

    /// ToLCNF.visit/visitAppArg erase proofs and type formers before inspecting
    /// their executable subexpressions. Unknown types are not evidence of
    /// erasure: retain the conservative recursor walk in that case.
    fn codegen_erased(&mut self, value: &Expr) -> Result<bool, NatDefinitionElabError> {
        let Some(type_) = self.known_type(value)? else {
            return Ok(false);
        };
        if self.codegen_type_former(&type_)? {
            return Ok(true);
        }
        let Some(sort) = self.known_type(&type_)? else {
            return Ok(false);
        };
        let sort = self.whnf(&sort)?;
        Ok(matches!(sort.node(), ExprNode::Sort { level } if level.is_zero()))
    }

    fn check_compiled_value(
        &mut self,
        value: &Expr,
        named: &[Name],
        dependencies: &dependencies::Dependencies,
    ) -> Result<(), NatDefinitionElabError> {
        enum Work {
            Visit(Expr),
            OpenLet(Name, Expr, Expr, Expr),
            Restore(LocalContext),
        }
        // Every binder is opened with a fresh local identity. Exact expression
        // keys therefore cannot confuse one de Bruijn node used in two scopes,
        // and retaining expressions prevents allocation-address reuse.
        let mut seen = HashSet::new();
        let mut work = vec![Work::Visit(value.clone())];
        while let Some(task) = work.pop() {
            self.tick()?;
            let expr = match task {
                Work::Restore(saved) => {
                    self.txn.lctx = saved;
                    continue;
                }
                Work::OpenLet(name, type_, value, body) => {
                    let saved = self.txn.lctx.clone();
                    let id = FVarId(self.fresh_name()?);
                    self.txn.lctx.add_let(id.clone(), name, type_, value);
                    let body = self.substitute(&body, &Expr::fvar(id))?;
                    work.push(Work::Restore(saved));
                    work.push(Work::Visit(body));
                    continue;
                }
                Work::Visit(expr) => expr,
            };
            if !seen.insert(expr.clone()) || self.codegen_erased(&expr)? {
                continue;
            }
            match expr.node() {
                ExprNode::App { .. } | ExprNode::Const { .. } => {
                    let mut args = Vec::new();
                    let mut head = &expr;
                    while let ExprNode::App { f, a } = head.node() {
                        self.tick()?;
                        args.push(a.clone());
                        head = f;
                    }
                    args.reverse();
                    let mut erased_params = 0;
                    if let ExprNode::Const { name, levels } = head.node() {
                        dependencies.check(name)?;
                        // ToLCNF.visitCtor ignores noncomputability throughout
                        // constructor parameters, which toMono later erases.
                        // A parameter can itself be data (e.g. `n : Nat` in
                        // `Box n`), so inspecting only its type is insufficient.
                        // Read the admitted constructor's arity, never a name
                        // convention. Fields and overapplication remain live;
                        // the constructor itself still needs executable code.
                        if let Some(ConstantInfo::Ctor(ctor)) = self.txn.env.find(name) {
                            erased_params = (ctor.num_params as usize).min(args.len());
                        }
                        if named.contains(name) && self.compiled_application(name, levels, &args)? {
                            if matches!(self.txn.env.find(name), Some(ConstantInfo::Defn(_))) {
                                return Err(failure(SourceInferenceError::AuxiliaryNotCompiled(
                                    name.clone(),
                                )));
                            }
                            return Err(failure(SourceInferenceError::UnsupportedRecursor(
                                name.clone(),
                            )));
                        }
                    } else {
                        work.push(Work::Visit(head.clone()));
                    }
                    work.extend(args.into_iter().skip(erased_params).map(Work::Visit));
                }
                // Domains are erased; bodies are opened rather than walking
                // loose bvars without the telescope that gives them meaning.
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => {
                    let saved = self.txn.lctx.clone();
                    let id = FVarId(self.fresh_name()?);
                    self.txn.lctx.add_param(
                        id.clone(),
                        binder_name.clone(),
                        binder_type.clone(),
                        *binder_info,
                    );
                    let body = self.substitute(body, &Expr::fvar(id))?;
                    work.push(Work::Restore(saved));
                    work.push(Work::Visit(body));
                }
                ExprNode::LetE {
                    decl_name,
                    type_,
                    value,
                    body,
                    ..
                } => {
                    // The value is checked outside its own binding, then the
                    // body sees the checked let for dependent type inference.
                    work.push(Work::OpenLet(
                        decl_name.clone(),
                        type_.clone(),
                        value.clone(),
                        body.clone(),
                    ));
                    work.push(Work::Visit(value.clone()));
                }
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                    work.push(Work::Visit(expr.clone()));
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Whether an application of the recursor `name` at `levels` to `args` produces data
    /// the pin compiles: neither a proof nor a type.
    fn compiled_application(
        &mut self,
        name: &Name,
        levels: &[Level],
        args: &[Expr],
    ) -> Result<bool, NatDefinitionElabError> {
        let recursor = match self.txn.env.find(name) {
            Some(ConstantInfo::Rec(recursor)) => recursor,
            // Only explicitly tagged wrappers (or their checked go helper)
            // enter source_recursors. Their motive parameter positions agree
            // with the original recursor even though its minors are replaced.
            Some(ConstantInfo::Defn(_)) => {
                // go returns PProd, including for a Prop-valued motive. Its
                // complete proof/type uses were erased above; a remaining data
                // application always requires the missing compiled signature.
                if matches!(name.leaf_view(), LeafView::Str("go")) {
                    return Ok(true);
                }
                let Some((_, recursor_name)) = auxiliary_origin(name) else {
                    return Ok(true);
                };
                let Some(ConstantInfo::Rec(recursor)) = self.txn.env.find(&recursor_name) else {
                    return Ok(true);
                };
                recursor
            }
            _ => return Ok(false),
        };
        let family = recursor.base.name.parent();
        let Some(ConstantInfo::Induct(inductive)) = self.txn.env.find(&family) else {
            return Ok(true);
        };
        // Without a universe of its own the recursor eliminates only into `Prop`.
        if recursor.base.level_params.len() <= inductive.base.level_params.len()
            || levels.first().is_some_and(Level::is_zero)
        {
            return Ok(false);
        }
        let type_ = recursor.base.type_.clone();
        let params = recursor.num_params as usize;
        let motives = recursor.num_motives as usize;
        let Some(index) = self.result_motive_argument(&type_, params, motives)? else {
            return Ok(true);
        };
        Ok(match args.get(index) {
            Some(motive) => !type_former_motive(motive),
            None => true,
        })
    }

    /// The actual result motive can belong to a nested container rather than
    /// the recursor's owning inductive. Read its bound-variable position from
    /// the checked telescope instead of inferring it from the owner's name.
    fn result_motive_argument(
        &mut self,
        type_: &Expr,
        params: usize,
        motives: usize,
    ) -> Result<Option<usize>, NatDefinitionElabError> {
        let mut body = type_;
        let mut binders = 0usize;
        loop {
            self.tick()?;
            match body.node() {
                ExprNode::ForallE { body: next, .. } => {
                    let Some(next_count) = binders.checked_add(1) else {
                        return Ok(None);
                    };
                    binders = next_count;
                    body = next;
                }
                ExprNode::MData { expr, .. } => body = expr,
                _ => break,
            }
        }
        loop {
            self.tick()?;
            match body.node() {
                ExprNode::App { f, .. } => body = f,
                ExprNode::MData { expr, .. } => body = expr,
                ExprNode::BVar { idx } => {
                    let Some(index) = binders.checked_sub(*idx as usize + 1) else {
                        return Ok(None);
                    };
                    return Ok(index
                        .checked_sub(params)
                        .filter(|motive| *motive < motives)
                        .map(|_| index));
                }
                _ => return Ok(None),
            }
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
    fn codegen_locals_are_restored_at_every_heartbeat_stop() {
        let env = crate::seed::bootstrap_nat_environment(Budget::DEFAULT).unwrap();
        let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());
        let name = Name::from_components(["x"]);
        let term = Typed {
            type_: Expr::forall_e(name.clone(), nat.clone(), nat.clone(), BinderInfo::Default),
            value: Expr::lam(
                name.clone(),
                nat.clone(),
                Expr::let_e(
                    name.clone(),
                    nat.clone(),
                    Expr::bvar(0).unwrap(),
                    Expr::bvar(0).unwrap(),
                    false,
                ),
                BinderInfo::Default,
            ),
        };
        let context = || {
            let mut context = Context::new(&env, Budget::DEFAULT);
            context
                .source_recursors
                .push(Name::from_components(["T", "rec"]));
            context.txn.lctx.add_param(
                FVarId(Name::from_components(["existing"])),
                name.clone(),
                nat.clone(),
                BinderInfo::Default,
            );
            context
        };
        let mut complete = context();
        let saved = complete.txn.lctx.clone();
        complete.check_compiled_recursors(&term).unwrap();
        assert_eq!(complete.txn.lctx, saved);
        let steps = complete.txn.budget.heartbeats_consumed;
        assert!(steps > 1, "the check must actually visit binders");
        for allowed in 1..steps {
            let mut limited = context();
            limited.txn.budget.max_heartbeats = allowed;
            assert!(
                limited.check_compiled_recursors(&term).is_err(),
                "bound {allowed}"
            );
            assert_eq!(limited.txn.lctx, saved, "locals escaped at bound {allowed}");
            assert_eq!(limited.txn.env, env);
        }
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
