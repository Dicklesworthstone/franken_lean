//! A selected-declaration fixture, never full IO module admission.
//!
//! Raw actual IO metadata discovers the test's dependency slice only. All pin
//! declarations in the execution engine are admitted with both readers/checkers
//! before their actual metadata is registered and source is checked again.
use super::*;
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    ExprNode, IndependentReading, OleanCheckLimits, OleanDecodeLimits, OleanFrontierJobs,
    OleanModuleInput,
};
use fln_elab::instances::{self, imported::ImportActivation};
use fln_olean::region::OleanView;
use fln_olean::source_extensions as metadata;
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::num::NonZeroUsize;
use std::time::Instant;

#[path = "../runtime_io_evaluation/actual.rs"]
mod actual;

type Parts = (Vec<u8>, Option<Vec<u8>>, Option<Vec<u8>>);

// Only checked declarations are produced here. These paths are never opened:
// the raw discovery engine never executes any test action or printer.
const DISCOVERY: &str = r#"
def ioSelectPure := (pure 42 : IO Nat)
def ioSelectBase := (pure 42 : BaseIO Nat)
def ioSelectEio := (pure 42 : EIO IO.Error Nat)
def ioSelectUnit := (pure () : IO Unit)
def ioSelectBaseUnit := (pure () : BaseIO Unit)
def ioSelectString := (pure "λ🙂" : IO String)
def ioSelectAppend : String := String.append "[" "]"
def ioSelectRecord := (pure (IoPrintRecord.mk true) : IO IoPrintRecord)
def ioSelectTree := (pure (IoPrintTree.leaf true) : IO IoPrintTree)
def ioSelectAlias := (pure (show IoPayloadAlias from (42 : Nat)) : IO IoPayloadAlias)
def ioSelectMap : IO Std.Format :=
  Functor.map (f := IO) (fun (value : Nat) => repr value) (pure 42 : IO Nat)
def ioSelectBaseMap : BaseIO Std.Format :=
  Functor.map (f := BaseIO) (fun (value : Nat) => repr value) (pure 42 : BaseIO Nat)
def ioSelectEioMap : EIO IO.Error Std.Format :=
  Functor.map (f := EIO IO.Error) (fun (value : Nat) => repr value) (pure 42 : EIO IO.Error Nat)
def ioSelectEffect : IO IoBoth := do
  let h ← IO.FS.Handle.mk "/fln-not-executed-discovery" IO.FS.Mode.append
  h.putStr "action\n"
  return IoBoth.mk
def ioSelectThrow : IO IoPrinterMustNotRun := do
  let h ← IO.FS.Handle.mk "/fln-not-executed-discovery" IO.FS.Mode.append
  h.putStr "before exception\n"
  throw (IO.userError "expected failure")
"#;

fn artifacts(library: &Path, root: &Name) -> BTreeMap<Name, Parts> {
    let mut pending = vec![root.clone()];
    let mut modules = BTreeMap::new();
    while let Some(module) = pending.pop() {
        if modules.contains_key(&module) {
            continue;
        }
        let path = library
            .join(module.to_display_string().replace('.', "/"))
            .with_extension("olean");
        let public = std::fs::read(&path).unwrap();
        pending.extend(fln::olean_module_imports(&public, OleanDecodeLimits::new(BYTES)).unwrap());
        let optional = |path: PathBuf| match std::fs::read(&path) {
            Ok(bytes) => Some(bytes),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => panic!("{}: {error}", path.display()),
        };
        modules.insert(
            module,
            (
                public,
                optional(path.with_extension("olean.server")),
                optional(path.with_extension("olean.private")),
            ),
        );
    }
    modules
}

fn references(expression: &Expr, output: &mut BTreeSet<Name>) {
    let mut pending = vec![expression];
    let mut seen = HashSet::new();
    while let Some(expression) = pending.pop() {
        if !seen.insert(std::ptr::from_ref(expression.node())) {
            continue;
        }
        assert!(seen.len() <= 1_000_000, "bounded fixture dependency walk");
        match expression.node() {
            ExprNode::Const { name, .. } => {
                output.insert(name.clone());
            }
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } => pending.push(expr),
            ExprNode::Proj {
                struct_name, expr, ..
            } => {
                output.insert(struct_name.clone());
                pending.push(expr);
            }
            ExprNode::BVar { .. }
            | ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Lit { .. } => {}
        }
    }
}

fn dependencies(info: &ConstantInfo, recursors: &BTreeMap<Vec<Name>, Vec<Name>>) -> BTreeSet<Name> {
    let mut output = BTreeSet::new();
    references(&info.constant_val().type_, &mut output);
    match info {
        ConstantInfo::Defn(value) => {
            references(&value.value, &mut output);
            output.extend(value.all.iter().cloned());
        }
        ConstantInfo::Thm(value) => {
            references(&value.value, &mut output);
            output.extend(value.all.iter().cloned());
        }
        ConstantInfo::Opaque(value) => {
            references(&value.value, &mut output);
            output.extend(value.all.iter().cloned());
        }
        ConstantInfo::Induct(value) => {
            output.extend(value.all.iter().cloned());
            output.extend(value.ctors.iter().cloned());
            output.extend(recursors.get(&value.all).into_iter().flatten().cloned());
        }
        ConstantInfo::Ctor(value) => {
            output.insert(value.induct.clone());
        }
        ConstantInfo::Rec(value) => {
            output.extend(value.all.iter().cloned());
            for rule in &value.rules {
                output.insert(rule.ctor.clone());
                references(&rule.rhs, &mut output);
            }
        }
        ConstantInfo::Axiom(_) | ConstantInfo::Quot(_) => {}
    }
    output
}

fn artifact_order(parts: &BTreeMap<Name, Parts>, root: &Name) -> Vec<Name> {
    let imports: BTreeMap<_, _> = parts
        .iter()
        .map(|(name, (public, _, _))| {
            (
                name.clone(),
                fln::olean_module_imports(public, OleanDecodeLimits::new(BYTES)).unwrap(),
            )
        })
        .collect();
    let mut seen = BTreeSet::new();
    let mut order = Vec::new();
    let mut pending = vec![(root.clone(), false)];
    while let Some((module, exit)) = pending.pop() {
        if exit {
            order.push(module);
            continue;
        }
        if !seen.insert(module.clone()) {
            continue;
        }
        pending.push((module.clone(), true));
        pending.extend(
            imports[&module]
                .iter()
                .rev()
                .cloned()
                .map(|module| (module, false)),
        );
    }
    assert_eq!(order.len(), parts.len());
    order
}

fn base(library: &Path) -> Engine {
    let roots = [
        name("Init.System.ST"),
        name("Init.Data.Repr"),
        name("Init.Data.ToString.Basic"),
    ];
    let mut parts = BTreeMap::new();
    for root in &roots {
        parts.extend(artifacts(library, root));
    }
    assert!(parts.contains_key(&name("Init.System.ST")));
    assert!(!parts.contains_key(&name("Init.System.IO")));
    assert!(!parts.contains_key(&name("Init.System.FilePath")));
    let inputs: Vec<_> = parts
        .iter()
        .map(|(name, (public, server, private))| OleanModuleInput {
            name,
            artifact: public,
            server_artifact: server.as_deref(),
            private_artifact: private.as_deref(),
        })
        .collect();
    let mut limits =
        SourceOleanImportLimits::new(OleanCheckLimits::new(BYTES, Budget::for_stack_bytes(STACK)));
    limits.jobs = OleanFrontierJobs {
        threads: NonZeroUsize::new(1).unwrap(),
        worker_stack_bytes: STACK,
    };
    let start = Instant::now();
    eprintln!(
        "IO printing fixture: admitting full ST/Repr/ToString closure ({} modules)",
        inputs.len()
    );
    let import = Engine::from_environment(Environment::new())
        .import_olean_modules_for_source(&inputs, &roots, &KVMap::new(), limits)
        .unwrap()
        .into_complete()
        .expect("the complete base closure passes both checkers");
    assert_eq!(import.checked.modules.len(), inputs.len());
    for module in &import.checked.modules {
        assert!(matches!(
            module.decoded.independent,
            IndependentReading::Read(_)
        ));
        assert_eq!(module.declarations.len(), module.decoded.constants.len());
    }
    eprintln!(
        "IO printing fixture: full base admitted in {:?}",
        start.elapsed()
    );
    import.engine
}

fn read_metadata(parts: &Parts) -> metadata::SourceExtensions {
    let (public, server, private) = parts;
    let decoded = fln::decode_olean_module_artifacts(
        public,
        server.as_deref().unwrap_or_default(),
        private.as_deref().unwrap_or_default(),
        OleanDecodeLimits::new(BYTES),
    )
    .unwrap();
    let view = if decoded.module.is_module {
        OleanView::parse_with_dependencies(
            private.as_deref().unwrap(),
            &[public.as_slice(), server.as_deref().unwrap()],
        )
    } else {
        OleanView::parse(public)
    }
    .unwrap();
    let limits =
        SourceOleanImportLimits::new(OleanCheckLimits::new(BYTES, Budget::for_stack_bytes(STACK)));
    let mut blocks = view
        .extension_payloads(limits.capture, limits.max_capture_bytes)
        .unwrap();
    let wanted = [
        metadata::CLASS_EXTENSION,
        metadata::INSTANCE_EXTENSION,
        metadata::DEFAULT_EXTENSION,
        metadata::ALIAS_EXTENSION,
        metadata::PROTECTED_EXTENSION,
        metadata::REDUCIBILITY_EXTENSION,
        metadata::EXTERN_EXTENSION,
        metadata::IMPLEMENTED_BY_EXTENSION,
    ]
    .map(name);
    blocks.retain(|block| wanted.contains(&block.name));
    metadata::decode(&blocks, limits.metadata).unwrap()
}

fn key(key: metadata::InstanceKey) -> instances::discr_tree::Key {
    use instances::discr_tree::Key;
    match key {
        metadata::InstanceKey::Star => Key::Star,
        metadata::InstanceKey::Other => Key::Other,
        metadata::InstanceKey::Lit(value) => Key::Lit(value),
        metadata::InstanceKey::FVar(value, arity) => {
            Key::FVar(fln_core::expr::FVarId(value), arity)
        }
        metadata::InstanceKey::Const(value, arity) => Key::Const(value, arity),
        metadata::InstanceKey::Arrow => Key::Arrow,
        metadata::InstanceKey::Proj(value, field, arity) => Key::Proj(value, field, arity),
    }
}

fn activate(
    mut activation: ImportActivation,
    data: metadata::SourceExtensions,
    selected: &BTreeSet<Name>,
) -> ImportActivation {
    for row in data
        .classes
        .into_iter()
        .filter(|row| selected.contains(&row.name))
    {
        activation = activation
            .register_class(
                &row.name,
                &instances::imported::ClassParameters {
                    out_params: row.out_params,
                    out_level_params: row.out_level_params,
                },
            )
            .unwrap();
    }
    for row in data
        .instances
        .into_iter()
        .filter(|row| selected.contains(&row.declaration))
    {
        let info = activation.environment().find(&row.declaration).unwrap();
        assert_eq!(
            row.value,
            Expr::const_(
                row.declaration.clone(),
                info.constant_val()
                    .level_params
                    .iter()
                    .cloned()
                    .map(fln_core::level::Level::param)
                    .collect()
            )
        );
        activation = activation
            .register_instance(
                &row.declaration,
                &instances::imported::InstanceParameters {
                    priority: row.priority,
                    synth_order: row.synth_order,
                    scope: row.scope,
                    keys: row.keys.into_iter().map(key).collect(),
                },
            )
            .unwrap();
    }
    for row in data
        .defaults
        .into_iter()
        .filter(|row| selected.contains(&row.declaration))
    {
        activation = activation
            .register_default(&row.declaration, row.priority)
            .unwrap();
    }
    for row in data
        .aliases
        .into_iter()
        .filter(|row| selected.contains(&row.declaration))
    {
        activation = activation
            .register_alias(&row.alias, &row.declaration)
            .unwrap();
    }
    let protected: Vec<_> = data
        .protected
        .into_iter()
        .filter(|name| selected.contains(name))
        .collect();
    activation = activation.register_protected(&protected).unwrap();
    for row in data
        .reducibility
        .into_iter()
        .filter(|row| selected.contains(&row.declaration))
    {
        use fln_elab::reducibility::Reducibility;
        activation = activation
            .register_reducibility(
                &row.declaration,
                match row.status {
                    metadata::ReducibilityStatus::Reducible => Reducibility::Reducible,
                    metadata::ReducibilityStatus::Semireducible => Reducibility::Semireducible,
                    metadata::ReducibilityStatus::Irreducible => Reducibility::Irreducible,
                    metadata::ReducibilityStatus::ImplicitReducible => {
                        Reducibility::ImplicitReducible
                    }
                },
            )
            .unwrap();
    }
    for row in data
        .externs
        .into_iter()
        .filter(|row| selected.contains(&row.declaration))
    {
        use fln_elab::externs::ExternEntry;
        activation = activation
            .register_extern(
                &row.declaration,
                row.entries
                    .into_iter()
                    .map(|entry| match entry {
                        metadata::ExternEntry::Adhoc { backend } => ExternEntry::Adhoc { backend },
                        metadata::ExternEntry::Inline { backend, pattern } => {
                            ExternEntry::Inline { backend, pattern }
                        }
                        metadata::ExternEntry::Standard { backend, symbol } => {
                            ExternEntry::Standard { backend, symbol }
                        }
                        metadata::ExternEntry::Opaque => ExternEntry::Opaque,
                    })
                    .collect(),
            )
            .unwrap();
    }
    for row in data
        .implemented_by
        .into_iter()
        .filter(|row| selected.contains(&row.declaration))
    {
        activation = activation
            .register_implemented_by(&row.declaration, &row.implementation)
            .unwrap();
    }
    activation
}

pub(super) fn admitted(library: &Path) -> Engine {
    let start = Instant::now();
    let actual::SourceFixture {
        engine: raw,
        owners,
    } = actual::decoded_io_with_source_metadata(library);
    let discovery = checked(&raw, &format!("{DECLARATIONS}\n{DISCOVERY}"));
    let mut engine = base(library);
    let parts = artifacts(library, &name("Init.System.IO"));
    let order = artifact_order(&parts, &name("Init.System.IO"));
    let mut recursors = BTreeMap::<Vec<Name>, Vec<Name>>::new();
    for (label, _) in discovery.environment().constants() {
        if let Some(ConstantInfo::Rec(info)) = discovery.environment().find(label) {
            recursors
                .entry(info.all.clone())
                .or_default()
                .push(label.clone());
        }
    }
    let mut pending: BTreeSet<_> = [
        "IO.RealWorld.nonemptyType",
        "IO.RealWorld",
        "BaseIO",
        "EIO",
        "IO",
        "IO.Error",
        // Coercion expansion replaces this dictionary by FilePath.mk in the
        // checked discovery terms. Rechecking the original String paths still
        // needs its actual source instance registration, admitted below.
        "System.instCoeStringFilePath",
        // The native open contract also checks the genuine path projection.
        // It is not a dependency of the path constructor or opaque Handle.mk.
        "System.FilePath.toString",
    ]
    .map(name)
    .into_iter()
    .collect();
    for (label, _) in discovery.environment().constants() {
        if !raw.environment().contains(label) {
            pending.insert(label.clone());
        }
    }
    let mut walked = BTreeSet::new();
    let mut selected = BTreeSet::new();
    let mut journals = BTreeMap::new();
    loop {
        while let Some(label) = pending.pop_first() {
            if engine.environment().contains(&label) || !walked.insert(label.clone()) {
                continue;
            }
            let info = discovery
                .environment()
                .find(&label)
                .unwrap_or_else(|| panic!("missing actual/source dependency {label:?}"));
            pending.extend(dependencies(info, &recursors));
            if raw.environment().contains(&label) {
                selected.insert(label);
            }
            assert!(
                selected.len() <= 10_000,
                "bounded selected actual IO declaration slice"
            );
        }
        for module in &order {
            if !journals.contains_key(module)
                && owners[module].iter().any(|label| selected.contains(label))
            {
                journals.insert(module.clone(), read_metadata(&parts[module]));
            }
        }
        for data in journals.values() {
            for row in &data.implemented_by {
                if selected.contains(&row.declaration)
                    && !engine.environment().contains(&row.implementation)
                    && !walked.contains(&row.implementation)
                {
                    pending.insert(row.implementation.clone());
                }
            }
        }
        if pending.is_empty() {
            break;
        }
    }
    drop(discovery);
    drop(raw);
    eprintln!(
        "IO printing fixture: independently admitting {} selected actual declarations (not full IO module admission)",
        selected.len()
    );
    let check_limits = OleanCheckLimits::new(BYTES, Budget::for_stack_bytes(STACK));
    let mut admitted = BTreeSet::new();
    for module in &order {
        if !owners[module]
            .iter()
            .any(|label| selected.contains(label) && !engine.environment().contains(label))
        {
            continue;
        }
        let (public, server, private) = &parts[module];
        let mut decoded = fln::decode_olean_module_artifacts(
            public,
            server.as_deref().unwrap_or_default(),
            private.as_deref().unwrap_or_default(),
            check_limits.decode,
        )
        .unwrap();
        decoded.constants.retain(|info| {
            selected.contains(info.name()) && !engine.environment().contains(info.name())
        });
        if decoded.constants.is_empty() {
            continue;
        }
        assert!(matches!(decoded.independent, IndependentReading::Read(_)));
        let checked = engine
            .check_decoded_olean(decoded, &KVMap::new(), check_limits)
            .unwrap_or_else(|error| panic!("selected declarations from {module:?}: {error:?}"))
            .into_complete()
            .expect("both checkers admit the selected actual declarations");
        assert_eq!(checked.declarations.len(), checked.decoded.constants.len());
        for row in &checked.declarations {
            assert_eq!(row.checker.schema, "fln.checker-admission/1");
            assert!(admitted.insert(row.name.clone()));
        }
        engine = checked.engine;
    }
    assert_eq!(
        admitted, selected,
        "no raw constant enters the execution engine"
    );
    let mut activation = ImportActivation::new(engine.environment().clone());
    for module in &order {
        if let Some(data) = journals.remove(module) {
            activation = activate(activation, data, &selected);
        }
    }
    let engine = Engine::from_environment(activation.finish().unwrap());
    assert!(
        engine
            .environment()
            .contains(&name("IO.RealWorld.nonemptyType"))
    );
    assert!(engine.environment().contains(&name("IO.FS.Handle.mk")));
    assert!(
        engine
            .environment()
            .contains(&name("System.instCoeStringFilePath"))
    );
    assert!(
        engine
            .environment()
            .contains(&name("System.FilePath.toString"))
    );
    // The main argv formatter uses the public append from String.Defs. Its
    // actual declaration/proof closure and extern journal are retained by
    // ioSelectAppend's checked references, not supplied as comparison models.
    assert!(engine.environment().contains(&name("String.append")));
    assert!(!engine.environment().contains(&name("ioSelectAppend")));
    assert!(!engine.environment().contains(&name("ioSelectEffect")));
    eprintln!(
        "IO printing fixture: selected declarations and actual metadata ready in {:?}",
        start.elapsed()
    );
    engine
}
