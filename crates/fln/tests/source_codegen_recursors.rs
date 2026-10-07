//! The pin's code generator refuses a compiled declaration that applies a recursor
//! directly (bead `franken_lean-z8j.1.6.6`, `crates/fln-elab/src/source/codegen.rs`).
//!
//! Every verdict below is the pinned Reference's (`lean` v4.32.0, commit `8c9756b2`),
//! measured on the same program, headerless, on 2026-10-07. A refusal carries the pin's
//! message.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Mode,
    ProductSidecarRefusal, SourceCheckLimits, VmExit,
};

const T: &str = "inductive T where | a | b (x : T)\n";
const POS: &str = "structure Pos where\n  val : Nat\n  proof : True\n";
const V: &str = "inductive V (A : Type) : Nat -> Type where | nil : V A 0 | cons (n : Nat) (x : A) (t : V A n) : V A (n+1)\n";

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

/// An engine in the `frontier` mode, the only one that executes directly written recursors.
fn frontier() -> Engine {
    Engine::builder()
        .mode(Mode::Frontier)
        .build_with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

fn pin_message(recursor: &str) -> String {
    format!(
        "code generator does not support recursor `{recursor}` yet, consider using 'match ... with' and/or structural recursion"
    )
}

/// `None` when check-source accepts `source`, as the pin does; otherwise why not.
fn accepted(source: &str) -> Option<String> {
    let result = engine().check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    (!matches!(result, Ok(fln::Outcome::Complete(_))))
        .then(|| format!("the pin accepts this:\n{source}\n{:?}", result.err()))
}

/// `None` when check-source refuses `source` with the pin's message for `recursor` and
/// publishes nothing; otherwise why not.
fn refused(source: &str, recursor: &str) -> Option<String> {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    let outcome = e.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    assert_eq!(e.logical_root(&KVMap::new()), root);
    match outcome {
        Err(error) if error.to_string().contains(&pin_message(recursor)) => None,
        Err(error) => Some(format!("refused for another reason:\n{source}\n{error}")),
        Ok(_) => Some(format!("the pin refuses this:\n{source}")),
    }
}

/// [`refused`] at the execution door, which also runs `#eval`.
fn refused_at_run(source: &str, recursor: &str) -> Option<String> {
    let run_limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    match engine().execute_source_definitions(&[source.as_bytes()], &KVMap::new(), run_limits) {
        Err(error) if format!("{error:?}").contains("UnsupportedRecursor(Name(") => {
            let shown = format!("{error:?}");
            (!recursor
                .split('.')
                .all(|part| shown.contains(&format!("component: \"{part}\""))))
            .then(|| format!("refused naming another recursor:\n{source}\n{shown}"))
        }
        Err(error) => Some(format!("refused for another reason:\n{source}\n{error:?}")),
        Ok(_) => Some(format!("the pin refuses this:\n{source}")),
    }
}

fn all_hold(failures: impl IntoIterator<Item = Option<String>>) {
    let failures: Vec<String> = failures.into_iter().flatten().collect();
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

#[test]
fn a_compiled_declaration_that_applies_a_recursor_to_data_is_refused() {
    let count = "0 (fun _ ih => ih + 1) t";
    let failures = [
        format!("def f (t : T) : Nat := T.rec {count}\n"),
        format!("def f (t : T) : Nat := T.rec (motive := fun _ => Nat) {count}\n"),
        format!("def f (t : T) : Nat := @T.rec (fun _ => Nat) {count}\n"),
        // Unapplied, it is still compiled code.
        "def f : Nat -> (T -> Nat -> Nat) -> T -> Nat := @T.rec (fun _ => Nat)\n".to_owned(),
        format!("example (t : T) : Nat := T.rec (motive := fun _ => Nat) {count}\n"),
        format!(
            "instance : Inhabited (T -> Nat) := ⟨fun t => T.rec (motive := fun _ => Nat) {count}⟩\n"
        ),
        // A data field of a structure value is compiled; only its proof field is erased.
        format!("{POS}def f (t : T) : Pos := ⟨T.rec (motive := fun _ => Nat) {count}, True.intro⟩\n"),
        // The `induction` tactic applies the recursor itself.
        "def f (t : T) : Nat := by\n  induction t with\n  | a => exact 0\n  | b x ih => exact ih + 1\n"
            .to_owned(),
    ]
    .into_iter()
    .map(|body| refused(&format!("{T}{body}"), "T.rec"))
    .chain([
        refused(
            &format!(
                "{V}def len (v : V Nat 2) : Nat := V.rec (motive := fun _ _ => Nat) 0 (fun _ _ _ ih => ih + 1) v\n"
            ),
            "V.rec",
        ),
        // `#eval` compiles its term; check-source has no `#eval`, so the execution door.
        refused_at_run(
            &format!(
                "{T}#eval (T.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 1) (T.b T.a) : Nat)\n"
            ),
            "T.rec",
        ),
    ]);
    all_hold(failures);
}

#[test]
fn what_the_pin_compiles_or_erases_is_accepted() {
    let erased = [
        // Not compiled: a theorem, and a proof, a type or a proposition inside a definition.
        "theorem f (t : T) : True := T.rec (motive := fun _ => True) True.intro (fun _ ih => ih) t\n",
        "structure Pos where\n  val : Nat\n  proof : True\ndef f (t : T) : Pos := ⟨0, T.rec (motive := fun _ => True) True.intro (fun _ ih => ih) t⟩\n",
        "def F (t : T) : Type := T.rec (motive := fun _ => Type) Nat (fun _ ih => ih) t\n",
        "def P (t : T) : Prop := T.rec (motive := fun _ => Prop) True (fun _ ih => ih) t\n",
        "structure Refl where\n  val : Nat\n  proof : val = val\ndef f (t : T) : Refl := ⟨0, by induction t with\n  | a => rfl\n  | b x ih => rfl⟩\n",
        // `cases` and `match` use `casesOn`, which the pin compiles.
        "def f (t : T) : Nat := by\n  cases t with\n  | a => exact 0\n  | b x => exact 1\n",
        "def f : T -> Nat\n  | .a => 0\n  | .b x => f x + 1\n",
    ]
    .map(|body| accepted(&format!("{T}{body}")));
    // `Nat.rec` is compiled through its csimp replacement `Nat.recCompiled`, and the
    // pin lowers `Eq.rec`, `And.rec` and `False.rec` itself.
    let lowered = [
        "def f (n : Nat) : Nat := Nat.rec 0 (fun _ ih => ih + 1) n\n",
        "def f (n : Nat) : Nat := by\n  induction n with\n  | zero => exact 0\n  | succ k ih => exact ih + 1\n",
        &format!("{V}def f (a b : Nat) (h : a = b) (x : V Nat a) : V Nat b := h ▸ x\n"),
        "def f (h : False) : Nat := False.elim h\n",
        "def f (h : True ∧ True) : Nat := And.rec (fun _ _ => 3) h\n",
    ]
    .map(accepted);
    all_hold(erased.into_iter().chain(lowered));
}

/// The bead's required decision, route 1: executing a directly written recursor is the
/// `frontier` lane. The default engine refuses the program at both doors as the pin
/// does; a frontier engine runs it, and the run's product sidecar binds the frontier
/// tag, which a Sound consumer refuses (D-18), so the code cannot pass as default output.
#[test]
fn frontier_mode_runs_recursor_code_the_default_refuses_and_marks_its_product() {
    let source = format!(
        "{T}def count (t : T) : Nat := T.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 1) t\n#eval count (T.b (T.b T.a))\n"
    );
    all_hold([refused(&source, "T.rec")]);
    let run_limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let error = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), run_limits)
        .expect_err("the default execution door refuses as well");
    assert!(
        format!("{error:?}").contains("UnsupportedRecursor"),
        "{error:?}"
    );

    let run = frontier()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), run_limits)
        .unwrap_or_else(|error| panic!("the frontier engine runs it: {error:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(run.engine.mode(), Mode::Frontier);
    let last = run.executions.last().unwrap();
    let VmExit::Returned(value) = &last.exit else {
        panic!("native return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("2")
    );

    let image = b"exact toolchain image";
    let sidecar =
        fln::build_source_run_flbc_sidecar(&[source.as_bytes()], &KVMap::new(), image, &run)
            .unwrap();
    assert_eq!(sidecar.mode(), Mode::Frontier);
    assert!(matches!(
        sidecar.verify_product(&last.flbc_artifact, Mode::Sound),
        Err(ProductSidecarRefusal::Mode(_))
    ));
    sidecar
        .verify_product(&last.flbc_artifact, Mode::Frontier)
        .unwrap();
    let bytes = fln::encode_flbc_product_sidecar(&sidecar);
    assert!(fln::verify_source_run_flbc_sidecar(&bytes, &last.flbc_artifact, image).is_err());
}
