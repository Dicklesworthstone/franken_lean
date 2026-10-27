//! The `reuse-verified` import posture: D6's single named exception (bead `fln-uyuz`).
//!
//! The posture, its records, its keys and its re-proof live in
//! [`fln_admission::reuse`], beside the council whose admissions they record (bead
//! `fln-import-reuse-composes-4ngt`): every decision about whether and what to record,
//! and every re-proof, is that crate's code. `fln` keeps every public name here and
//! supplies two things the crate cannot: the metadata activation that runs after the
//! council ([`super::imported`]), whose effect reaches a record only through the
//! result root every reuse compares, and the record store, which is untrusted by
//! design.
use super::imported::{
    SourceImportHost, SourceOleanImport, SourceOleanImportError, SourceOleanImportLimits,
};
use crate::*;
pub use fln_admission::reuse::{
    CheckerIdentity, ImportAdmission, ImportClosureKey, ImportPosture, ImportPostureReport,
    ImportPostureRequest, ImportReuseRecord, ImportReuseRefusal, ImportReuseStore, RecordLookup,
    RecordWrite, ReuseVerified,
};

/// A reused closure, or why its record was refused
/// ([`fln_admission::reuse::ImportReuse`] over [`SourceOleanImport`]).
pub type ImportReuse = fln_admission::reuse::ImportReuse<SourceOleanImport>;

type ImportResult<T> = std::result::Result<T, SourceOleanImportError>;

impl Engine {
    /// [`Engine::import_olean_modules_for_source_with_cancel`] under an explicit posture:
    /// [`Admitted::import_olean_modules_with_posture`] on this engine, with `fln`'s
    /// metadata activation as its host.
    ///
    /// `Recheck` is exactly the council import and never touches a store.
    /// `ReuseVerified` looks the closure up by [`ImportClosureKey`]; a found record is
    /// re-proved (rebuilt by the D6 carve-out in `fln_admission::reuse`) and used only if
    /// every root matches; anything else runs the council and records its admission.
    pub fn import_olean_modules_with_posture(
        &self,
        modules: &[OleanModuleInput<'_>],
        roots: &[Name],
        options: &KVMap,
        limits: SourceOleanImportLimits,
        posture: ImportPostureRequest<'_>,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> ImportResult<Outcome<(SourceOleanImport, ImportPostureReport)>> {
        let host = match SourceImportHost::prepare(self, modules, roots, limits, cancellation)? {
            Outcome::Complete(host) => host,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        self.admitted().import_olean_modules_with_posture(
            &host,
            modules,
            roots,
            options,
            limits.council_limits(),
            posture,
            cancellation,
        )
    }
}

/// The checked set `record` re-proves for `modules`, for tests elsewhere in the crate
/// that need a second copy of a council-admitted closure without a second council.
#[cfg(test)]
impl Engine {
    pub(super) fn rebuild_for_test(
        &self,
        modules: &[OleanModuleInput<'_>],
        record: &ImportReuseRecord,
    ) -> Option<CheckedOleanSet> {
        match self.admitted().rebuild_reused_olean_set(
            modules,
            &KVMap::new(),
            super::imported::tests::limits(1).check,
            OleanFrontierJobs::SERIAL,
            record,
            None,
        ) {
            Outcome::Complete(Ok(checked)) => {
                Some(checked.map_engine(|engine| self.with_admitted(engine)))
            }
            _ => None,
        }
    }

    /// [`Admitted::compose_recorded_modules_with`] on this engine, for the scheduler
    /// tests: their councils run real admissions on the `Engine` a module's context
    /// converts to, exactly as before the scheduler moved.
    fn compose_recorded_modules_with(
        &self,
        modules: &[OleanModuleInput<'_>],
        options: &KVMap,
        limits: SourceOleanImportLimits,
        reuse: &ReuseVerified<'_>,
        cancellation: Option<&dyn CancellationProbe>,
        council: &(
             impl Fn(&Name, &Engine, DecodedOlean) -> Result<Outcome<CheckedOlean>, OleanCheckError>
             + Sync
         ),
    ) -> Result<Outcome<Option<ComposedModules<Engine>>>, OleanCheckError> {
        self.admitted()
            .compose_recorded_modules_with(
                modules,
                options,
                limits.council_limits(),
                reuse,
                cancellation,
                &|name: &Name, context: &Admitted, decoded: DecodedOlean| {
                    council(name, &self.with_admitted(context.clone()), decoded).map(|outcome| {
                        outcome
                            .map_complete(|checked| checked.map_engine(|engine| engine.admitted()))
                    })
                },
            )
            .map(|outcome| {
                outcome.map_complete(|composed| {
                    composed
                        .map(|composed| composed.map_engine(|engine| self.with_admitted(engine)))
                })
            })
    }

    /// [`Admitted::reuse_recorded_closure`] on this engine, with `fln`'s activation.
    #[allow(clippy::too_many_arguments)]
    fn reuse_recorded_closure(
        &self,
        modules: &[OleanModuleInput<'_>],
        roots: &[Name],
        options: &KVMap,
        limits: SourceOleanImportLimits,
        key: ImportClosureKey,
        checker: CheckerIdentity,
        record: &ImportReuseRecord,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> ImportResult<Outcome<ImportReuse>> {
        self.admitted().reuse_recorded_closure(
            &SourceImportHost::new(self, limits),
            modules,
            roots,
            options,
            limits.council_limits(),
            key,
            checker,
            record,
            cancellation,
        )
    }
}

// What the tests below and in `composed_tests` reach of the moved posture.
#[cfg(test)]
use fln_admission::reuse::{
    ComposedModules, MODULE_RECORD_PREFIX, ModuleReuseRecord, RECORD_SCHEMA, RecordedModule,
    module_reuse_key, seal,
};
#[cfg(test)]
use fln_hash::domain::Domain;
#[cfg(test)]
use std::collections::BTreeMap;

#[cfg(test)]
mod composed_tests;

#[cfg(test)]
mod tests {
    use super::super::imported::tests::{closure, inputs, limits, n, on_import_stack, pinned_lib};
    use super::*;
    use std::sync::Mutex;

    /// Records held in memory under the same byte contract as any other store.
    #[derive(Default)]
    pub(super) struct Memory(pub(super) Mutex<BTreeMap<ImportClosureKey, Vec<u8>>>);
    impl ImportReuseStore for Memory {
        fn load(&self, key: ImportClosureKey) -> std::result::Result<Option<Vec<u8>>, String> {
            Ok(self.0.lock().expect("store lock").get(&key).cloned())
        }
        fn save(&self, key: ImportClosureKey, bytes: &[u8]) -> std::result::Result<(), String> {
            self.0
                .lock()
                .expect("store lock")
                .insert(key, bytes.to_vec());
            Ok(())
        }
    }

    pub(super) fn identity(name: &str) -> CheckerIdentity {
        CheckerIdentity::of_executable(name.as_bytes())
    }

    pub(super) fn import_with(
        modules: &[OleanModuleInput<'_>],
        roots: &[Name],
        posture: ImportPostureRequest<'_>,
    ) -> (SourceOleanImport, ImportPostureReport) {
        Engine::from_environment(Environment::new())
            .import_olean_modules_with_posture(
                modules,
                roots,
                &KVMap::new(),
                limits(1),
                posture,
                None,
            )
            .expect("the pinned closure imports")
            .into_complete()
            .expect("the pinned closure imports completely")
    }

    pub(super) fn reuse<'a>(
        checker: CheckerIdentity,
        store: &'a dyn ImportReuseStore,
    ) -> ImportPostureRequest<'a> {
        ImportPostureRequest::ReuseVerified(ReuseVerified { checker, store })
    }

    /// The decoded declarations of one module's parts.
    fn declarations(
        name: &Name,
        parts: &[Vec<u8>; 3],
    ) -> std::result::Result<Vec<ConstantInfo>, OleanCheckError> {
        let [exported, server, private] = parts;
        crate::decode_olean_module_input(
            &OleanModuleInput {
                name,
                artifact: exported,
                server_artifact: (!server.is_empty()).then_some(server.as_slice()),
                private_artifact: (!private.is_empty()).then_some(private.as_slice()),
            },
            limits(1).check,
        )
        .map(|decoded| decoded.constants)
    }

    /// Change the last byte of the only occurrence of `word` in part `part`.
    fn flip(parts: &mut [Vec<u8>; 3], part: usize, word: &[u8]) {
        let bytes = &mut parts[part];
        let hits: Vec<usize> = bytes
            .windows(word.len())
            .enumerate()
            .filter(|(_, window)| *window == word)
            .map(|(at, _)| at)
            .collect();
        assert_eq!(hits.len(), 1, "{word:?} must occur once in part {part}");
        let last = hits[0] + word.len() - 1;
        bytes[last] = if bytes[last] == b'z' { b'y' } else { b'z' };
    }

    /// Everything the council's checked set and the reused one must share. The fields
    /// that differ are stated, not skipped: the council retains its independent-checker
    /// projection of every admitted declaration, the rebuild retains none; and the
    /// council's decode carries the checker's own reading of each artifact, which the
    /// rebuild never consults and so never makes.
    fn assert_same_closure(council: &SourceOleanImport, reused: &SourceOleanImport) {
        let (left, right) = (&council.checked, &reused.checked);
        assert!(
            left.engine.environment == right.engine.environment,
            "environments"
        );
        assert_eq!(left.engine.imported_modules, right.engine.imported_modules);
        assert!(left.engine.imported_environment == right.engine.imported_environment);
        assert_eq!(
            left.engine.imported_module_dependencies,
            right.engine.imported_module_dependencies
        );
        assert_eq!(left.engine.options, right.engine.options);
        assert_eq!(left.engine.epoch, right.engine.epoch);
        assert_eq!(left.base_logical_root, right.base_logical_root);
        assert_eq!(left.result_logical_root, right.result_logical_root);
        assert_eq!(left.modules.len(), right.modules.len());
        for (left, right) in left.modules.iter().zip(&right.modules) {
            assert_eq!(left.name, right.name);
            assert!(
                matches!(left.decoded.independent, crate::IndependentReading::Read(_)),
                "the council read every artifact itself"
            );
            assert!(
                matches!(
                    right.decoded.independent,
                    crate::IndependentReading::Unread(_)
                ),
                "the rebuild makes no checker reading"
            );
            let mut council_decode = left.decoded.clone();
            council_decode.independent = right.decoded.independent.clone();
            assert!(council_decode == right.decoded, "decoded artifacts");
            assert_eq!(left.base_logical_root, right.base_logical_root);
            assert_eq!(left.result_logical_root, right.result_logical_root);
            assert_eq!(left.declarations, right.declarations, "checker rows");
        }
        assert!(left.engine.checker_environment.is_some());
        assert!(right.engine.checker_environment.is_none());
        assert!(
            council.engine.environment == reused.engine.environment,
            "metadata engines"
        );
        assert_eq!(council.result_logical_root, reused.result_logical_root);
        assert_eq!(council.modules, reused.modules, "metadata reports");
    }

    /// The positive half: a multi-module closure admitted once is rebuilt from its
    /// record into the same closure, says so, and checks source to the same roots.
    #[test]
    fn a_recorded_closure_is_rebuilt_into_the_council_closure_and_says_so() {
        let Some(lib) = pinned_lib() else {
            eprintln!("SKIP: pinned Reference lib/lean absent");
            return;
        };
        let roots = ["Init.Data.Cast", "Init.Data.Option.Coe", "Init.Data.Zero"];
        let closure = closure(&lib, &roots);
        let modules = inputs(&closure);
        let roots: Vec<Name> = roots.iter().map(|root| n(root)).collect();
        on_import_stack(|| {
            let store = Memory::default();
            let checker = identity("checker A");
            let (council, first) = import_with(&modules, &roots, reuse(checker, &store));
            assert_eq!(first.posture, ImportPosture::ReuseVerified);
            assert_eq!(first.admission, ImportAdmission::Council);
            assert_eq!(first.record, RecordLookup::Absent);
            assert_eq!(first.record_write, RecordWrite::Stored);
            let (reused, second) = import_with(&modules, &roots, reuse(checker, &store));
            assert_eq!(second.admission, ImportAdmission::Reused);
            assert_eq!(second.record, RecordLookup::Hit);
            assert_eq!(second.record_write, RecordWrite::NotAttempted);
            assert_eq!(first.key, second.key);
            assert_same_closure(&council, &reused);

            let main = n("Main");
            let source =
                b"prelude\nimport Init.Data.Cast\ntheorem keep (P : Prop) (h : P) : P := h\n";
            let check = |receipt: &SourceOleanImport| {
                receipt
                    .check_source_modules(
                        &[SourceModuleInput {
                            name: &main,
                            source,
                        }],
                        &main,
                        &KVMap::new(),
                        super::super::SourceModuleCheckLimits::new(SourceCheckLimits::new(
                            EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
                        )),
                        None,
                    )
                    .expect("source checks against the receipt")
                    .into_complete()
                    .expect("source checks completely")
            };
            let (council, reused) = (check(&council), check(&reused));
            assert_eq!(council.checked.theorems, 1);
            assert_eq!(council.checked.theorems, reused.checked.theorems);
            assert_eq!(
                council.checked.base_logical_root,
                reused.checked.base_logical_root
            );
            assert_eq!(
                council.checked.result_logical_root,
                reused.checked.result_logical_root
            );
            assert!(council.checked.engine.environment == reused.checked.engine.environment);
        });
    }

    /// `recheck` is the council import and says so. A `Recheck` request carries no
    /// store, so there is nothing it could consult; the report must not claim one.
    #[test]
    fn recheck_is_the_council_import_and_reports_no_record() {
        let Some(lib) = pinned_lib() else {
            eprintln!("SKIP: pinned Reference lib/lean absent");
            return;
        };
        let closure = closure(&lib, &["Init.Prelude"]);
        let modules = inputs(&closure);
        let roots = [n("Init.Prelude")];
        on_import_stack(|| {
            let (_, report) = import_with(&modules, &roots, ImportPostureRequest::Recheck);
            assert_eq!(report.posture, ImportPosture::Recheck);
            assert_eq!(report.admission, ImportAdmission::Council);
            assert_eq!(report.record, RecordLookup::NotConsulted);
            assert_eq!(report.record_write, RecordWrite::NotAttempted);
            assert_eq!(report.key, None);
        });
    }

    /// The planted negatives, on the real Prelude.
    ///
    /// 1. One changed byte in a docstring (the `.server` part): the declarations are
    ///    unchanged, so only the KEY can catch it, and it does: the record is not found
    ///    and the council admits again.
    /// 2. A record of another checker identity, planted under this identity's key, is
    ///    refused as such and the council admits again.
    /// 3. A record with one wrong root is refused at that root, while the genuine record
    ///    over the same bytes still re-proves.
    #[test]
    fn changed_bytes_other_checkers_and_forged_records_are_refused() {
        let Some(lib) = pinned_lib() else {
            eprintln!("SKIP: pinned Reference lib/lean absent");
            return;
        };
        let prelude = n("Init.Prelude");
        let roots = [prelude.clone()];
        let original = closure(&lib, &["Init.Prelude"]);
        assert_eq!(original.len(), 1);
        let unchanged = declarations(&prelude, &original[0].1).expect("Prelude decodes");

        let mut docstring = original.clone();
        flip(&mut docstring[0].1, 1, b"The identity function");
        assert!(
            declarations(&prelude, &docstring[0].1).expect("still decodes") == unchanged,
            "the docstring flip must leave every declaration as it was"
        );

        on_import_stack(|| {
            let store = Memory::default();
            let checker = identity("checker A");
            let modules = inputs(&original);
            let (_, stored) = import_with(&modules, &roots, reuse(checker, &store));
            assert_eq!(stored.record_write, RecordWrite::Stored);
            let key = stored.key.expect("reuse-verified computes a key");
            let record_bytes = store.load(key).unwrap().expect("the record was stored");
            let record = ImportReuseRecord::parse(&record_bytes).expect("the record parses");

            // 1. A docstring byte: another key, so the council admits again.
            let (_, changed) = import_with(&inputs(&docstring), &roots, reuse(checker, &store));
            assert_ne!(changed.key, Some(key));
            assert_eq!(changed.record, RecordLookup::Absent);
            assert_eq!(changed.admission, ImportAdmission::Council);

            // 2. Another checker identity's record under this identity's key.
            let other = identity("checker B");
            let other_key = ImportClosureKey::compute(&modules, &roots, &KVMap::new(), other);
            assert_ne!(other_key, key, "the identity is part of the key");
            store.save(other_key, &record_bytes).unwrap();
            let (_, refused) = import_with(&modules, &roots, reuse(other, &store));
            assert_eq!(
                refused.record,
                RecordLookup::Refused(ImportReuseRefusal::CheckerIdentity)
            );
            assert_eq!(refused.admission, ImportAdmission::Council);
            assert_eq!(refused.record_write, RecordWrite::Stored);

            let base = Engine::from_environment(Environment::new());
            // 3. The genuine bytes with one wrong root: refused at that root.
            let wrong = record
                .clone()
                .with_declaration_root(fln_hash::domain::hash(Domain::CacheKey, b"planted"));
            let verdict = base
                .reuse_recorded_closure(
                    &modules,
                    &roots,
                    &KVMap::new(),
                    limits(1),
                    key,
                    checker,
                    &wrong,
                    None,
                )
                .expect("a refusal is not an import error")
                .into_complete()
                .expect("the re-proof answers");
            assert!(
                matches!(
                    verdict,
                    ImportReuse::Refused(ImportReuseRefusal::Root {
                        at: "declarations",
                        module: None
                    })
                ),
                "{verdict:?}"
            );
            // The genuine record still re-proves: the refusals above are about the
            // planted differences, not about a rebuild that never succeeds.
            assert!(matches!(
                base.reuse_recorded_closure(
                    &modules,
                    &roots,
                    &KVMap::new(),
                    limits(1),
                    key,
                    checker,
                    &record,
                    None,
                )
                .expect("the genuine record re-proves")
                .into_complete()
                .expect("the re-proof answers"),
                ImportReuse::Reused(_)
            ));
        });
    }

    /// One `.olean` for module `Lib`, written by this toolchain from `source`.
    fn built_lib(source: &str) -> Vec<u8> {
        let lib = n("Lib");
        let built = Engine::builder()
            .build_empty()
            .compile_source_modules(
                &[SourceModuleInput {
                    name: &lib,
                    source: source.as_bytes(),
                }],
                &lib,
                &KVMap::new(),
                super::super::SourceModuleCheckLimits::new(SourceCheckLimits::new(
                    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
                )),
                OleanWriteBudget::default(),
            )
            .expect("Lib builds")
            .into_complete()
            .expect("Lib builds completely");
        assert_eq!(built.artifacts.len(), 1);
        built.artifacts[0].bytes.clone()
    }

    /// The key is not the only guard. A record whose key is forged onto another closure
    /// (here: the same module name, a different declaration, both genuine artifacts that
    /// decode) is refused by the ROOTS at that module, through the store and the posture
    /// door, and the council admits the real closure instead.
    #[test]
    fn a_record_forged_onto_other_declarations_is_refused_by_the_roots() {
        let lib = n("Lib");
        let roots = [lib.clone()];
        let first = built_lib("prelude\ndef Lib.v.{u} {A : Sort u} (x : A) : A := x\n");
        let other = built_lib("prelude\ndef Lib.w.{u} {A : Sort u} (x : A) : A := x\n");
        assert_ne!(first, other);
        let input = |artifact: &'static [u8]| -> Vec<OleanModuleInput<'static>> {
            let name: &'static Name = Box::leak(Box::new(n("Lib")));
            vec![OleanModuleInput {
                name,
                artifact,
                server_artifact: None,
                private_artifact: None,
            }]
        };
        let first: &'static [u8] = Box::leak(first.into_boxed_slice());
        let other: &'static [u8] = Box::leak(other.into_boxed_slice());
        on_import_stack(|| {
            let store = Memory::default();
            let checker = identity("checker A");
            let (_, stored) = import_with(&input(first), &roots, reuse(checker, &store));
            assert_eq!(stored.record_write, RecordWrite::Stored);
            let record = ImportReuseRecord::parse(
                &store
                    .load(stored.key.expect("a key"))
                    .unwrap()
                    .expect("the record was stored"),
            )
            .expect("the record parses");

            let other_key =
                ImportClosureKey::compute(&input(other), &roots, &KVMap::new(), checker);
            store
                .save(other_key, &record.clone().with_key(other_key).to_bytes())
                .unwrap();
            let (admitted, refused) = import_with(&input(other), &roots, reuse(checker, &store));
            assert_eq!(
                refused.record,
                RecordLookup::Refused(ImportReuseRefusal::Root {
                    at: "module-result",
                    module: Some(lib.clone()),
                })
            );
            assert_eq!(refused.admission, ImportAdmission::Council);
            assert!(admitted.engine.environment.contains(&n("Lib.w")));
            assert!(!admitted.engine.environment.contains(&n("Lib.v")));
        });
    }

    /// The record format is strict and never panics: a round trip is exact, and every
    /// truncation and every single-byte change of a real record is refused.
    #[test]
    fn records_round_trip_and_every_damaged_record_is_refused() {
        let record = ImportReuseRecord {
            key: fln_hash::domain::hash(Domain::CacheKey, b"key"),
            checker: fln_hash::domain::hash(Domain::CacheKey, b"checker"),
            base_root: fln_hash::domain::hash(Domain::CacheKey, b"base"),
            declaration_root: fln_hash::domain::hash(Domain::CacheKey, b"declarations"),
            result_root: fln_hash::domain::hash(Domain::CacheKey, b"result"),
            modules: vec![
                RecordedModule {
                    name: n("A.B").to_canonical_bytes(),
                    base_root: fln_hash::domain::hash(Domain::CacheKey, b"a0"),
                    result_root: fln_hash::domain::hash(Domain::CacheKey, b"a1"),
                    rows: vec![
                        (
                            1,
                            CheckerAgreement {
                                schema: "fln-checker/v1",
                                ground: CheckerAdmissionGround::BodyCheckedAgainstDeclaredType,
                            },
                        ),
                        (
                            0,
                            CheckerAgreement {
                                schema: fln_checker::admit::ADMISSION_SCHEMA,
                                ground: CheckerAdmissionGround::AxiomPreamble,
                            },
                        ),
                        (
                            12,
                            CheckerAgreement {
                                schema: "fln-checker/v1",
                                ground: CheckerAdmissionGround::PartialQuarantine,
                            },
                        ),
                    ],
                },
                RecordedModule {
                    name: n("C").to_canonical_bytes(),
                    base_root: fln_hash::domain::hash(Domain::CacheKey, b"a1"),
                    result_root: fln_hash::domain::hash(Domain::CacheKey, b"a1"),
                    rows: Vec::new(),
                },
            ],
        };
        let bytes = record.to_bytes();
        assert_eq!(ImportReuseRecord::parse(&bytes), Ok(record));
        for end in 0..bytes.len() {
            assert!(
                ImportReuseRecord::parse(&bytes[..end]).is_err(),
                "prefix {end}"
            );
        }
        for at in 0..bytes.len() {
            let mut damaged = bytes.clone();
            damaged[at] ^= 0x01;
            assert!(ImportReuseRecord::parse(&damaged).is_err(), "byte {at}");
        }
        assert!(ImportReuseRecord::parse(b"").is_err());
        assert!(ImportReuseRecord::parse(&[0xff; 64]).is_err());

        // A pre-Merkle record differs only in its schema line and is correctly sealed,
        // so it is refused for its format, not for damage.
        let text = String::from_utf8(bytes).expect("records are UTF-8");
        let body_end = text
            .trim_end_matches('\n')
            .rfind('\n')
            .expect("a seal line")
            + 1;
        let old_body = text[..body_end].replacen(RECORD_SCHEMA, "fln.import-reuse-record/1", 1);
        assert_ne!(old_body, text[..body_end]);
        let old = format!("{old_body}seal {}\n", seal(old_body.as_bytes()).to_hex());
        assert_eq!(
            ImportReuseRecord::parse(old.as_bytes()),
            Err(ImportReuseRefusal::Malformed("unknown schema"))
        );
    }
}
