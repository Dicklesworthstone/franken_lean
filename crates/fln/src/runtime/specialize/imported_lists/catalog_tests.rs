//! Compiler representation probes over the decoded pinned declarations.
//! Decoding here does not grant admission authority or execute the fixture.
use super::*;

fn c(label: &str) -> Expr {
    Expr::const_(named(label), vec![])
}

#[test]
fn decoded_list_length_catalog_compiles_with_ground_addition_dictionaries() {
    let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(std::path::PathBuf::from) else {
        assert!(std::env::var_os("FLN_REQUIRE_REFERENCE").is_none());
        eprintln!("SKIP: pinned Reference lib/lean is absent");
        return;
    };
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let path = library.join("Init/Prelude.olean");
            let parts = [
                std::fs::read(&path).unwrap(),
                std::fs::read(path.with_extension("olean.server")).unwrap(),
                std::fs::read(path.with_extension("olean.private")).unwrap(),
            ];
            let decoded = decode_olean_module_artifacts(
                &parts[0],
                &parts[1],
                &parts[2],
                OleanDecodeLimits::new(256 * 1024 * 1024),
            )
            .unwrap();
            let environment = decoded
                .constants
                .into_iter()
                .fold(Environment::new(), |env, info| env.add_decl(info).unwrap());
            let dictionary = application(
                constant("instHAdd", vec![Level::zero()]),
                [c("Nat"), c("instAddNat")],
            );
            let named_projection = application(
                constant("HAdd.hAdd", vec![Level::zero(); 3]),
                [
                    c("Nat"),
                    c("Nat"),
                    c("Nat"),
                    dictionary.clone(),
                    nat::literal(20),
                    nat::literal(22),
                ],
            );
            let direct_projection = application(
                Expr::proj(named("HAdd"), 0, dictionary),
                [nat::literal(20), nat::literal(22)],
            );
            let nil = Expr::app(constant("List.nil", vec![Level::zero()]), c("Nat"));
            let list = application(
                constant("List.cons", vec![Level::zero()]),
                [c("Nat"), nat::literal(42), nil],
            );
            let length = application(
                constant("List.length", vec![Level::zero()]),
                [c("Nat"), list],
            );
            let mut failures = Vec::new();
            for (label, body) in [
                ("named addition projection", named_projection),
                ("raw addition projection", direct_projection),
                ("imported List.length", length),
            ] {
                let limits = IngressLimits::default();
                let mut preparation = Preparation::new(&environment, limits);
                let prepared = preparation
                    .expression_at_type(&body, Some(c("Nat")))
                    .unwrap();
                let mut catalog = crate::executable_dependencies(
                    &environment,
                    &prepared,
                    limits,
                    &mut preparation,
                )
                .unwrap();
                preparation.refine_expression_captures(&prepared).unwrap();
                let interfaces = preparation
                    .finalize_callables(&mut catalog.functions, &mut catalog.intrinsics)
                    .unwrap();
                let ingress = fln_comp::ingress::lower_closed_expr_at_result(
                    &prepared,
                    &catalog.scalar_constructors,
                    &catalog.intrinsics,
                    &preparation.constructors,
                    preparation.callables(&catalog.functions),
                    &interfaces,
                    Some(ValueType::Nat),
                    limits,
                );
                if let Err(error) = ingress {
                    eprintln!("{label} root: {prepared:?}");
                    for function in &catalog.functions {
                        eprintln!("{label} function {:?}: {:?}", function.name, function.body);
                    }
                    for (key, generated) in &preparation.specializations.instances {
                        eprintln!("{label} specialization {generated:?} <- {:?}", key.0);
                    }
                    failures.push(format!("{label}: {error:?}"));
                }
            }
            assert!(failures.is_empty(), "{failures:#?}");
        })
        .unwrap()
        .join()
        .unwrap();
}
