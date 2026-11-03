//! Decode the published Reference artifacts as data for the extraction script.
//! This never runs IR, imports a declaration into an admission environment, or
//! links the Reference runtime. The Python driver verifies both input digests.

#![forbid(unsafe_code)]

use std::collections::BTreeMap;

use fln_core::expr::ExprNode;
use fln_env::constants::ConstantInfo;
use fln_olean::decl::DeclDecoder;
use fln_olean::ir::{
    IrAlt, IrArg, IrCtorInfo, IrDecl, IrDecodeLimits, IrExpr, IrModule, IrStmt, IrTerminal, IrType,
    decode_ir,
};
use fln_olean::region::{OleanView, WalkBudget};

fn ir_type(ty: &IrType) -> Result<&'static str, String> {
    match ty {
        IrType::Object => Ok("obj"),
        IrType::TObject => Ok("tobj"),
        _ => Err(format!("unexpected macro telescope type: {ty:?}")),
    }
}

fn function<'a>(module: &'a IrModule, name: &str) -> Result<&'a IrDecl, String> {
    let mut matches = module
        .decls
        .iter()
        .filter(|decl| decl.name().to_display_string() == name);
    let declaration = matches.next().ok_or_else(|| format!("missing {name}"))?;
    if matches.next().is_some() || !matches!(declaration, IrDecl::Function { .. }) {
        return Err(format!("expected one IR function: {name}"));
    }
    Ok(declaration)
}

fn collect_layout(
    layouts: &mut BTreeMap<String, IrCtorInfo>,
    info: &IrCtorInfo,
) -> Result<(), String> {
    let name = info.name.to_display_string();
    if !["Option.some", "Option.none", "Lean.Macro.Context.mk"].contains(&name.as_str()) {
        return Ok(());
    }
    if let Some(previous) = layouts.insert(name.clone(), info.clone())
        && previous != *info
    {
        return Err(format!("inconsistent compiled constructor: {name}"));
    }
    Ok(())
}

fn extract(ir: &[u8], olean: &[u8]) -> Result<(), String> {
    let view = OleanView::parse(ir).map_err(|error| error.to_string())?;
    let blocks = view
        .extension_payloads(WalkBudget::default(), 1 << 30)
        .map_err(|error| error.to_string())?;
    let module = decode_ir(
        &blocks,
        IrDecodeLimits {
            max_bytes: 1 << 30,
            ..IrDecodeLimits::default()
        },
    )
    .map_err(|error| error.to_string())?;
    let mut layouts = BTreeMap::new();
    for declaration in &module.decls {
        if let IrDecl::Function { body, .. } = declaration {
            for nested in body.bodies() {
                for statement in &nested.stmts {
                    if let IrStmt::VDecl {
                        expr: IrExpr::Ctor { info, .. } | IrExpr::Reuse { info, .. },
                        ..
                    } = statement
                    {
                        collect_layout(&mut layouts, info)?;
                    }
                }
                if let IrTerminal::Case { alts, .. } = nested.terminal.as_ref() {
                    for alternative in alts {
                        if let IrAlt::Ctor { info, .. } = alternative {
                            collect_layout(&mut layouts, info)?;
                        }
                    }
                }
            }
        }
    }
    let view = OleanView::parse(olean).map_err(|error| error.to_string())?;
    let declarations = DeclDecoder::new(&view, WalkBudget::default())
        .decode_module_constants()
        .map_err(|error| error.to_string())?;
    let mut fields = BTreeMap::new();
    let mut logical_fields = None;
    for declaration in &declarations {
        let name = declaration.name().to_display_string();
        if name == "Lean.Macro.Context.mk" {
            let ConstantInfo::Ctor(ctor) = declaration else {
                return Err("Macro.Context.mk is not a constructor".into());
            };
            if ctor.num_params != 0 {
                return Err("Macro.Context unexpectedly has parameters".into());
            }
            logical_fields = Some(u64::from(ctor.num_fields));
        }
        if ![
            "Lean.Macro.Context.currRecDepth",
            "Lean.Macro.Context.maxRecDepth",
            "Lean.Macro.Context.ref",
        ]
        .contains(&name.as_str())
        {
            continue;
        }
        let ConstantInfo::Defn(definition) = declaration else {
            return Err(format!("getter is not a definition: {name}"));
        };
        let ExprNode::Lam {
            binder_type, body, ..
        } = definition.value.node()
        else {
            return Err(format!("getter is not a lambda: {name}"));
        };
        if !matches!(binder_type.node(), ExprNode::Const { name, levels }
            if name.to_display_string() == "Lean.Macro.Context" && levels.is_empty())
        {
            return Err(format!("getter has a different argument type: {name}"));
        }
        let ExprNode::Proj {
            struct_name,
            idx,
            expr,
        } = body.node()
        else {
            return Err(format!("getter is not a projection: {name}"));
        };
        if struct_name.to_display_string() != "Lean.Macro.Context"
            || !matches!(expr.node(), ExprNode::BVar { idx: 0 })
            || fields.insert(name, *idx).is_some()
        {
            return Err("invalid or duplicate Macro.Context projection".into());
        }
    }
    let context = layouts
        .get("Lean.Macro.Context.mk")
        .ok_or("missing compiled Macro.Context constructor")?;
    // A structure with exactly the same number of logical fields and object
    // slots, and no scalar fields, preserves projection order. Check that
    // correspondence against the compiled constructor, not a remembered offset.
    if logical_fields != Some(context.size)
        || context.usize != 0
        || context.ssize != 0
        || fields.len() != 3
        || fields.values().any(|field| *field >= context.size)
    {
        return Err("Macro.Context logical/compiled layout mismatch".into());
    }
    // Independently join the semantic getter slots to their actual compiled
    // use: the depth comparison must project these two fields from the unique
    // borrowed Context argument of withIncRecDepth.
    let IrDecl::Function { params, body, .. } =
        function(&module, "Lean.Macro.withIncRecDepth._redArg")?
    else {
        unreachable!()
    };
    let contexts: Vec<_> = params
        .iter()
        .filter(|parameter| parameter.borrow && parameter.ty == IrType::Object)
        .collect();
    if contexts.len() != 1 {
        return Err("withIncRecDepth has no unique borrowed Context".into());
    }
    let projected: BTreeMap<_, _> = body
        .stmts
        .iter()
        .filter_map(|statement| match statement {
            IrStmt::VDecl {
                x,
                expr: IrExpr::Proj { i, x: context },
                ..
            } if *context == contexts[0].x => Some((*x, *i)),
            _ => None,
        })
        .collect();
    let depth = fields["Lean.Macro.Context.currRecDepth"];
    let maximum = fields["Lean.Macro.Context.maxRecDepth"];
    let reference = fields["Lean.Macro.Context.ref"];
    if !projected.values().any(|field| *field == reference)
        || !body.stmts.iter().any(|statement| {
            matches!(statement, IrStmt::VDecl {
                expr: IrExpr::Fap { function, args }, ..
            } if function.to_display_string() == "Nat.decEq"
                && matches!(args.as_slice(), [IrArg::Var(left), IrArg::Var(right)]
                    if projected.get(left) == Some(&depth)
                        && projected.get(right) == Some(&maximum)))
        })
    {
        return Err("compiled recursion-depth projections disagree with getters".into());
    }
    let IrDecl::Function { params, result, .. } = function(&module, "Lean.Macro.expandMacro?")?
    else {
        unreachable!()
    };
    let borrowed = params
        .iter()
        .map(|parameter| parameter.borrow.to_string())
        .collect::<Vec<_>>()
        .join(",");
    let types = params
        .iter()
        .map(|parameter| ir_type(&parameter.ty).map(|name| format!("\"{name}\"")))
        .collect::<Result<Vec<_>, _>>()?
        .join(",");
    println!(
        "{{\"borrowed\":[{borrowed}],\"parameters\":[{types}],\"result\":\"{}\",",
        ir_type(result)?
    );
    println!("\"depth\":{depth},\"max_depth\":{maximum},\"reference\":{reference},");
    for (index, name) in ["Option.some", "Option.none"].iter().enumerate() {
        let layout = layouts
            .get(*name)
            .ok_or_else(|| format!("missing {name}"))?;
        if layout.usize != 0 || layout.cidx > u64::from(u8::MAX) {
            return Err(format!("unsupported constructor layout: {name}"));
        }
        let comma = if index == 0 { "," } else { "" };
        println!(
            "\"{name}\":[{},{},{}]{comma}",
            layout.cidx, layout.size, layout.ssize
        );
    }
    println!("}}");
    Ok(())
}

fn main() -> Result<(), String> {
    let arguments: Vec<_> = std::env::args_os().skip(1).collect();
    if arguments.len() != 2 {
        return Err("usage: extract_macro_expansion_abi <Prelude.ir> <Prelude.olean>".into());
    }
    let ir = std::fs::read(&arguments[0]).map_err(|error| error.to_string())?;
    let olean = std::fs::read(&arguments[1]).map_err(|error| error.to_string())?;
    extract(&ir, &olean)
}
