//! Bounded native stdout with ordinary logical Stream callbacks.
//!
//! Native Stream and packed IO.Result values never become admitted data by
//! relabeling. The exact getter returns a private carrier; its putStr callback
//! returns a private, checked transport record. Golem wrappers reconstruct
//! checked Unit, IO.Error and EST.Out layouts, retaining the incoming world.
//! The other stream callbacks remain the VM's explicit native-call refusals.

use super::*;
use crate::source_intrinsics::io::stdout::{self, ErrorFields};
use fln_comp::fir::EffectClass;
use fln_comp::flbc::ResultOwnership;
use fln_comp::ingress::ConstructorBinding;
use std::collections::BTreeMap;

const RAW_STREAM: &str = "_fln_runtime_stdout_stream";
const TRANSPORT: &str = "_fln_runtime_stdout_result";
const GETTER: &str = "_fln_runtime_stdout_get";

#[derive(Default)]
pub(super) struct Store {
    next_adapter: u64,
    bindings: BTreeMap<Name, (IntrinsicBinding, Expr)>,
    layout: Option<Layout>,
}

#[derive(Clone)]
struct Layout {
    stream: records::Shape,
    get_result: records::Shape,
    io_result: records::Shape,
    error: records::Shape,
    option: records::Shape,
    unit_constructor: Name,
    word_constructor: Name,
    bits_constructor: Name,
    fin_constructor: Name,
    raw_stream: Expr,
    transport: Expr,
    world: Expr,
}

fn c(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}

fn apply(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

fn b(index: u32) -> Result<Expr, IngressError> {
    Expr::bvar(index).map_err(|_| unsupported("stdout adapter binder scope"))
}

fn function(domains: &[Expr], result: Expr) -> Expr {
    domains.iter().rev().fold(result, |body, domain| {
        Expr::forall_e(Name::anonymous(), domain.clone(), body, BinderInfo::Default)
    })
}

fn choose(type_: Expr, condition: Expr, no: Expr, yes: Expr) -> Expr {
    // All adapter result types are closed. The normal Boolean recursor path
    // creates lazy branches, so only the selected error layout is allocated.
    apply(
        Expr::const_(name("Bool.rec"), vec![Level::one()]),
        [
            Expr::lam(Name::anonymous(), c("Bool"), type_, BinderInfo::Default),
            no,
            yes,
            condition,
        ],
    )
}

fn transport_field(index: u64) -> Result<Expr, IngressError> {
    Ok(Expr::proj(name(TRANSPORT), index, b(0)?))
}

impl Preparation<'_> {
    pub(crate) fn stdout_intrinsic_binding(&self, name: &Name) -> Option<IntrinsicBinding> {
        self.stdout
            .bindings
            .get(name)
            .map(|(binding, _)| binding.clone())
    }

    pub(super) fn stdout_intrinsic_type(&self, name: &Name) -> Option<Expr> {
        self.stdout
            .bindings
            .get(name)
            .map(|(_, type_)| type_.clone())
    }

    fn stdout_adapter_name(&mut self) -> Result<Name, IngressError> {
        self.tick()?;
        let serial = self.stdout.next_adapter;
        self.stdout.next_adapter = serial
            .checked_add(1)
            .ok_or_else(|| unsupported("stdout adapter identity"))?;
        let name = Name::num(name("_fln_runtime_stdout_scope"), serial);
        if self.environment.contains(&name) {
            return Err(unsupported("stdout adapter name collision"));
        }
        Ok(name)
    }

    fn stdout_shape(&mut self, source: Expr) -> Result<records::Shape, IngressError> {
        let source = self.erase_runtime_type(&source)?;
        if self.value_type(&source)? != Some(ValueType::Constructor) {
            return Err(unsupported("stdout requires a checked logical data layout"));
        }
        self.record_shape(&source)?
            .ok_or_else(|| unsupported("stdout checked data layout"))
    }

    fn stdout_single_constructor(
        &mut self,
        source: Expr,
        fields: usize,
    ) -> Result<records::ShapeConstructor, IngressError> {
        let shape = self.stdout_shape(source)?;
        let [constructor] = shape.constructors.as_slice() else {
            return Err(unsupported("stdout logical structure constructor"));
        };
        if constructor.tag != 0 || constructor.fields.len() != fields {
            return Err(unsupported("stdout logical structure field count"));
        }
        Ok(constructor.clone())
    }

    /// These types never enter the environment or either checker. The native
    /// producer/consumer contract is their only authority, and private names
    /// are checked before any projection or callable interface is registered.
    fn stdout_carrier(&mut self, label: &str, fields: Vec<Expr>) -> Result<Expr, IngressError> {
        let family = name(label);
        let constructor = Name::str(family.clone(), "mk");
        let source = Expr::const_(family.clone(), Vec::new());
        if self.environment.contains(&family) || self.environment.contains(&constructor) {
            return Err(unsupported("stdout private carrier name collision"));
        }
        if self.data_shapes.contains_key(&source) {
            return Ok(source);
        }
        let mut values = Vec::new();
        for field in &fields {
            self.tick()?;
            let value = self
                .value_type(field)?
                .ok_or_else(|| unsupported("stdout private field representation"))?;
            reserve(&mut values, self.limits.max_context_depth)?;
            values.push(value);
        }
        reserve(&mut self.constructors, self.limits.fir.max_constructors)?;
        self.constructors.push(ConstructorBinding {
            name: constructor.clone(),
            projection_structure: Some(family.clone()),
            universe_arity: 0,
            tag: 0,
            fields: values,
            static_scalar_bytes: Vec::new(),
        });
        self.remember_constructor_type(constructor.clone(), function(&fields, source.clone()))?;
        self.value_types
            .records
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: self.value_types.records.len().saturating_add(1),
            })?;
        self.value_types.records.insert(source.clone());
        self.data_shapes
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: self.data_shapes.len().saturating_add(1),
            })?;
        self.data_shapes.insert(
            source.clone(),
            records::Shape {
                source: source.clone(),
                name: family,
                recursive: false,
                constructors: vec![records::ShapeConstructor {
                    original: constructor.clone(),
                    name: constructor,
                    tag: 0,
                    type_fields: vec![false; fields.len()],
                    fields,
                }],
            },
        );
        Ok(source)
    }

    fn stdout_bind_getter(&mut self, result_type: Expr) -> Result<(), IngressError> {
        let private = name(GETTER);
        if self.environment.contains(&private) {
            return Err(unsupported("stdout private getter name collision"));
        }
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.id == "extern:IO.getStdout")
            .ok_or_else(|| unsupported("stdout generated getter row"))?;
        if row.name != "IO.getStdout"
            || row.kind != "opaque"
            || row.levels != 0
            || row.arity != 0
            || row.effect != "io"
            || row.ownership != "rule(borrowed-args,owned-result)"
        {
            return Err(unsupported("stdout generated getter contract"));
        }
        self.stdout.bindings.insert(
            private.clone(),
            (
                IntrinsicBinding {
                    name: private,
                    universe_arity: 0,
                    row: row.id.to_owned(),
                    arguments: Vec::new(),
                    argument_ownership: Vec::new(),
                    result: ValueType::Constructor,
                    result_ownership: ResultOwnership::Owned,
                    effect: EffectClass::Io,
                },
                result_type,
            ),
        );
        Ok(())
    }

    fn stdout_layout(&mut self) -> Result<Option<Layout>, IngressError> {
        if let Some(layout) = &self.stdout.layout {
            return Ok(Some(layout.clone()));
        }
        if !stdout::contract_matches(
            self.environment,
            &mut self.externs,
            &mut self.visited,
            self.limits,
        )? {
            return Ok(None);
        }
        let Some(world) = self.st_evaluation_world()? else {
            return Ok(None);
        };
        let stream = self.stdout_shape(c("IO.FS.Stream"))?;
        if stream.constructors.len() != 1 || stream.constructors[0].fields.len() != 6 {
            return Err(unsupported("stdout logical Stream layout"));
        }
        let get_result =
            self.stdout_shape(apply(c("ST.Out"), [c("IO.RealWorld"), c("IO.FS.Stream")]))?;
        let io_result = self.stdout_shape(apply(
            c("EST.Out"),
            [c("IO.Error"), c("IO.RealWorld"), c("Unit")],
        ))?;
        if get_result.constructors.len() != 1
            || get_result.constructors[0].fields.len() != 2
            || io_result.constructors.len() != 2
            || io_result
                .constructors
                .iter()
                .any(|constructor| constructor.fields.len() != 2)
        {
            return Err(unsupported("stdout checked world-result layout"));
        }
        let error = self.stdout_shape(c("IO.Error"))?;
        if error.constructors.len() != stdout::error_cases().len() {
            return Err(unsupported("stdout logical error variants"));
        }
        let option = self.stdout_shape(Expr::app(
            Expr::const_(name("Option"), vec![Level::zero()]),
            c("String"),
        ))?;
        if option.constructors.len() != 2
            || !option.constructors[0].fields.is_empty()
            || option.constructors[1].fields != [c("String")]
        {
            return Err(unsupported("stdout optional filename layout"));
        }
        let unit = self.stdout_single_constructor(c("Unit"), 0)?;
        let word = self.stdout_single_constructor(c("UInt32"), 1)?;
        let bits = self.stdout_single_constructor(word.fields[0].clone(), 1)?;
        let fin = self.stdout_single_constructor(bits.fields[0].clone(), 2)?;
        if fin.fields != [c("Nat"), proofs::erased_type()] {
            return Err(unsupported("stdout erased finite-word layout"));
        }
        let transport = self.stdout_carrier(
            TRANSPORT,
            vec![
                c("Bool"),
                c("Nat"),
                c("Nat"),
                c("Bool"),
                c("String"),
                c("String"),
            ],
        )?;
        let mut native_fields = stream.constructors[0].fields.clone();
        native_fields[4] = function(&[c("String"), world.clone()], transport.clone());
        let raw_stream = self.stdout_carrier(RAW_STREAM, native_fields)?;
        self.stdout_bind_getter(raw_stream.clone())?;
        let layout = Layout {
            stream,
            get_result,
            io_result,
            error,
            option,
            unit_constructor: unit.name,
            word_constructor: word.name,
            bits_constructor: bits.name,
            fin_constructor: fin.name,
            raw_stream,
            transport,
            world,
        };
        self.stdout.layout = Some(layout.clone());
        Ok(Some(layout))
    }

    /// Rebuild UInt32's admitted object layout. Native packed scalar storage
    /// is deliberately absent from the public value; the Fin proof retains
    /// exactly the ordinary erasure slot used by checked record preparation.
    fn stdout_error_word(&mut self, layout: &Layout) -> Result<Expr, IngressError> {
        self.tick()?;
        let fin = apply(
            Expr::const_(layout.fin_constructor.clone(), Vec::new()),
            [transport_field(2)?, proofs::erased_value()],
        );
        Ok(Expr::app(
            Expr::const_(layout.word_constructor.clone(), Vec::new()),
            Expr::app(
                Expr::const_(layout.bits_constructor.clone(), Vec::new()),
                fin,
            ),
        ))
    }

    fn stdout_error(&mut self, layout: &Layout) -> Result<Expr, IngressError> {
        let filename = transport_field(4)?;
        let details = transport_field(5)?;
        let code = self.stdout_error_word(layout)?;
        let optional_file = choose(
            layout.option.source.clone(),
            transport_field(3)?,
            Expr::const_(layout.option.constructors[0].name.clone(), Vec::new()),
            Expr::app(
                Expr::const_(layout.option.constructors[1].name.clone(), Vec::new()),
                filename.clone(),
            ),
        );
        let mut branches = Vec::new();
        for ((_, shape), constructor) in stdout::error_cases()
            .into_iter()
            .zip(&layout.error.constructors)
        {
            self.tick()?;
            let fields = match shape {
                ErrorFields::OptionalFileCodeDetails => {
                    vec![optional_file.clone(), code.clone(), details.clone()]
                }
                ErrorFields::CodeDetails => vec![code.clone(), details.clone()],
                ErrorFields::FileCodeDetails => {
                    vec![filename.clone(), code.clone(), details.clone()]
                }
                ErrorFields::Empty => Vec::new(),
                ErrorFields::Message => vec![details.clone()],
            };
            reserve(&mut branches, self.limits.max_context_depth)?;
            branches.push(apply(
                Expr::const_(constructor.name.clone(), Vec::new()),
                fields,
            ));
        }
        // The safe native bridge accepts exactly tags 0..18 before creating
        // this private transport. The final branch is therefore tag 18, never
        // an invented default error for an unknown native layout.
        let mut result = branches
            .pop()
            .ok_or_else(|| unsupported("stdout error cases"))?;
        for (index, branch) in branches.into_iter().enumerate().rev() {
            self.tick()?;
            let condition = apply(
                c("Nat.beq"),
                [transport_field(1)?, nat::literal(index as u64)],
            );
            result = choose(layout.error.source.clone(), condition, result, branch);
        }
        Ok(result)
    }

    fn stdout_put_str_result(&mut self, layout: &Layout) -> Result<Expr, IngressError> {
        let success = apply(
            Expr::const_(layout.io_result.constructors[0].name.clone(), Vec::new()),
            [
                Expr::const_(layout.unit_constructor.clone(), Vec::new()),
                b(1)?,
            ],
        );
        let error = self.stdout_error(layout)?;
        let failure = apply(
            Expr::const_(layout.io_result.constructors[1].name.clone(), Vec::new()),
            [error, b(1)?],
        );
        Ok(choose(
            layout.io_result.source.clone(),
            transport_field(0)?,
            failure,
            success,
        ))
    }

    fn stdout_stream(&mut self, layout: &Layout) -> Result<Expr, IngressError> {
        let mut fields = Vec::new();
        for (index, type_) in layout.stream.constructors[0].fields.iter().enumerate() {
            let mut tail = type_.clone();
            let mut domains = Vec::new();
            while let ExprNode::ForallE {
                binder_type, body, ..
            } = tail.node()
            {
                self.tick()?;
                if body.has_loose_bvars() {
                    return Err(unsupported("stdout dependent callback type"));
                }
                reserve(&mut domains, self.limits.max_context_depth)?;
                domains.push(binder_type.clone());
                tail = body.clone();
            }
            let count =
                u32::try_from(domains.len()).map_err(|_| unsupported("stdout callback arity"))?;
            if count == 0 || domains.last() != Some(&layout.world) {
                return Err(unsupported("stdout callback world telescope"));
            }
            let mut body = Expr::proj(name(RAW_STREAM), index as u64, b(count)?);
            for argument in (0..count).rev() {
                body = Expr::app(body, b(argument)?);
            }
            if index == 4 {
                if domains != [c("String"), layout.world.clone()] || tail != layout.io_result.source
                {
                    return Err(unsupported("stdout putStr callback telescope"));
                }
                body = Expr::let_e(
                    self.stdout_adapter_name()?,
                    layout.transport.clone(),
                    body,
                    self.stdout_put_str_result(layout)?,
                    false,
                );
            }
            // Unsupported fields forward to their exact native target. The
            // VM refuses them before any result exists; no dummy logical
            // ByteArray, String, Bool, Unit or error value is manufactured.
            for domain in domains.into_iter().rev() {
                body = Expr::lam(
                    self.stdout_adapter_name()?,
                    domain,
                    body,
                    BinderInfo::Default,
                );
            }
            let value_type = self
                .value_type(type_)?
                .ok_or_else(|| unsupported("stdout callback interface"))?;
            body = self.typed_callable_result(body, type_.clone(), value_type)?;
            reserve(&mut fields, self.limits.max_context_depth)?;
            fields.push(body);
        }
        Ok(apply(
            Expr::const_(layout.stream.constructors[0].name.clone(), Vec::new()),
            fields,
        ))
    }

    /// The native getter runs only when its world action is invoked. Bare
    /// constants and stored aliases retain an ordinary reusable Golem closure.
    pub(super) fn stdout_call(
        &mut self,
        head: &Expr,
        arguments: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const {
            name: requested,
            levels,
        } = head.node()
        else {
            return Ok(None);
        };
        if requested != &stdout::source_name() || !levels.is_empty() {
            return Ok(None);
        }
        let Some(layout) = self.stdout_layout()? else {
            return Ok(None);
        };
        if arguments.len() > 1 {
            return Ok(None);
        }
        let stream = self.stdout_stream(&layout)?;
        let returned = apply(
            Expr::const_(layout.get_result.constructors[0].name.clone(), Vec::new()),
            [stream, b(1)?],
        );
        let body = Expr::let_e(
            self.stdout_adapter_name()?,
            layout.raw_stream,
            c(GETTER),
            returned,
            false,
        );
        let world_name = self.stdout_adapter_name()?;
        if let Some(world) = arguments.first() {
            return Ok(Some(Expr::let_e(
                world_name,
                layout.world,
                world.clone(),
                body,
                false,
            )));
        }
        let action_type = function(
            std::slice::from_ref(&layout.world),
            layout.get_result.source,
        );
        let value = Expr::lam(world_name, layout.world, body, BinderInfo::Default);
        Ok(Some(Expr::let_e(
            self.stdout_adapter_name()?,
            action_type,
            value,
            b(0)?,
            false,
        )))
    }
}

#[cfg(test)]
mod tests;
