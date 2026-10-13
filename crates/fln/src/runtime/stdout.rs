//! Bounded native stdin/stdout with ordinary logical Stream callbacks.
//!
//! Native Stream and packed IO.Result values never become admitted data by
//! relabeling. The exact getter returns a private carrier; its putStr callback
//! returns a private, checked transport record. Golem wrappers reconstruct
//! checked Unit, IO.Error and EST.Out layouts, retaining the incoming world.
//! getLine likewise reconstructs checked String/error results. The other
//! stream callbacks remain the VM's explicit native-call refusals.

use super::*;
use crate::source_intrinsics::io::stdout;
#[cfg(test)]
use crate::source_intrinsics::io::stdout::ErrorFields;
use fln_comp::fir::EffectClass;
use fln_comp::flbc::ResultOwnership;
use io_result::{ErrorLayout, choose};
use std::collections::BTreeMap;

const RAW_STREAM: &str = "_fln_runtime_stdout_stream";
const TRANSPORT: &str = "_fln_runtime_stdout_result";
const GETTER: &str = "_fln_runtime_stdout_get";
const STDIN_GETTER: &str = "_fln_runtime_stdin_get";
const READ_TRANSPORT: &str = "_fln_runtime_stdio_read_result";
const READ_PAYLOAD: &str = "_fln_runtime_stdio_read_payload";

fn getter_name(getter: stdout::Getter) -> Name {
    name(match getter {
        stdout::Getter::Stdout => GETTER,
        stdout::Getter::Stdin => STDIN_GETTER,
    })
}

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
    read_result: records::Shape,
    error: ErrorLayout,
    raw_stream: Expr,
    transport: Expr,
    read_transport: Expr,
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

    fn stdout_bind_getter(
        &mut self,
        getter: stdout::Getter,
        result_type: Expr,
    ) -> Result<(), IngressError> {
        let private = getter_name(getter);
        if self.environment.contains(&private) {
            return Err(unsupported("stdout private getter name collision"));
        }
        let source = getter.source_name().to_display_string();
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.name == source)
            .ok_or_else(|| unsupported("stdout generated getter row"))?;
        if row.kind != "opaque"
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
        self.stdio_layout(stdout::Getter::Stdout)
    }

    fn stdio_layout(&mut self, getter: stdout::Getter) -> Result<Option<Layout>, IngressError> {
        // Layout sharing never authorizes the other getter. Each source name
        // must pass its own exact opaque and required extern gate before its
        // distinct private binding is installed.
        if self.stdout.bindings.contains_key(&getter_name(getter)) {
            return Ok(self.stdout.layout.clone());
        }
        let matched = match getter {
            stdout::Getter::Stdout => stdout::contract_matches(
                self.environment,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )?,
            stdout::Getter::Stdin => stdout::getter_matches(
                self.environment,
                getter,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )?,
        };
        if !matched {
            return Ok(None);
        }
        if let Some(layout) = self.stdout.layout.clone() {
            self.stdout_bind_getter(getter, layout.raw_stream.clone())?;
            return Ok(Some(layout));
        }
        let Some(world) = self.st_evaluation_world()? else {
            return Ok(None);
        };
        let stream = self.io_checked_shape(c("IO.FS.Stream"))?;
        if stream.constructors.len() != 1 || stream.constructors[0].fields.len() != 6 {
            return Err(unsupported("stdout logical Stream layout"));
        }
        let get_result =
            self.io_checked_shape(apply(c("ST.Out"), [c("IO.RealWorld"), c("IO.FS.Stream")]))?;
        let io_result = self.io_checked_shape(apply(
            c("EST.Out"),
            [c("IO.Error"), c("IO.RealWorld"), c("Unit")],
        ))?;
        let read_result = self.io_checked_shape(apply(
            c("EST.Out"),
            [c("IO.Error"), c("IO.RealWorld"), c("String")],
        ))?;
        if get_result.constructors.len() != 1
            || get_result.constructors[0].fields.len() != 2
            || io_result.constructors.len() != 2
            || io_result
                .constructors
                .iter()
                .any(|constructor| constructor.fields.len() != 2)
            || read_result.constructors.len() != 2
            || read_result
                .constructors
                .iter()
                .enumerate()
                .any(|(index, ctor)| ctor.tag != index as u8 || ctor.fields.len() != 2)
        {
            return Err(unsupported("stdout checked world-result layout"));
        }
        let error = self.io_error_layout()?;
        let transport = self.io_private_record(
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
        let payload = c(READ_PAYLOAD);
        if self.environment.contains(&name(READ_PAYLOAD)) {
            return Err(unsupported("stdio read private payload name collision"));
        }
        if let Some(known) = self.value_types.native.get(&payload) {
            if *known != (ValueType::Abi, CallableResultOwnership::Erased) {
                return Err(unsupported("stdio read private payload representation"));
            }
        } else {
            self.value_types.native.try_reserve(1).map_err(|_| {
                IngressError::AllocationFailure {
                    resource: IngressResource::ProgramTables,
                    requested: self.value_types.native.len().saturating_add(1),
                }
            })?;
            self.value_types.native.insert(
                payload.clone(),
                (ValueType::Abi, CallableResultOwnership::Erased),
            );
        }
        let read_transport = self.io_private_record(
            READ_TRANSPORT,
            vec![
                payload,
                c("Bool"),
                c("Nat"),
                c("Nat"),
                c("Bool"),
                c("String"),
                c("String"),
            ],
        )?;
        native_fields[3] = function(std::slice::from_ref(&world), read_transport.clone());
        native_fields[4] = function(&[c("String"), world.clone()], transport.clone());
        let raw_stream = self.io_private_record(RAW_STREAM, native_fields)?;
        self.stdout_bind_getter(getter, raw_stream.clone())?;
        let layout = Layout {
            stream,
            get_result,
            io_result,
            read_result,
            error,
            raw_stream,
            transport,
            read_transport,
            world,
        };
        self.stdout.layout = Some(layout.clone());
        Ok(Some(layout))
    }

    fn stdout_put_str_result(&mut self, layout: &Layout) -> Result<Expr, IngressError> {
        let success = apply(
            Expr::const_(layout.io_result.constructors[0].name.clone(), Vec::new()),
            [
                Expr::const_(layout.error.unit_constructor.clone(), Vec::new()),
                b(1)?,
            ],
        );
        let error = self.io_transport_error(
            &layout.error,
            [
                transport_field(1)?,
                transport_field(2)?,
                transport_field(3)?,
                transport_field(4)?,
                transport_field(5)?,
            ],
        )?;
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
            if index == 3 {
                if domains != [layout.world.clone()] || tail != layout.read_result.source {
                    return Err(unsupported("stdio getLine callback telescope"));
                }
                let field =
                    |index| Ok::<_, IngressError>(Expr::proj(name(READ_TRANSPORT), index, b(0)?));
                // Native success alone authorizes ABI-to-String refinement;
                // the error arm's scalar placeholder is never a String.
                let success = apply(
                    Expr::const_(layout.read_result.constructors[0].name.clone(), Vec::new()),
                    [field(0)?, b(1)?],
                );
                let error = self.io_transport_error(
                    &layout.error,
                    [field(2)?, field(3)?, field(4)?, field(5)?, field(6)?],
                )?;
                let failure = apply(
                    Expr::const_(layout.read_result.constructors[1].name.clone(), Vec::new()),
                    [error, b(1)?],
                );
                let returned = choose(
                    layout.read_result.source.clone(),
                    field(1)?,
                    failure,
                    success,
                );
                body = Expr::let_e(
                    self.stdout_adapter_name()?,
                    layout.read_transport.clone(),
                    body,
                    returned,
                    false,
                );
            } else if index == 4 {
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
        let Some(getter) = stdout::Getter::from_name(requested) else {
            return Ok(None);
        };
        if !levels.is_empty() {
            return Ok(None);
        }
        let layout = match getter {
            stdout::Getter::Stdout => self.stdout_layout()?,
            stdout::Getter::Stdin => self.stdio_layout(getter)?,
        };
        let Some(layout) = layout else {
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
            Expr::const_(getter_name(getter), Vec::new()),
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
