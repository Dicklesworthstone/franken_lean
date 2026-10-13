//! Deferred file writing and line reading through checked Handle primitives.
//!
//! FilePath and Mode retain their admitted logical layouts. Native handles
//! have a separate owned ABI carrier, never Handle's opaque Unit default.
//! Native results remain private until their success/error branches rebuild
//! the corresponding checked EST.Out value with its incoming world token.

use super::*;
use crate::source_intrinsics::io::fs::{self, Operation};
use fln_comp::fir::EffectClass;
use fln_comp::flbc::{ArgumentOwnership, ResultOwnership};
use io_result::{ErrorLayout, choose};
use std::collections::BTreeMap;
mod bytes;
mod directory;

const HANDLE: &str = "_fln_runtime_fs_handle";
const PAYLOAD: &str = "_fln_runtime_fs_payload";
const TRANSPORT: &str = "_fln_runtime_fs_result";
const READ_TRANSPORT: &str = "_fln_runtime_fs_read_result";
const BYTES_TRANSPORT: &str = "_fln_runtime_fs_bytes_result";
const DIRECTORY_TRANSPORT: &str = "_fln_runtime_fs_directory_result";

#[derive(Default)]
pub(super) struct Store {
    next_adapter: u64,
    handle_checked: bool,
    bindings: BTreeMap<Name, (IntrinsicBinding, Expr)>,
    layout: Option<Layout>,
    read_layout: Option<Layout>,
    bytes_layout: Option<Layout>,
    directory_layout: Option<Layout>,
    word: Option<bytes::WordLayout>,
    word_repr_checked: bool,
    word_platform_checked: bool,
    bytes: Option<bytes::Layout>,
    write_bytes: Option<bytes::WriteLayout>,
    directory: Option<directory::Layout>,
}

#[derive(Clone)]
struct Layout {
    error: ErrorLayout,
    receiver: Expr,
    transport: Expr,
    transport_name: Name,
    world: Expr,
}

fn c(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}

fn b(index: u32) -> Result<Expr, IngressError> {
    Expr::bvar(index).map_err(|_| unsupported("filesystem adapter binder scope"))
}

fn apply(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

fn function(domains: &[Expr], result: Expr) -> Expr {
    domains.iter().rev().fold(result, |body, domain| {
        Expr::forall_e(Name::anonymous(), domain.clone(), body, BinderInfo::Default)
    })
}

fn field(layout: &Layout, index: u64) -> Result<Expr, IngressError> {
    Ok(Expr::proj(layout.transport_name.clone(), index, b(0)?))
}

impl Preparation<'_> {
    pub(crate) fn fs_intrinsic_binding(&self, requested: &Name) -> Option<IntrinsicBinding> {
        self.fs
            .bindings
            .get(requested)
            .map(|(binding, _)| binding.clone())
    }

    pub(super) fn fs_intrinsic_type(&self, requested: &Name) -> Option<Expr> {
        self.fs
            .bindings
            .get(requested)
            .map(|(_, type_)| type_.clone())
    }

    fn fs_adapter_name(&mut self) -> Result<Name, IngressError> {
        self.tick()?;
        let serial = self.fs.next_adapter;
        self.fs.next_adapter = serial
            .checked_add(1)
            .ok_or_else(|| unsupported("filesystem adapter identity"))?;
        let name = Name::num(name("_fln_runtime_fs_scope"), serial);
        if self.environment.contains(&name) {
            return Err(unsupported("filesystem adapter name collision"));
        }
        Ok(name)
    }

    fn fs_abi_carrier(
        &mut self,
        label: &str,
        ownership: CallableResultOwnership,
    ) -> Result<Expr, IngressError> {
        self.tick()?;
        let type_ = c(label);
        if self.environment.contains(&name(label)) {
            return Err(unsupported("filesystem private carrier name collision"));
        }
        if let Some(known) = self.value_types.native.get(&type_) {
            if *known != (ValueType::Abi, ownership) {
                return Err(unsupported("filesystem private carrier ownership"));
            }
            return Ok(type_);
        }
        self.value_types
            .native
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::ProgramTables,
                requested: self.value_types.native.len().saturating_add(1),
            })?;
        self.value_types
            .native
            .insert(type_.clone(), (ValueType::Abi, ownership));
        Ok(type_)
    }

    fn fs_handle(&mut self) -> Result<Option<Expr>, IngressError> {
        if !self.fs.handle_checked {
            if !fs::handle_matches(
                self.environment,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )? {
                return Ok(None);
            }
            self.fs.handle_checked = true;
        }
        self.fs_abi_carrier(HANDLE, CallableResultOwnership::Owned)
            .map(Some)
    }

    /// Keep the exact opaque Handle distinct before any type reduction. The
    /// carrier's Owned refinement is preserved in functions and closures, so
    /// its last ordinary Obj reference runs the native file finalizer.
    pub(super) fn fs_type_head(
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
        if requested != &name("IO.FS.Handle") || !levels.is_empty() || !arguments.is_empty() {
            return Ok(None);
        }
        self.fs_handle()
    }

    fn fs_layout(&mut self, operation: Operation) -> Result<Layout, IngressError> {
        let cached = match operation {
            Operation::GetLine => &self.fs.read_layout,
            Operation::Read => &self.fs.bytes_layout,
            Operation::ReadDir => &self.fs.directory_layout,
            _ => &self.fs.layout,
        };
        if let Some(layout) = cached {
            return Ok(layout.clone());
        }
        let receiver = if operation == Operation::ReadDir {
            c("String")
        } else {
            self.fs_handle()?
                .ok_or_else(|| unsupported("filesystem checked Handle"))?
        };
        let world = self
            .st_evaluation_world()?
            .ok_or_else(|| unsupported("filesystem checked world"))?;
        let error = self.io_error_layout()?;
        let payload = self.fs_abi_carrier(PAYLOAD, CallableResultOwnership::Erased)?;
        let transport_label = match operation {
            Operation::GetLine => READ_TRANSPORT,
            Operation::Read => BYTES_TRANSPORT,
            Operation::ReadDir => DIRECTORY_TRANSPORT,
            _ => TRANSPORT,
        };
        let transport = self.io_private_record(
            transport_label,
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
        let layout = Layout {
            error,
            receiver,
            transport,
            transport_name: name(transport_label),
            world,
        };
        match operation {
            Operation::GetLine => self.fs.read_layout = Some(layout.clone()),
            Operation::Read => self.fs.bytes_layout = Some(layout.clone()),
            Operation::ReadDir => self.fs.directory_layout = Some(layout.clone()),
            _ => self.fs.layout = Some(layout.clone()),
        }
        Ok(layout)
    }

    fn fs_bind_primitive(
        &mut self,
        operation: Operation,
        layout: &Layout,
    ) -> Result<Name, IngressError> {
        let private = operation.private_name();
        if self.fs.bindings.contains_key(&private) {
            return Ok(private);
        }
        if self.environment.contains(&private) {
            return Err(unsupported("filesystem primitive name collision"));
        }
        let source = operation.source_name().to_display_string();
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.name == source)
            .ok_or_else(|| unsupported("filesystem generated primitive row"))?;
        let arity = operation.source_arity() as u32;
        if row.kind != "opaque"
            || row.levels != 0
            || row.arity != arity
            || row.effect != "io"
            || row.ownership != "rule(borrowed-args,owned-result)"
        {
            return Err(unsupported("filesystem generated primitive contract"));
        }
        let (arguments, domains) = match operation {
            Operation::Open => (
                vec![ValueType::String, ValueType::Nat],
                vec![c("String"), c("Nat")],
            ),
            Operation::PutStr => (
                vec![ValueType::Abi, ValueType::String],
                vec![layout.receiver.clone(), c("String")],
            ),
            Operation::GetLine => (vec![ValueType::Abi], vec![layout.receiver.clone()]),
            Operation::Read => {
                let bytes = self.fs_bytes_layout()?;
                (
                    vec![ValueType::Abi, ValueType::Abi],
                    vec![layout.receiver.clone(), bytes.word.native],
                )
            }
            Operation::Write => {
                let bytes = self.fs_bytes_layout()?;
                (
                    vec![ValueType::Abi, ValueType::Abi],
                    vec![layout.receiver.clone(), bytes.packed],
                )
            }
            Operation::ReadDir => (vec![ValueType::String], vec![layout.receiver.clone()]),
        };
        self.fs.bindings.insert(
            private.clone(),
            (
                IntrinsicBinding {
                    name: private.clone(),
                    universe_arity: 0,
                    row: row.id.to_owned(),
                    arguments,
                    argument_ownership: vec![ArgumentOwnership::Borrowed; domains.len()],
                    result: ValueType::Constructor,
                    result_ownership: ResultOwnership::Owned,
                    effect: EffectClass::Io,
                },
                function(&domains, layout.transport.clone()),
            ),
        );
        Ok(private)
    }

    /// Select the logical variant through its checked eliminator. Nullary
    /// Mode values are boxed records, so native scalar unboxing is invalid.
    fn fs_mode_ordinal(&mut self, value: Expr) -> Result<Expr, IngressError> {
        self.tick()?;
        Ok(apply(
            Expr::const_(name("IO.FS.Mode.rec"), vec![Level::one()]),
            [
                Expr::lam(
                    Name::anonymous(),
                    c("IO.FS.Mode"),
                    c("Nat"),
                    BinderInfo::Default,
                ),
                nat::literal(0),
                nat::literal(1),
                nat::literal(2),
                nat::literal(3),
                nat::literal(4),
                value,
            ],
        ))
    }

    fn fs_result(
        &mut self,
        operation: Operation,
        layout: &Layout,
        result: &records::Shape,
    ) -> Result<Expr, IngressError> {
        let value = match operation {
            // The error-arm placeholder is never projected as a Handle.
            // Only the safe native open producer authorizes this payload.
            Operation::Open => field(layout, 0)?,
            Operation::PutStr | Operation::Write => {
                Expr::const_(layout.error.unit_constructor.clone(), Vec::new())
            }
            // The native producer validates canonical String success. The
            // typed EST.Out constructor inserts an explicit ABI-to-String
            // refinement here, inside the lazy success arm only. Error
            // packets carry scalar zero and never reach that projection.
            Operation::GetLine => field(layout, 0)?,
            Operation::Read => self.fs_materialize_bytes(field(layout, 0)?)?,
            Operation::ReadDir => self.fs_materialize_directory(field(layout, 0)?)?,
        };
        let success = apply(
            Expr::const_(result.constructors[0].name.clone(), Vec::new()),
            [value, b(1)?],
        );
        let error = self.io_transport_error(
            &layout.error,
            [
                field(layout, 2)?,
                field(layout, 3)?,
                field(layout, 4)?,
                field(layout, 5)?,
                field(layout, 6)?,
            ],
        )?;
        let failure = apply(
            Expr::const_(result.constructors[1].name.clone(), Vec::new()),
            [error, b(1)?],
        );
        Ok(choose(
            result.source.clone(),
            field(layout, 1)?,
            failure,
            success,
        ))
    }

    /// All source arguments remain ordinary strict applications of a closed,
    /// typed wrapper. The native row appears only inside the world lambda,
    /// preserving bare functions, aliases, partial applications and reuse.
    pub(super) fn fs_call(
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
        let Some(operation) = Operation::from_name(requested) else {
            return self.fs_word_call(head, arguments);
        };
        if !levels.is_empty() {
            return Ok(None);
        }
        if !self.fs.bindings.contains_key(&operation.private_name())
            && !fs::primitive_matches(
                self.environment,
                operation,
                &mut self.externs,
                &mut self.visited,
                self.limits,
            )?
        {
            return Ok(None);
        }
        let source_arity = operation.source_arity();
        if arguments.len() > source_arity + 1 {
            return Ok(None);
        }
        let layout = self.fs_layout(operation)?;
        let primitive = self.fs_bind_primitive(operation, &layout)?;
        let result_type = match operation {
            Operation::Open => c("IO.FS.Handle"),
            Operation::PutStr | Operation::Write => c("Unit"),
            Operation::GetLine => c("String"),
            Operation::Read => c("ByteArray"),
            Operation::ReadDir => directory::result_type(),
        };
        let result = self.io_checked_shape(apply(
            c("EST.Out"),
            [c("IO.Error"), c("IO.RealWorld"), result_type],
        ))?;
        if result.constructors.len() != 2
            || result
                .constructors
                .iter()
                .enumerate()
                .any(|(index, constructor)| {
                    constructor.tag != index as u8 || constructor.fields.len() != 2
                })
        {
            return Err(unsupported("filesystem checked IO result layout"));
        }
        let (domains, native_arguments) = match operation {
            Operation::Open => {
                let path = self.io_checked_shape(c("System.FilePath"))?;
                if path.constructors.len() != 1 || path.constructors[0].fields != [c("String")] {
                    return Err(unsupported("filesystem checked FilePath layout"));
                }
                let mode = self.io_checked_shape(c("IO.FS.Mode"))?;
                if mode.constructors.len() != 5
                    || mode
                        .constructors
                        .iter()
                        .enumerate()
                        .any(|(index, constructor)| {
                            constructor.tag != index as u8 || !constructor.fields.is_empty()
                        })
                {
                    return Err(unsupported("filesystem checked Mode layout"));
                }
                (
                    vec![path.source.clone(), mode.source.clone()],
                    vec![
                        Expr::proj(path.projection(&path.constructors[0]), 0, b(2)?),
                        self.fs_mode_ordinal(b(1)?)?,
                    ],
                )
            }
            Operation::PutStr => (
                vec![layout.receiver.clone(), c("String")],
                vec![b(2)?, b(1)?],
            ),
            Operation::GetLine => (vec![layout.receiver.clone()], vec![b(1)?]),
            Operation::Read => {
                let bytes = self.fs_bytes_layout()?;
                (
                    vec![layout.receiver.clone(), bytes.word.logical.source.clone()],
                    vec![b(2)?, self.fs_native_read_count(b(1)?)?],
                )
            }
            Operation::Write => (
                vec![layout.receiver.clone(), c("ByteArray")],
                vec![b(2)?, self.fs_native_write_bytes(b(1)?)?],
            ),
            Operation::ReadDir => {
                let path = self.io_checked_shape(c("System.FilePath"))?;
                if path.constructors.len() != 1 || path.constructors[0].fields != [c("String")] {
                    return Err(unsupported("directory checked FilePath layout"));
                }
                (
                    vec![path.source.clone()],
                    vec![Expr::proj(path.projection(&path.constructors[0]), 0, b(1)?)],
                )
            }
        };
        let returned = self.fs_result(operation, &layout, &result)?;
        let mut body = Expr::let_e(
            self.fs_adapter_name()?,
            layout.transport.clone(),
            apply(Expr::const_(primitive, Vec::new()), native_arguments),
            returned,
            false,
        );
        let mut domains = domains;
        domains.push(layout.world);
        for domain in domains.iter().rev() {
            body = Expr::lam(
                self.fs_adapter_name()?,
                domain.clone(),
                body,
                BinderInfo::Default,
            );
        }
        let wrapper = Expr::let_e(
            self.fs_adapter_name()?,
            function(&domains, result.source),
            body,
            b(0)?,
            false,
        );
        Ok(Some(arguments.iter().cloned().fold(wrapper, Expr::app)))
    }
}

#[cfg(test)]
mod tests;
