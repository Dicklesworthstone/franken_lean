//! Rebuild native directory entries in their admitted logical data shapes.
//!
//! Native Array and two-String entries remain compiler-private. Every entry
//! is read once, then becomes FilePath.mk / DirEntry.mk / List / Array through
//! ordinary constructors and metered Nat recursion in the deferred IO action.
use super::*;

const NATIVE_ARRAY: &str = "_fln_runtime_fs_native_directory_array";
const NATIVE_ENTRY: &str = "_fln_runtime_fs_native_directory_entry";

pub(super) fn result_type() -> Expr {
    Expr::app(
        Expr::const_(name("Array"), vec![Level::zero()]),
        c("IO.FS.DirEntry"),
    )
}

#[derive(Clone)]
pub(super) struct Layout {
    native_array: Expr,
    native_entry: Expr,
    array: records::ShapeConstructor,
    list: records::Shape,
    path: records::ShapeConstructor,
    entry: records::ShapeConstructor,
    size: Name,
    get: Name,
}

fn lambda(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}

fn constructor(shape: &records::ShapeConstructor, fields: impl IntoIterator<Item = Expr>) -> Expr {
    apply(Expr::const_(shape.name.clone(), Vec::new()), fields)
}

impl Preparation<'_> {
    fn fs_directory_helper(
        &mut self,
        get: bool,
        native_array: &Expr,
        native_entry: &Expr,
    ) -> Result<Name, IngressError> {
        self.tick()?;
        let private = Name::str(
            name("_fln_runtime_fs_directory_helper"),
            if get { "get" } else { "size" },
        );
        if self.environment.contains(&private) {
            return Err(unsupported("directory helper name collision"));
        }
        if self.fs.bindings.contains_key(&private) {
            return Ok(private);
        }
        let (source, arity, ownership) = if get {
            (
                "Array.getInternal",
                4,
                "abi((a: borrowed_arg, i: borrowed_arg) -> owned_res)",
            )
        } else {
            ("Array.size", 2, "abi((a: borrowed_arg) -> raw_object)")
        };
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.name == source)
            .ok_or_else(|| unsupported("directory generated Array helper row"))?;
        if row.kind != "defn"
            || row.levels != 1
            || row.arity != arity
            || row.effect != "pure"
            || row.ownership != ownership
        {
            return Err(unsupported("directory generated Array helper contract"));
        }
        let mut domains = vec![native_array.clone()];
        let mut arguments = vec![ValueType::Abi];
        if get {
            domains.push(c("Nat"));
            arguments.push(ValueType::Nat);
        }
        self.fs.bindings.insert(
            private.clone(),
            (
                IntrinsicBinding {
                    name: private.clone(),
                    universe_arity: 0,
                    row: row.id.to_owned(),
                    arguments,
                    argument_ownership: vec![ArgumentOwnership::Borrowed; domains.len()],
                    result: if get {
                        ValueType::Constructor
                    } else {
                        ValueType::Nat
                    },
                    result_ownership: if get {
                        ResultOwnership::Owned
                    } else {
                        ResultOwnership::RawObject
                    },
                    effect: EffectClass::Pure,
                },
                function(&domains, if get { native_entry.clone() } else { c("Nat") }),
            ),
        );
        Ok(private)
    }

    fn fs_directory_layout(&mut self) -> Result<Layout, IngressError> {
        if let Some(layout) = &self.fs.directory {
            return Ok(layout.clone());
        }
        let path = self.io_checked_single_constructor(c("System.FilePath"), 1)?;
        let entry = self.io_checked_single_constructor(c("IO.FS.DirEntry"), 2)?;
        if path.fields != [c("String")] || entry.fields != [c("System.FilePath"), c("String")] {
            return Err(unsupported("directory checked entry and path layout"));
        }
        let array = self.io_checked_single_constructor(result_type(), 1)?;
        let list = self.io_checked_shape(array.fields[0].clone())?;
        if list.constructors.len() != 2
            || list.constructors[0].tag != 0
            || !list.constructors[0].fields.is_empty()
            || list.constructors[1].tag != 1
            || list.constructors[1].fields != [c("IO.FS.DirEntry"), list.source.clone()]
        {
            return Err(unsupported("directory checked entry list layout"));
        }
        let native_array = self.fs_abi_carrier(NATIVE_ARRAY, CallableResultOwnership::Owned)?;
        let native_entry = self.io_private_record(NATIVE_ENTRY, vec![c("String"), c("String")])?;
        let size = self.fs_directory_helper(false, &native_array, &native_entry)?;
        let get = self.fs_directory_helper(true, &native_array, &native_entry)?;
        let layout = Layout {
            native_array,
            native_entry,
            array,
            list,
            path,
            entry,
            size,
            get,
        };
        self.fs.directory = Some(layout.clone());
        Ok(layout)
    }

    pub(super) fn fs_materialize_directory(&mut self, payload: Expr) -> Result<Expr, IngressError> {
        let layout = self.fs_directory_layout()?;
        // After array/size bindings, the Nat.rec step has #0=accumulator,
        // #1=IH, #2=index, #3=size, #4=native Array. Its strict entry binding
        // adds one binder, so #0=entry, #1=accumulator and #2=IH in the body.
        let raw = apply(Expr::const_(layout.get.clone(), Vec::new()), [b(4)?, b(2)?]);
        let root = Expr::proj(name(NATIVE_ENTRY), 0, b(0)?);
        let file_name = Expr::proj(name(NATIVE_ENTRY), 1, b(0)?);
        let path = constructor(&layout.path, [root]);
        let entry = constructor(&layout.entry, [path, file_name]);
        let cons = constructor(&layout.list.constructors[1], [entry, b(1)?]);
        let entry_binding = Expr::let_e(
            self.fs_adapter_name()?,
            layout.native_entry,
            raw,
            Expr::app(b(2)?, cons),
            false,
        );
        let accumulator = function(
            std::slice::from_ref(&layout.list.source),
            layout.list.source.clone(),
        );
        let step = lambda(
            c("Nat"),
            lambda(
                accumulator.clone(),
                lambda(layout.list.source.clone(), entry_binding),
            ),
        );
        let motive = lambda(c("Nat"), accumulator);
        let zero = lambda(layout.list.source.clone(), b(0)?);
        let nil = constructor(&layout.list.constructors[0], []);
        let values = apply(
            Expr::const_(name("Nat.rec"), vec![Level::one()]),
            [motive, zero, step, b(0)?, nil],
        );
        // Descending indices prepended to the accumulator preserve the native
        // order; getInternal retains its own bounds check. No sort or path
        // normalization occurs and no error placeholder reaches this branch.
        let result = constructor(&layout.array, [values]);
        let size_binding = Expr::let_e(
            self.fs_adapter_name()?,
            c("Nat"),
            Expr::app(Expr::const_(layout.size, Vec::new()), b(0)?),
            result,
            false,
        );
        Ok(Expr::let_e(
            self.fs_adapter_name()?,
            layout.native_array,
            payload,
            size_binding,
            false,
        ))
    }
}
