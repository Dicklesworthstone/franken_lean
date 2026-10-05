//! The TCB inventory (bead `franken_lean-z8j.1.17`; plan §8.1): which functions of the
//! workspace's own crates the kernel's one authority, `fln_kernel::check`, can reach.
//!
//! The 12 KLOC covenant counts the lines of `crates/fln-kernel/src` and nothing else, while
//! kernel verdicts also depend on trusted logic that lives elsewhere: universe normalization in
//! `fln-core`'s `level.rs`, binder arithmetic in its `expr.rs`, the persistent map in
//! `fln-env`. This module measures that dependency closure from the real call graph, so it
//! cannot drift from the code the way a hand-kept list does.
//!
//! # Where the graph comes from
//!
//! The linker. `src/bin/tcb-probe.rs` references nothing from the workspace except `check`,
//! taken as an opaque function pointer. Each function is emitted into its own section and the
//! linker discards every section nothing references, so the `fln_*` functions left in that
//! binary are the ones reachable from `check` as the compiler resolved them: inherent and
//! trait methods, generic instantiations, closures, and `Drop` impls included. This module
//! reads that set out of the binary's ELF64 symbol table and names each symbol with a
//! demangler for Rust's v0 mangling. Both are std-only, because the dependency universe is
//! closed (D1) and no symbol or ELF crate is in it.
//!
//! # What it counts
//!
//! A symbol belongs to the crate that *defines* its function: a method of an `impl` block
//! belongs to the crate of that block, a trait's default method to the trait's crate, a
//! closure to the crate of the function containing it. `core`'s `sort_by` instantiated with a
//! kernel closure is toolchain code. An *item* is a source-level function: generic
//! instantiations of one function, and the closures inside it, collapse into that function's
//! item. The inventory lists items per workspace crate and counts symbols beside them.
//!
//! # What it does not establish
//!
//! * Reachability, not execution. The linker keeps every method of a vtable that `check`
//!   builds, and the formatting code on panic paths, so the set over-approximates the dynamic
//!   call graph.
//! * Inlined code would be invisible. The measurement is defined at the dev profile
//!   (opt-level 0), where neither the MIR inliner nor LLVM's inliner runs, and none of the
//!   counted crates uses `#[inline(always)]`. The test refuses a run without debug assertions,
//!   its proxy for that profile.
//! * Compile-time evaluation leaves no function behind, so `const` code that only runs at
//!   compile time is not counted.
//! * The toolchain's own crates (`core`, `alloc`, `std`) are counted, not listed.
//! * The root is `check` alone. Another public kernel entry point is outside the measurement
//!   unless `check` reaches it.
//! * Units are functions. The covenant counts lines, so the two numbers are different
//!   measurements of the trust base and neither is its semantic size.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// Why the binary could not be read as an inventory source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InventoryError {
    /// Not a little-endian ELF64 file.
    NotElf64,
    /// A header, table, or string runs past the end of the file.
    Truncated(&'static str),
    /// No `.symtab`: the binary was stripped, so its functions cannot be named.
    NoSymbolTable,
    /// A Rust v0 symbol this demangler could not read. Counting it as anything would guess.
    Undemangleable {
        symbol: String,
        error: DemangleError,
    },
}

impl fmt::Display for InventoryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotElf64 => f.write_str("not a little-endian ELF64 file"),
            Self::Truncated(what) => {
                write!(f, "truncated ELF: {what} runs past the end of the file")
            }
            Self::NoSymbolTable => f.write_str("the binary has no .symtab (stripped)"),
            Self::Undemangleable { symbol, error } => {
                write!(f, "cannot demangle {symbol}: {error}")
            }
        }
    }
}

impl std::error::Error for InventoryError {}

fn read_u16(bytes: &[u8], at: usize, what: &'static str) -> Result<u16, InventoryError> {
    let raw = bytes
        .get(at..at.checked_add(2).ok_or(InventoryError::Truncated(what))?)
        .ok_or(InventoryError::Truncated(what))?;
    Ok(u16::from_le_bytes([raw[0], raw[1]]))
}

fn read_u32(bytes: &[u8], at: usize, what: &'static str) -> Result<u32, InventoryError> {
    let raw = bytes
        .get(at..at.checked_add(4).ok_or(InventoryError::Truncated(what))?)
        .ok_or(InventoryError::Truncated(what))?;
    let mut word = [0_u8; 4];
    word.copy_from_slice(raw);
    Ok(u32::from_le_bytes(word))
}

fn read_u64(bytes: &[u8], at: usize, what: &'static str) -> Result<u64, InventoryError> {
    let raw = bytes
        .get(at..at.checked_add(8).ok_or(InventoryError::Truncated(what))?)
        .ok_or(InventoryError::Truncated(what))?;
    let mut word = [0_u8; 8];
    word.copy_from_slice(raw);
    Ok(u64::from_le_bytes(word))
}

fn to_index(value: u64, what: &'static str) -> Result<usize, InventoryError> {
    usize::try_from(value).map_err(|_| InventoryError::Truncated(what))
}

/// The names of every defined function symbol (`STT_FUNC`, section index not `SHN_UNDEF`) in an
/// ELF64 little-endian file's `.symtab`, local and global alike, deduplicated and sorted.
pub fn elf_function_symbols(elf: &[u8]) -> Result<Vec<String>, InventoryError> {
    const SECTION_HEADER: usize = 64;
    const SYMBOL: usize = 24;
    const SHT_SYMTAB: u32 = 2;
    const STT_FUNC: u8 = 2;
    if elf.get(..4) != Some(b"\x7fELF".as_slice())
        || elf.get(4) != Some(&2)
        || elf.get(5) != Some(&1)
    {
        return Err(InventoryError::NotElf64);
    }
    let section_table = to_index(read_u64(elf, 0x28, "e_shoff")?, "e_shoff")?;
    let entry_size = usize::from(read_u16(elf, 0x3a, "e_shentsize")?);
    if entry_size != SECTION_HEADER {
        return Err(InventoryError::NotElf64);
    }
    let section = |index: usize| -> Result<usize, InventoryError> {
        index
            .checked_mul(SECTION_HEADER)
            .and_then(|offset| offset.checked_add(section_table))
            .ok_or(InventoryError::Truncated("section header"))
    };
    // Extended numbering: a zero e_shnum means the count lives in section 0's sh_size.
    let mut sections = usize::from(read_u16(elf, 0x3c, "e_shnum")?);
    if sections == 0 {
        sections = to_index(read_u64(elf, section(0)? + 32, "sh_size")?, "sh_size")?;
    }
    let mut symbols = BTreeSet::new();
    let mut found = false;
    for index in 0..sections {
        let header = section(index)?;
        if read_u32(elf, header + 4, "sh_type")? != SHT_SYMTAB {
            continue;
        }
        found = true;
        let offset = to_index(read_u64(elf, header + 24, "sh_offset")?, "sh_offset")?;
        let size = to_index(read_u64(elf, header + 32, "sh_size")?, "sh_size")?;
        let strings_header = section(to_index(
            u64::from(read_u32(elf, header + 40, "sh_link")?),
            "sh_link",
        )?)?;
        let strings = to_index(
            read_u64(elf, strings_header + 24, "sh_offset")?,
            "sh_offset",
        )?;
        let strings_size = to_index(read_u64(elf, strings_header + 32, "sh_size")?, "sh_size")?;
        let string_table = elf
            .get(
                strings
                    ..strings
                        .checked_add(strings_size)
                        .ok_or(InventoryError::Truncated("strtab"))?,
            )
            .ok_or(InventoryError::Truncated("strtab"))?;
        let table = elf
            .get(
                offset
                    ..offset
                        .checked_add(size)
                        .ok_or(InventoryError::Truncated("symtab"))?,
            )
            .ok_or(InventoryError::Truncated("symtab"))?;
        let (entries, _) = table.as_chunks::<SYMBOL>();
        for entry in entries {
            let entry = entry.as_slice();
            let info = entry.get(4).copied().unwrap_or(0);
            let section_index = read_u16(entry, 6, "st_shndx")?;
            if info & 0xf != STT_FUNC || section_index == 0 {
                continue;
            }
            let name_at = to_index(u64::from(read_u32(entry, 0, "st_name")?), "st_name")?;
            let tail = string_table
                .get(name_at..)
                .ok_or(InventoryError::Truncated("symbol name"))?;
            let end = tail
                .iter()
                .position(|&byte| byte == 0)
                .ok_or(InventoryError::Truncated("symbol name"))?;
            if end > 0 {
                symbols.insert(String::from_utf8_lossy(&tail[..end]).into_owned());
            }
        }
    }
    if !found {
        return Err(InventoryError::NoSymbolTable);
    }
    Ok(symbols.into_iter().collect())
}

/// Why a v0 symbol could not be read, and where.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DemangleError {
    pub at: usize,
    pub reason: &'static str,
}

impl fmt::Display for DemangleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at byte {}", self.reason, self.at)
    }
}

/// A demangled v0 symbol.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Demangled {
    /// The whole name with generic arguments, crate hashes dropped.
    pub full: String,
    /// The source-level function: generic arguments erased, enclosing closures folded away.
    pub item: String,
    /// The crate that defines the function.
    pub crate_name: String,
}

#[derive(Debug, Clone)]
enum Path {
    Crate(String),
    /// `<T>` for an inherent impl (`implementor` names the impl block's own path).
    Inherent {
        implementor: Box<Path>,
        self_ty: Box<Type>,
    },
    /// `<T as Trait>` from a trait impl (`implementor` names the impl's own path).
    TraitImpl {
        implementor: Box<Path>,
        self_ty: Box<Type>,
        trait_path: Box<Path>,
    },
    /// `<T as Trait>` naming a trait's own (default) item.
    TraitDef {
        self_ty: Box<Type>,
        trait_path: Box<Path>,
    },
    Nested {
        namespace: u8,
        parent: Box<Path>,
        disambiguator: u64,
        name: String,
    },
    Generic {
        path: Box<Path>,
        args: Vec<GenericArg>,
    },
}

#[derive(Debug, Clone)]
enum GenericArg {
    Lifetime,
    Type(Type),
    Const(String),
}

#[derive(Debug, Clone)]
enum Type {
    Basic(&'static str),
    Named(Path),
    Array(Box<Type>, String),
    Slice(Box<Type>),
    Tuple(Vec<Type>),
    Ref { mutable: bool, inner: Box<Type> },
    Ptr { mutable: bool, inner: Box<Type> },
    Fn(String),
    Dyn(String),
}

struct Parser<'a> {
    input: &'a [u8],
    at: usize,
    depth: usize,
}

const MAX_DEPTH: usize = 256;

impl Parser<'_> {
    fn error(&self, reason: &'static str) -> DemangleError {
        DemangleError {
            at: self.at,
            reason,
        }
    }

    fn peek(&self) -> Option<u8> {
        self.input.get(self.at).copied()
    }

    fn eat(&mut self, byte: u8) -> bool {
        if self.peek() == Some(byte) {
            self.at += 1;
            true
        } else {
            false
        }
    }

    fn next(&mut self) -> Result<u8, DemangleError> {
        let byte = self.peek().ok_or_else(|| self.error("unexpected end"))?;
        self.at += 1;
        Ok(byte)
    }

    fn enter(&mut self) -> Result<(), DemangleError> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return Err(self.error("nesting too deep"));
        }
        Ok(())
    }

    /// `{0-9a-zA-Z} "_"`: an empty run is 0, otherwise the value plus one.
    fn base62(&mut self) -> Result<u64, DemangleError> {
        if self.eat(b'_') {
            return Ok(0);
        }
        let mut value: u64 = 0;
        loop {
            let byte = self.next()?;
            let digit = match byte {
                b'0'..=b'9' => byte - b'0',
                b'a'..=b'z' => 10 + byte - b'a',
                b'A'..=b'Z' => 36 + byte - b'A',
                b'_' => break,
                _ => return Err(self.error("bad base-62 digit")),
            };
            value = value
                .checked_mul(62)
                .and_then(|v| v.checked_add(u64::from(digit)))
                .ok_or_else(|| self.error("base-62 overflow"))?;
        }
        value
            .checked_add(1)
            .ok_or_else(|| self.error("base-62 overflow"))
    }

    /// `"0" | [1-9] {[0-9]}`: a leading zero is the whole number, so `00` is two numbers.
    fn decimal(&mut self) -> Result<usize, DemangleError> {
        if self.eat(b'0') {
            return Ok(0);
        }
        let start = self.at;
        let mut value: usize = 0;
        while let Some(byte @ b'0'..=b'9') = self.peek() {
            self.at += 1;
            value = value
                .checked_mul(10)
                .and_then(|v| v.checked_add(usize::from(byte - b'0')))
                .ok_or_else(|| self.error("decimal overflow"))?;
        }
        if self.at == start {
            return Err(self.error("expected a decimal number"));
        }
        Ok(value)
    }

    /// `["s" <base-62-number>]`: absent is 0, present is the number plus one.
    fn disambiguator(&mut self) -> Result<u64, DemangleError> {
        if !self.eat(b's') {
            return Ok(0);
        }
        self.base62()?
            .checked_add(1)
            .ok_or_else(|| self.error("disambiguator overflow"))
    }

    /// `["u"] <decimal> ["_"] <bytes>`.
    fn undisambiguated_identifier(&mut self) -> Result<String, DemangleError> {
        let punycode = self.eat(b'u');
        let length = self.decimal()?;
        self.eat(b'_');
        let end = self
            .at
            .checked_add(length)
            .filter(|&end| end <= self.input.len())
            .ok_or_else(|| self.error("identifier runs past the end"))?;
        let bytes = &self.input[self.at..end];
        self.at = end;
        let text = String::from_utf8_lossy(bytes).into_owned();
        Ok(if punycode {
            format!("punycode{{{text}}}")
        } else {
            text
        })
    }

    /// Parse the production at a back-reference target, then resume after the reference.
    fn backref<T>(
        &mut self,
        parse: impl FnOnce(&mut Self) -> Result<T, DemangleError>,
    ) -> Result<T, DemangleError> {
        let reference_at = self.at - 1;
        let target =
            usize::try_from(self.base62()?).map_err(|_| self.error("bad back-reference"))?;
        // Targets count from just after "_R" and must point strictly backwards.
        let absolute = target + 2;
        if absolute >= reference_at {
            return Err(self.error("back-reference does not point backwards"));
        }
        let resume = self.at;
        self.at = absolute;
        let parsed = parse(self);
        self.at = resume;
        parsed
    }

    fn path(&mut self) -> Result<Path, DemangleError> {
        self.enter()?;
        let path = match self.next()? {
            b'C' => {
                self.disambiguator()?;
                Path::Crate(self.undisambiguated_identifier()?)
            }
            b'M' => {
                self.disambiguator()?;
                let implementor = Box::new(self.path()?);
                let self_ty = Box::new(self.ty()?);
                Path::Inherent {
                    implementor,
                    self_ty,
                }
            }
            b'X' => {
                self.disambiguator()?;
                let implementor = Box::new(self.path()?);
                let self_ty = Box::new(self.ty()?);
                let trait_path = Box::new(self.path()?);
                Path::TraitImpl {
                    implementor,
                    self_ty,
                    trait_path,
                }
            }
            b'Y' => {
                let self_ty = Box::new(self.ty()?);
                let trait_path = Box::new(self.path()?);
                Path::TraitDef {
                    self_ty,
                    trait_path,
                }
            }
            b'N' => {
                let namespace = self.next()?;
                if !namespace.is_ascii_alphabetic() {
                    return Err(self.error("bad namespace"));
                }
                let parent = Box::new(self.path()?);
                let disambiguator = self.disambiguator()?;
                let name = self.undisambiguated_identifier()?;
                Path::Nested {
                    namespace,
                    parent,
                    disambiguator,
                    name,
                }
            }
            b'I' => {
                let path = Box::new(self.path()?);
                let mut args = Vec::new();
                while !self.eat(b'E') {
                    args.push(self.generic_arg()?);
                }
                Path::Generic { path, args }
            }
            b'B' => self.backref(Self::path)?,
            _ => return Err(self.error("bad path tag")),
        };
        self.depth -= 1;
        Ok(path)
    }

    fn generic_arg(&mut self) -> Result<GenericArg, DemangleError> {
        if self.eat(b'L') {
            self.base62()?;
            return Ok(GenericArg::Lifetime);
        }
        if self.eat(b'K') {
            return Ok(GenericArg::Const(self.constant()?));
        }
        Ok(GenericArg::Type(self.ty()?))
    }

    fn lifetime_and_type(&mut self) -> Result<Type, DemangleError> {
        if self.eat(b'L') {
            self.base62()?;
        }
        self.ty()
    }

    fn ty(&mut self) -> Result<Type, DemangleError> {
        self.enter()?;
        let start = self.at;
        let ty = match self.next()? {
            b'a' => Type::Basic("i8"),
            b'b' => Type::Basic("bool"),
            b'c' => Type::Basic("char"),
            b'd' => Type::Basic("f64"),
            b'e' => Type::Basic("str"),
            b'f' => Type::Basic("f32"),
            b'h' => Type::Basic("u8"),
            b'i' => Type::Basic("isize"),
            b'j' => Type::Basic("usize"),
            b'l' => Type::Basic("i32"),
            b'm' => Type::Basic("u32"),
            b'n' => Type::Basic("i128"),
            b'o' => Type::Basic("u128"),
            b's' => Type::Basic("i16"),
            b't' => Type::Basic("u16"),
            b'u' => Type::Basic("()"),
            b'v' => Type::Basic("..."),
            b'x' => Type::Basic("i64"),
            b'y' => Type::Basic("u64"),
            b'z' => Type::Basic("!"),
            b'p' => Type::Basic("_"),
            b'A' => {
                let element = Box::new(self.ty()?);
                Type::Array(element, self.constant()?)
            }
            b'S' => Type::Slice(Box::new(self.ty()?)),
            b'T' => {
                let mut elements = Vec::new();
                while !self.eat(b'E') {
                    elements.push(self.ty()?);
                }
                Type::Tuple(elements)
            }
            b'R' => Type::Ref {
                mutable: false,
                inner: Box::new(self.lifetime_and_type()?),
            },
            b'Q' => Type::Ref {
                mutable: true,
                inner: Box::new(self.lifetime_and_type()?),
            },
            b'P' => Type::Ptr {
                mutable: false,
                inner: Box::new(self.ty()?),
            },
            b'O' => Type::Ptr {
                mutable: true,
                inner: Box::new(self.ty()?),
            },
            b'F' => Type::Fn(self.fn_signature()?),
            b'D' => Type::Dyn(self.dyn_bounds()?),
            b'B' => self.backref(Self::ty)?,
            b'C' | b'M' | b'X' | b'Y' | b'N' | b'I' => {
                self.at = start;
                Type::Named(self.path()?)
            }
            _ => return Err(self.error("bad type tag")),
        };
        self.depth -= 1;
        Ok(ty)
    }

    fn binder(&mut self) -> Result<(), DemangleError> {
        if self.eat(b'G') {
            self.base62()?;
        }
        Ok(())
    }

    fn fn_signature(&mut self) -> Result<String, DemangleError> {
        self.binder()?;
        let unsafety = if self.eat(b'U') { "unsafe " } else { "" };
        let abi = if self.eat(b'K') {
            if self.eat(b'C') {
                "extern \"C\" ".to_owned()
            } else {
                format!(
                    "extern \"{}\" ",
                    self.undisambiguated_identifier()?.replace('_', "-")
                )
            }
        } else {
            String::new()
        };
        let mut inputs = Vec::new();
        while !self.eat(b'E') {
            inputs.push(render_type(&self.ty()?, true));
        }
        let output = self.ty()?;
        let mut text = format!("{unsafety}{abi}fn({})", inputs.join(", "));
        if !matches!(output, Type::Basic("()")) {
            text.push_str(" -> ");
            text.push_str(&render_type(&output, true));
        }
        Ok(text)
    }

    fn dyn_bounds(&mut self) -> Result<String, DemangleError> {
        self.binder()?;
        let mut traits = Vec::new();
        while !self.eat(b'E') {
            let mut text = render_path_in(&self.path()?, true, true);
            let mut bindings = Vec::new();
            while self.eat(b'p') {
                let name = self.undisambiguated_identifier()?;
                bindings.push(format!("{name} = {}", render_type(&self.ty()?, true)));
            }
            if !bindings.is_empty() {
                // Associated-type bindings join the trait's own argument list, if it has one.
                let bindings = bindings.join(", ");
                if text.ends_with('>') {
                    text.pop();
                    text.push_str(&format!(", {bindings}>"));
                } else {
                    text.push_str(&format!("<{bindings}>"));
                }
            }
            traits.push(text);
        }
        // The trailing lifetime bound.
        if self.eat(b'L') {
            self.base62()?;
        }
        Ok(format!("dyn {}", traits.join(" + ")))
    }

    fn constant(&mut self) -> Result<String, DemangleError> {
        self.enter()?;
        let value = match self.next()? {
            b'p' => "_".to_owned(),
            b'B' => self.backref(Self::constant)?,
            tag @ (b'a' | b'b' | b'c' | b'h' | b'i' | b'j' | b'l' | b'm' | b'n' | b'o' | b's'
            | b't' | b'x' | b'y') => {
                let negative = self.eat(b'n');
                let mut digits = String::new();
                while let Some(byte) = self.peek() {
                    self.at += 1;
                    if byte == b'_' {
                        break;
                    }
                    if !byte.is_ascii_hexdigit() {
                        return Err(self.error("bad constant digit"));
                    }
                    digits.push(char::from(byte));
                }
                let magnitude =
                    u128::from_str_radix(if digits.is_empty() { "0" } else { &digits }, 16)
                        .map_err(|_| self.error("constant overflow"))?;
                // Every scalar constant is the type's tag, an optional `n`, hex digits, `_`.
                match (tag, magnitude) {
                    (b'b', 0) => "false".to_owned(),
                    (b'b', 1) => "true".to_owned(),
                    (b'b', _) => return Err(self.error("bad bool constant")),
                    (b'c', code) => format!("'\\u{{{code:x}}}'"),
                    _ => format!("{}{magnitude}", if negative { "-" } else { "" }),
                }
            }
            _ => return Err(self.error("unsupported constant")),
        };
        self.depth -= 1;
        Ok(value)
    }
}

fn render_type(ty: &Type, generics: bool) -> String {
    match ty {
        Type::Basic(name) => (*name).to_owned(),
        Type::Named(path) => render_path_in(path, generics, true),
        Type::Array(element, length) => format!("[{}; {length}]", render_type(element, generics)),
        Type::Slice(element) => format!("[{}]", render_type(element, generics)),
        Type::Tuple(elements) => {
            let inner: Vec<String> = elements.iter().map(|e| render_type(e, generics)).collect();
            if inner.len() == 1 {
                format!("({},)", inner[0])
            } else {
                format!("({})", inner.join(", "))
            }
        }
        Type::Ref { mutable, inner } => {
            format!(
                "&{}{}",
                if *mutable { "mut " } else { "" },
                render_type(inner, generics)
            )
        }
        Type::Ptr { mutable, inner } => {
            format!(
                "*{} {}",
                if *mutable { "mut" } else { "const" },
                render_type(inner, generics)
            )
        }
        Type::Fn(signature) => signature.clone(),
        Type::Dyn(bounds) => bounds.clone(),
    }
}

fn render_path(path: &Path, generics: bool) -> String {
    render_path_in(path, generics, false)
}

/// Render a path. In a type (`in_type`), generic arguments follow the name directly
/// (`Arc<T>`); in a value path they take the turbofish (`sort_by::<F>`).
fn render_path_in(path: &Path, generics: bool, in_type: bool) -> String {
    match path {
        Path::Crate(name) => name.clone(),
        Path::Inherent { self_ty, .. } => format!("<{}>", render_type(self_ty, generics)),
        Path::TraitImpl {
            self_ty,
            trait_path,
            ..
        }
        | Path::TraitDef {
            self_ty,
            trait_path,
        } => {
            format!(
                "<{} as {}>",
                render_type(self_ty, generics),
                render_path_in(trait_path, generics, true)
            )
        }
        Path::Nested {
            namespace,
            parent,
            disambiguator,
            name,
        } => {
            let parent = render_path_in(parent, generics, in_type);
            match namespace {
                b'C' if name.is_empty() => format!("{parent}::{{closure#{disambiguator}}}"),
                b'C' => format!("{parent}::{{closure:{name}#{disambiguator}}}"),
                b'S' => format!("{parent}::{{shim:{name}#{disambiguator}}}"),
                upper if upper.is_ascii_uppercase() && name.is_empty() => {
                    format!("{parent}::{{{}#{disambiguator}}}", char::from(*upper))
                }
                upper if upper.is_ascii_uppercase() => {
                    format!(
                        "{parent}::{{{}:{name}#{disambiguator}}}",
                        char::from(*upper)
                    )
                }
                // A constructor's value path carries no name of its own.
                _ if name.is_empty() => parent,
                _ => format!("{parent}::{name}"),
            }
        }
        Path::Generic { path, args } => {
            let base = render_path_in(path, generics, in_type);
            if !generics {
                return base;
            }
            let args: Vec<String> = args
                .iter()
                .filter_map(|arg| match arg {
                    GenericArg::Lifetime => None,
                    GenericArg::Type(ty) => Some(render_type(ty, true)),
                    GenericArg::Const(value) => Some(value.clone()),
                })
                .collect();
            let open = if in_type { "<" } else { "::<" };
            if args.is_empty() {
                base
            } else {
                format!("{base}{open}{}>", args.join(", "))
            }
        }
    }
}

/// The crate that defines the function `path` names.
fn defining_crate(path: &Path) -> &str {
    match path {
        Path::Crate(name) => name,
        Path::Nested { parent, .. } => defining_crate(parent),
        Path::Generic { path, .. } => defining_crate(path),
        // An impl block's methods belong to the crate the block is written in, which for
        // `impl [T]` is the toolchain's, not the element type's.
        Path::Inherent { implementor, .. } | Path::TraitImpl { implementor, .. } => {
            defining_crate(implementor)
        }
        Path::TraitDef { trait_path, .. } => defining_crate(trait_path),
    }
}

/// Fold closures, shims and other compiler-made nested items into the function enclosing them.
fn enclosing_item(path: &Path) -> &Path {
    match path {
        Path::Nested {
            namespace, parent, ..
        } if namespace.is_ascii_uppercase() => enclosing_item(parent),
        Path::Generic { path, .. } => enclosing_item(path),
        other => other,
    }
}

/// Demangle one Rust v0 symbol (`_R...`).
pub fn demangle_v0(symbol: &str) -> Result<Demangled, DemangleError> {
    // An LLVM-made local copy carries a `.llvm.<n>` suffix; vendor suffixes start with `.` or `$`.
    let mangled = symbol.split(['.', '$']).next().unwrap_or(symbol);
    let input = mangled.strip_prefix("_R").ok_or(DemangleError {
        at: 0,
        reason: "not a v0 symbol",
    })?;
    let mut parser = Parser {
        input: mangled.as_bytes(),
        at: 2,
        depth: 0,
    };
    if input.as_bytes().first().is_some_and(u8::is_ascii_digit) {
        parser.decimal()?;
    }
    let path = parser.path()?;
    // The instantiating crate, if present, is not part of the name.
    if parser.at < parser.input.len() {
        parser.path()?;
    }
    if parser.at != parser.input.len() {
        return Err(parser.error("trailing bytes"));
    }
    let item = render_path(enclosing_item(&path), false);
    Ok(Demangled {
        full: render_path(&path, true),
        item,
        crate_name: defining_crate(enclosing_item(&path)).to_owned(),
    })
}

/// What the probe binary's symbol table says about the workspace's trust base.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Inventory {
    /// Per workspace crate (`fln_*`), the distinct source-level function items it contributes.
    pub items: BTreeMap<String, BTreeSet<String>>,
    /// Per workspace crate, the distinct linked function symbols (instantiations and closures
    /// counted separately, local duplicates collapsed).
    pub symbols: BTreeMap<String, BTreeSet<String>>,
    /// Distinct function symbols defined by any other crate: the toolchain and the probe.
    pub other_symbols: usize,
    /// Function symbols that are not Rust v0 symbols: C runtime and assembly stubs.
    pub non_rust_symbols: usize,
}

/// The crates whose functions the inventory lists. Derived, not hand-kept: every product
/// crate of this workspace is named `fln` or `fln_*`, so whatever the linker keeps from any of
/// them is counted. The facade crate `fln` itself was once left out by a `fln_` prefix test;
/// `fln_kernel::check` cannot reach it, but the checker-reader probe roots there (bead
/// `franken_lean-z8j.1.14`), and a classifier blind to it would hide the facade's functions.
pub fn is_workspace_crate(crate_name: &str) -> bool {
    crate_name == "fln" || crate_name.starts_with("fln_")
}

impl Inventory {
    pub fn item_count(&self) -> usize {
        self.items.values().map(BTreeSet::len).sum()
    }

    /// Items outside `fln_kernel`: the trusted code the line covenant does not count.
    pub fn adjacent_item_count(&self) -> usize {
        self.items
            .iter()
            .filter(|(crate_name, _)| crate_name.as_str() != "fln_kernel")
            .map(|(_, items)| items.len())
            .sum()
    }
}

/// Build the inventory from a symbol list. Every `_R` symbol must demangle.
pub fn inventory(symbols: &[String]) -> Result<Inventory, InventoryError> {
    let mut inventory = Inventory::default();
    let mut other = BTreeSet::new();
    for symbol in symbols {
        if !symbol.starts_with("_R") {
            inventory.non_rust_symbols += 1;
            continue;
        }
        let demangled = demangle_v0(symbol).map_err(|error| InventoryError::Undemangleable {
            symbol: symbol.clone(),
            error,
        })?;
        if is_workspace_crate(&demangled.crate_name) {
            inventory
                .items
                .entry(demangled.crate_name.clone())
                .or_default()
                .insert(demangled.item);
            inventory
                .symbols
                .entry(demangled.crate_name)
                .or_default()
                .insert(demangled.full);
        } else {
            other.insert(demangled.full);
        }
    }
    inventory.other_symbols = other.len();
    Ok(inventory)
}

/// The schema line of the disclosure file.
pub const SCHEMA: &str = "schema fln.tcb-inventory/1";

/// Render the disclosure: counts, the declared budget, then every item.
pub fn render(inventory: &Inventory, adjacent_budget: usize) -> String {
    let mut text = String::new();
    text.push_str(
        "# The TCB inventory (bead franken_lean-z8j.1.17): every function of the workspace's own\n\
         # crates that the linker keeps reachable from fln_kernel::check, measured from the\n\
         # crates/fln-conformance tcb-probe binary. Do not edit by hand; regenerate with\n\
         #   FLN_TCB_INVENTORY_WRITE=1 cargo test -p fln-conformance --test tcb_inventory\n\
         # which rewrites this file from a fresh measurement and keeps the `budget` line.\n\
         # The test re-measures on every run and fails if this file disagrees in either\n\
         # direction. Limits are in crates/fln-conformance/src/tcb_inventory.rs.\n\
         # `budget` is declared by hand, not measured: the ceiling on functions outside\n\
         # fln_kernel that check may reach, the trusted code the 12 KLOC line covenant on\n\
         # crates/fln-kernel/src does not count. Raising it is a reviewed decision.\n",
    );
    text.push_str(SCHEMA);
    text.push('\n');
    text.push_str("root fln_kernel::check\n");
    for (crate_name, items) in &inventory.items {
        let symbols = inventory.symbols.get(crate_name).map_or(0, BTreeSet::len);
        text.push_str(&format!(
            "crate {crate_name} items={} symbols={symbols}\n",
            items.len()
        ));
    }
    text.push_str(&format!(
        "total items={} adjacent-items={} toolchain-symbols={} non-rust-symbols={}\n",
        inventory.item_count(),
        inventory.adjacent_item_count(),
        inventory.other_symbols,
        inventory.non_rust_symbols,
    ));
    text.push_str(&format!("budget adjacent-items<={adjacent_budget}\n"));
    for (crate_name, items) in &inventory.items {
        for item in items {
            text.push_str(&format!("item {crate_name} {item}\n"));
        }
    }
    text
}

/// The declared budget from a disclosure's `budget adjacent-items<=N` line.
pub fn declared_budget(disclosure: &str) -> Option<usize> {
    disclosure
        .lines()
        .find_map(|line| line.strip_prefix("budget adjacent-items<="))
        .and_then(|value| value.trim().parse().ok())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn demangled(symbol: &str) -> Demangled {
        demangle_v0(symbol).unwrap_or_else(|error| panic!("{symbol}: {error}"))
    }

    #[test]
    fn a_plain_function_names_its_crate_and_item() {
        // fln_kernel::check, as the pinned toolchain mangled it in a measured probe build.
        let d = demangled("_RNvCsgx4vv6SgL4G_10fln_kernel5check");
        assert_eq!(d.full, "fln_kernel::check");
        assert_eq!(d.item, "fln_kernel::check");
        assert_eq!(d.crate_name, "fln_kernel");
    }

    #[test]
    fn a_toolchain_generic_instantiated_with_workspace_types_is_toolchain_code() {
        // `<[CollisionEntry<Name, Arc<ExtensionState>>]>::sort_by::<insert::{closure#0}>`.
        let d = demangled(
            "_RINvMNtCs2UjXZW35p3F_5alloc5sliceSINtNtCs5zN3FMW9pIr_7fln_env4pmap14CollisionEntryNtNtCsd4mFFZWE8Vv_8fln_core4name4NameINtNtB5_4sync3ArcNtNtBB_10extensions14ExtensionStateEE7sort_byNCNvMs2_Bz_INtBz_15CollisionBucketB1i_B1T_E6inserts_0EBB_",
        );
        assert_eq!(d.crate_name, "alloc");
        assert_eq!(d.item, "<[fln_env::pmap::CollisionEntry]>::sort_by");
        assert!(d.full.contains("fln_core::name::Name"), "{}", d.full);
        assert!(
            // `s_` is closure disambiguator 1, as binutils' c++filt also renders it.
            d.full.ends_with("::sort_by::<<fln_env::pmap::CollisionBucket<fln_core::name::Name, alloc::sync::Arc<fln_env::extensions::ExtensionState>>>::insert::{closure#1}>"),
            "{}",
            d.full
        );
    }

    #[test]
    fn nested_closures_with_empty_names_parse_digit_by_digit() {
        // `<bool>::then::<Option<Name>, <RecursorMajorCache>::get::{closure#0}::{closure#0}>`:
        // the two closures' empty identifiers are encoded `00`, two numbers, not one.
        let d = demangled(
            "_RINvMNtCsiUvn3s3DH4V_4core4boolb4thenINtNtB5_6option6OptionNtNtCsd4mFFZWE8Vv_8fln_core4name4NameENCNCNvMs6_NtCsgx4vv6SgL4G_10fln_kernel2tcNtB1H_18RecursorMajorCache3get00EB1J_",
        );
        assert_eq!(d.crate_name, "core");
        assert_eq!(d.item, "<bool>::then");
        assert_eq!(
            d.full,
            "<bool>::then::<core::option::Option<fln_core::name::Name>, \
             <fln_kernel::tc::RecursorMajorCache>::get::{closure#0}::{closure#0}>"
        );
    }

    #[test]
    fn closures_fold_into_the_function_that_contains_them() {
        let parent = Path::Nested {
            namespace: b'v',
            parent: Box::new(Path::Crate("fln_core".to_owned())),
            disambiguator: 0,
            name: "normalize".to_owned(),
        };
        let closure = Path::Nested {
            namespace: b'C',
            parent: Box::new(parent),
            disambiguator: 1,
            name: String::new(),
        };
        assert_eq!(
            render_path(&closure, true),
            "fln_core::normalize::{closure#1}"
        );
        assert_eq!(
            render_path(enclosing_item(&closure), false),
            "fln_core::normalize"
        );
        assert_eq!(defining_crate(&closure), "fln_core");
    }

    #[test]
    fn malformed_symbols_are_refused_not_guessed() {
        for symbol in [
            "_R",
            "_RNv",
            "_RQ",
            "_RNvC5fln_k",
            "_RB_",
            "_RNvCs_3abc3defZ",
        ] {
            assert!(demangle_v0(symbol).is_err(), "{symbol} must not demangle");
        }
        // A back-reference must point strictly backwards.
        assert!(demangle_v0("_RNvB0_3abc").is_err());
        let symbols = vec!["_RNvC3abc".to_owned()];
        assert!(matches!(
            inventory(&symbols),
            Err(InventoryError::Undemangleable { .. })
        ));
    }

    #[test]
    fn a_non_elf_input_is_refused() {
        assert_eq!(
            elf_function_symbols(b"not an elf"),
            Err(InventoryError::NotElf64)
        );
        assert!(matches!(
            elf_function_symbols(b"\x7fELF\x02\x01\x01\0"),
            Err(InventoryError::Truncated(_))
        ));
    }

    #[test]
    fn the_rendered_disclosure_carries_its_budget_and_every_item() {
        let mut inventory = Inventory::default();
        inventory
            .items
            .entry("fln_core".to_owned())
            .or_default()
            .insert("fln_core::level::normalize".to_owned());
        inventory
            .items
            .entry("fln_kernel".to_owned())
            .or_default()
            .insert("fln_kernel::check".to_owned());
        let text = render(&inventory, 7);
        assert_eq!(declared_budget(&text), Some(7));
        assert!(text.contains("total items=2 adjacent-items=1 "), "{text}");
        assert!(
            text.contains("\nitem fln_core fln_core::level::normalize\n"),
            "{text}"
        );
        assert!(
            text.contains("\nitem fln_kernel fln_kernel::check\n"),
            "{text}"
        );
    }
}
