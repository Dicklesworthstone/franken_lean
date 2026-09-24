//! Fresh `ModuleData` emission with persistent environment-extension values.
//!
//! Extension entries are typed, immutable runtime object graphs, not process
//! addresses or unvalidated serialized handles. The shared compactor owns their
//! representation. Sharing is retained across entries and blocks; distinct
//! allocations are not interned. Block and entry order are caller order.
//!
//! This encodes persistence, not the meaning or activation of an extension.
//! Closures and mutable/runtime cells are refused. Reference byte identity,
//! extension-specific schemas, and native-library relocation remain separate
//! obligations of bead `franken_lean-0nz`.

use std::collections::{HashMap, HashSet};

use fln_core::name::{LeafView, Name};
use fln_rt::abi;
use fln_rt::obj::Obj;
use fln_rt::region::{audit, compact, materialize, parse_olean_envelope};

use crate::format;
use crate::write::{
    EncodedModule, ModuleWriteInput, OleanWriteHeader, WriteBudget, WriteError, WriteResource,
    encode_module,
};

type Result<T> = std::result::Result<T, WriteError>;

/// One named persistent extension and its entries, in emission order.
///
/// Entry graphs may contain scalars, constructors, arrays, scalar arrays,
/// strings, and big integers. They must be acyclic. Closures, references,
/// thunks, tasks, promises, and external objects are not persistent data here.
#[derive(Clone, Copy)]
pub struct ModuleExtensionInput<'a> {
    pub name: &'a Name,
    pub entries: &'a [Obj],
}

impl std::fmt::Debug for ModuleExtensionInput<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ModuleExtensionInput")
            .field("name", &self.name)
            .field("entries", &self.entries.len())
            .finish()
    }
}

fn contract(what: &'static str) -> WriteError {
    WriteError::Contract { what }
}

fn aligned(bytes: u64) -> Result<u64> {
    bytes
        .checked_add(7)
        .map(|n| n / 8 * 8)
        .ok_or_else(|| contract("extension object size overflows"))
}

fn extent(fixed: u64, count: usize, width: u64) -> Result<u64> {
    (count as u64)
        .checked_mul(width)
        .and_then(|n| n.checked_add(fixed))
        .ok_or_else(|| contract("extension object extent overflows"))
}

struct Builder {
    budget: WriteBudget,
    objects: u64,
    bytes: u64,
    // false = on the current DFS path; true = fully checked. A mere visited
    // set would accept cycles which the post-order compactor cannot finish.
    visited: HashMap<usize, bool>,
    names: HashMap<Name, Obj>,
    strings: HashMap<String, Obj>,
}

impl Builder {
    fn new(budget: WriteBudget) -> Self {
        Self {
            budget,
            objects: 0,
            bytes: 0,
            visited: HashMap::new(),
            names: HashMap::new(),
            strings: HashMap::new(),
        }
    }

    fn charge(&mut self, bytes: u64) -> Result<()> {
        let objects = self
            .objects
            .checked_add(1)
            .ok_or_else(|| contract("extension object count overflows"))?;
        if objects > self.budget.max_objects {
            return Err(WriteError::Budget {
                resource: WriteResource::Objects,
                limit: self.budget.max_objects,
                attempted: objects,
            });
        }
        let total = self
            .bytes
            .checked_add(bytes)
            .ok_or_else(|| contract("extension byte count overflows"))?;
        if total > self.budget.max_bytes {
            return Err(WriteError::Budget {
                resource: WriteResource::Bytes,
                limit: self.budget.max_bytes,
                attempted: total,
            });
        }
        self.objects = objects;
        self.bytes = total;
        Ok(())
    }

    /// Validate and size caller-owned graphs without cloning their heap
    /// structure. Charge an object before scheduling its children.
    fn visit(&mut self, root: &Obj) -> Result<()> {
        let mut stack = vec![(root.clone_ref(), false)];
        while let Some((object, exit)) = stack.pop() {
            if object.is_scalar() {
                continue;
            }
            let identity = object.identity_token();
            if exit {
                self.visited.insert(identity, true);
                continue;
            }
            match self.visited.get(&identity) {
                Some(true) => continue,
                Some(false) => return Err(contract("cyclic extension object graph")),
                None => {}
            }
            // Refuse an exhausted object budget before copying a leaf view.
            if self.objects >= self.budget.max_objects {
                return Err(WriteError::Budget {
                    resource: WriteResource::Objects,
                    limit: self.budget.max_objects,
                    attempted: self.objects.saturating_add(1),
                });
            }
            let header = object.header();
            let tag = header.tag;
            let mut children = 0;
            let bytes = if tag <= abi::TAG_MAX_CTOR_TAG {
                children = usize::from(header.other);
                let minimum = extent(8, children, 8)?;
                let size = u64::from(header.cs_sz);
                if size < minimum
                    || !size.is_multiple_of(8)
                    || children >= abi::MAX_CTOR_FIELDS
                    || size - minimum >= abi::MAX_CTOR_SCALARS_SIZE as u64
                {
                    return Err(contract("invalid extension constructor shape"));
                }
                size
            } else if tag == abi::TAG_ARRAY {
                children = object
                    .try_array_view()
                    .ok_or_else(|| contract("invalid extension array"))?
                    .0;
                extent(24, children, 8)?
            } else if tag == abi::TAG_STRING {
                let (size, _, _, _) = object
                    .try_string_view()
                    .ok_or_else(|| contract("invalid extension string"))?;
                aligned(extent(32, size, 1)?)?
            } else if tag == abi::TAG_SCALAR_ARRAY {
                let (_, _, _, data) = object
                    .try_sarray_view()
                    .ok_or_else(|| contract("invalid extension scalar array"))?;
                aligned(extent(24, data.len(), 1)?)?
            } else if tag == abi::TAG_MPZ {
                let (_, _, limbs) = object
                    .try_mpz_view()
                    .ok_or_else(|| contract("invalid extension big integer"))?;
                let size = extent(24, limbs.len(), 8)?;
                if size > u64::from(u16::MAX) {
                    return Err(contract(
                        "extension big integer exceeds the small-object ABI",
                    ));
                }
                size
            } else {
                return Err(WriteError::Unsupported {
                    what: "extension entry contains a closure, runtime cell, or external object",
                });
            };
            self.charge(bytes)?;
            self.visited.insert(identity, false);
            stack.push((object.clone_ref(), true));
            for index in (0..children).rev() {
                let child = if tag == abi::TAG_ARRAY {
                    object.array_child(index)
                } else {
                    object
                        .try_ctor_child(index)
                        .ok_or_else(|| contract("extension constructor child is absent"))?
                };
                stack.push((child, false));
            }
        }
        Ok(())
    }

    fn string(&mut self, text: &str) -> Result<Obj> {
        if let Some(object) = self.strings.get(text) {
            return Ok(object.clone_ref());
        }
        self.charge(aligned(extent(33, text.len(), 1)?)?)?;
        let object = Obj::mk_string(text);
        self.strings.insert(text.to_owned(), object.clone_ref());
        Ok(object)
    }

    fn name(&mut self, name: &Name) -> Result<Obj> {
        let mut chain = Vec::new();
        let mut cursor = name.clone();
        let mut parent = loop {
            if cursor.is_anonymous() {
                break Obj::mk_nat(0);
            }
            if let Some(object) = self.names.get(&cursor) {
                break object.clone_ref();
            }
            chain.push(cursor.clone());
            cursor = cursor.parent();
        };
        for component in chain.into_iter().rev() {
            let (tag, value) = match component.leaf_view() {
                LeafView::Anonymous => return Err(contract("anonymous extension Name component")),
                LeafView::Str(text) => (1, self.string(text)?),
                LeafView::Num(number) => {
                    if component.component_overflowed() {
                        return Err(WriteError::Unsupported {
                            what: "extension Name.num component wider than u64",
                        });
                    }
                    let value = if let Ok(small) = usize::try_from(number)
                        && small <= usize::MAX >> 1
                    {
                        Obj::mk_nat(small)
                    } else {
                        self.charge(32)?;
                        Obj::mk_mpz(&[number], false)
                    };
                    (2, value)
                }
            };
            self.charge(32)?;
            parent = Obj::mk_ctor(tag, vec![parent, value], &component.hash().to_le_bytes());
            self.names.insert(component, parent.clone_ref());
        }
        Ok(parent)
    }

    fn array(&mut self, children: Vec<Obj>) -> Result<Obj> {
        self.charge(extent(24, children.len(), 8)?)?;
        Ok(Obj::mk_array(children))
    }
}

fn subtract_budget(limit: u64, reserved: u64, resource: WriteResource) -> Result<u64> {
    limit.checked_sub(reserved).ok_or(WriteError::Budget {
        resource,
        limit,
        attempted: reserved,
    })
}

/// Encode a complete module with nonempty persistent extension data.
///
/// The same budget covers declarations, metadata, and extension graphs. Shared
/// entry objects are charged once across all blocks. Empty `extensions` delegates
/// exactly to [`encode_module`]. Duplicate extension names are refused rather
/// than merged or reordered. This does not register or execute the extensions.
pub fn encode_module_with_extensions(
    input: ModuleWriteInput<'_>,
    extensions: &[ModuleExtensionInput<'_>],
    header: OleanWriteHeader<'_>,
    budget: WriteBudget,
) -> Result<EncodedModule> {
    if extensions.is_empty() {
        return encode_module(input, header, budget);
    }
    let mut builder = Builder::new(budget);
    let mut names = HashSet::new();
    let mut blocks = Vec::new();
    for extension in extensions {
        if !names.insert(extension.name.clone()) {
            return Err(contract("duplicate persistent extension name"));
        }
        for entry in extension.entries {
            builder.visit(entry)?;
        }
        let name = builder.name(extension.name)?;
        let entries = builder.array(extension.entries.iter().map(Obj::clone_ref).collect())?;
        builder.charge(24)?;
        blocks.push(Obj::mk_ctor(0, vec![name, entries], &[]));
    }
    let entries = builder.array(blocks)?;

    // The basic writer already charges one empty entries array (24 bytes).
    // Replace that object, not the module's declaration or metadata budgets.
    let extra_objects = builder
        .objects
        .checked_sub(1)
        .ok_or_else(|| contract("extension entries array missing from the object census"))?;
    let extra_bytes = builder
        .bytes
        .checked_sub(24)
        .ok_or_else(|| contract("extension entries array missing from the byte census"))?;
    let basic_budget = WriteBudget {
        max_objects: subtract_budget(budget.max_objects, extra_objects, WriteResource::Objects)?,
        max_bytes: subtract_budget(budget.max_bytes, extra_bytes, WriteResource::Bytes)?,
    };
    let mut encoded = encode_module(input, header, basic_budget).map_err(|error| match error {
        WriteError::Budget {
            resource,
            attempted,
            ..
        } => {
            let (limit, reserved) = match resource {
                WriteResource::Objects => (budget.max_objects, extra_objects),
                WriteResource::Bytes => (budget.max_bytes, extra_bytes),
            };
            WriteError::Budget {
                resource,
                limit,
                attempted: attempted.saturating_add(reserved),
            }
        }
        error => error,
    })?;
    let file_bytes = encoded
        .report
        .file_bytes
        .checked_add(extra_bytes)
        .ok_or_else(|| contract("extended module byte count overflows"))?;
    let objects = encoded
        .report
        .runtime_objects
        .checked_add(extra_objects)
        .ok_or_else(|| contract("extended module object count overflows"))?;
    // The shared compactor uses base-plus-offset arithmetic. Validate the
    // entire expanded mapped range before giving it any objects to compact.
    header
        .base_addr
        .checked_add(file_bytes)
        .ok_or_else(|| contract("extended module mapped address range overflows"))?;

    let envelope = parse_olean_envelope(&encoded.bytes)?;
    let payload_end = envelope.payload_offset + envelope.payload_len;
    let original = materialize(
        &encoded.bytes[envelope.payload_offset..payload_end],
        envelope.payload_base(),
    )?;
    let fields: Vec<&str> = format::MODULE_DATA_FIELDS
        .iter()
        .filter(|field| field.lean_type != "Bool")
        .map(|field| field.name)
        .collect();
    if fields
        != [
            "imports",
            "constNames",
            "constants",
            "extraConstNames",
            "entries",
        ]
    {
        return Err(contract("generated ModuleData object-field layout changed"));
    }
    let root_header = original.header();
    if root_header.tag != 0 || usize::from(root_header.other) != fields.len() {
        return Err(contract(
            "basic writer returned an unexpected ModuleData root",
        ));
    }
    let root_offset = usize::try_from(encoded.root - header.base_addr)
        .map_err(|_| contract("ModuleData root offset exceeds the host address space"))?;
    let scalar_start = root_offset + 8 + 8 * fields.len();
    let scalar_end = root_offset + usize::from(root_header.cs_sz);
    let scalars = encoded
        .bytes
        .get(scalar_start..scalar_end)
        .ok_or_else(|| contract("ModuleData scalar tail is outside the file"))?;
    let mut children = Vec::new();
    for index in 0..fields.len() {
        children.push(
            original
                .try_ctor_child(index)
                .ok_or_else(|| contract("ModuleData object field is absent"))?,
        );
    }
    if children[4].try_array_view().is_none_or(|(len, _)| len != 0) {
        return Err(contract(
            "basic writer did not provide an empty entries array",
        ));
    }
    children[4] = entries;
    let root = Obj::mk_ctor(0, children, scalars);
    let payload = compact(&root, envelope.payload_base())?;
    let checked = audit(&payload, envelope.payload_base())?;
    let framing = if envelope.version == 3 { 8 } else { 0 };
    if checked.objects != objects
        || envelope.payload_offset as u64 + payload.len() as u64 + framing != file_bytes
    {
        return Err(contract(
            "extended module census differs from the shared compactor",
        ));
    }
    encoded.bytes.truncate(envelope.payload_offset);
    if envelope.version == 3 {
        encoded.bytes[format::OLEAN_HEADER_SIZE..envelope.payload_offset]
            .copy_from_slice(&(payload.len() as u64).to_le_bytes());
    }
    encoded.bytes.extend_from_slice(&payload);
    if envelope.version == 3 {
        encoded.bytes.extend_from_slice(&0u32.to_le_bytes());
        encoded.bytes.extend_from_slice(&0u32.to_le_bytes());
    }
    encoded.root = checked.root;
    encoded.report.runtime_objects = objects;
    encoded.report.file_bytes = file_bytes;
    Ok(encoded)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decl::DeclDecoder;
    use crate::region::{OleanView, WalkBudget};
    use fln_core::expr::Expr;
    use fln_core::level::Level;
    use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};
    use fln_rt::region::SubgraphCapture;

    fn name(text: &str) -> Name {
        Name::str(Name::anonymous(), text)
    }

    fn header(version: u8) -> OleanWriteHeader<'static> {
        OleanWriteHeader {
            version,
            flags: 1,
            lean_version: "4.32.0",
            githash: "0123456789abcdef0123456789abcdef01234567",
            base_addr: 0x20_000,
        }
    }

    fn empty_input() -> ModuleWriteInput<'static> {
        ModuleWriteInput {
            is_module: false,
            imports: &[],
            constants: &[],
            extra_const_names: &[],
        }
    }

    fn entry_arrays(encoded: &EncodedModule, expected_names: &[Name]) -> Vec<Vec<u64>> {
        let view = OleanView::parse(&encoded.bytes).expect("envelope");
        let root = view.deref(encoded.root).expect("root");
        let blocks = view
            .deref(view.read_u64(root + 8 + 4 * 8).expect("entries slot"))
            .expect("entries array");
        assert_eq!(
            view.read_u64(blocks + 8).expect("block count"),
            expected_names.len() as u64
        );
        let mut result = Vec::new();
        for (index, expected) in expected_names.iter().enumerate() {
            let pair = view
                .deref(view.read_u64(blocks + 24 + 8 * index as u64).expect("pair"))
                .expect("pair object");
            let decoded = DeclDecoder::new(&view, WalkBudget::default())
                .decode_name(view.read_u64(pair + 8).expect("name"))
                .expect("extension name");
            assert_eq!(&decoded, expected);
            let entries = view
                .deref(view.read_u64(pair + 16).expect("entry array"))
                .expect("entry array object");
            let count = view.read_u64(entries + 8).expect("entry count");
            result.push(
                (0..count)
                    .map(|i| view.read_u64(entries + 24 + 8 * i).expect("entry"))
                    .collect(),
            );
        }
        result
    }

    #[test]
    fn nonempty_extensions_roundtrip_with_declarations_in_both_versions() {
        let shared = Obj::mk_string("shared extension value");
        let pair = Obj::mk_ctor(7, vec![shared.clone_ref(), shared.clone_ref()], &[0x55; 8]);
        let first = vec![
            pair,
            Obj::mk_sarray(1, &[0, 1, 0xff]),
            Obj::mk_mpz(&[u64::MAX, 3], false),
        ];
        let second = vec![shared.clone_ref(), shared];
        let names = vec![
            name("extension.first"),
            Name::num(name("extension.second"), u64::MAX),
        ];
        let extensions = [
            ModuleExtensionInput {
                name: &names[0],
                entries: &first,
            },
            ModuleExtensionInput {
                name: &names[1],
                entries: &second,
            },
        ];
        let constants = [ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: name("proofInput"),
                level_params: vec![],
                type_: Expr::sort(Level::zero()),
            },
            is_unsafe: false,
        })];
        for version in [2, 3] {
            let input = ModuleWriteInput {
                constants: &constants,
                ..empty_input()
            };
            let encoded = encode_module_with_extensions(
                input,
                &extensions,
                header(version),
                WriteBudget::default(),
            )
            .expect("extended module");
            let view = OleanView::parse(&encoded.bytes).expect("view");
            let report = view.shared_audit().expect("independent region audit");
            assert_eq!(report.objects, encoded.report.runtime_objects);
            assert_eq!(encoded.bytes.len() as u64, encoded.report.file_bytes);
            assert_eq!(
                DeclDecoder::new(&view, WalkBudget::default())
                    .decode_module_constants()
                    .expect("constants"),
                constants
            );
            assert_eq!(
                view.module_data(WalkBudget::default())
                    .expect("ModuleData")
                    .extensions
                    .len(),
                2
            );
            let arrays = entry_arrays(&encoded, &names);
            assert_eq!(arrays[0].len(), 3);
            assert_eq!(arrays[1].len(), 2);
            assert_eq!(
                arrays[1][0], arrays[1][1],
                "shared entries retain allocation identity"
            );
            let envelope = parse_olean_envelope(&encoded.bytes).expect("envelope");
            let payload = &encoded.bytes
                [envelope.payload_offset..envelope.payload_offset + envelope.payload_len];
            let capture =
                SubgraphCapture::new(payload, envelope.payload_base()).expect("capture index");
            for (pointers, entries) in arrays.iter().zip([&first, &second]) {
                for (&pointer, expected) in pointers.iter().zip(entries) {
                    let captured = capture.capture(pointer, 1 << 20).expect("entry capture");
                    let decoded = materialize(&captured, 0).expect("entry graph");
                    assert_eq!(
                        compact(&decoded, 0).expect("decoded graph"),
                        compact(expected, 0).expect("input graph")
                    );
                }
            }
            assert_eq!(
                crate::rebuild::rebuild(&encoded.bytes).expect("rebuild").0,
                encoded.bytes
            );
            let repeated = encode_module_with_extensions(
                input,
                &extensions,
                header(version),
                WriteBudget::default(),
            )
            .expect("repeat emission");
            assert_eq!(
                repeated.bytes, encoded.bytes,
                "fresh emission is deterministic"
            );
        }
    }

    #[test]
    fn exact_whole_module_budgets_include_extensions() {
        let name = name("budgeted");
        let entries = [Obj::mk_string("payload")];
        let extensions = [ModuleExtensionInput {
            name: &name,
            entries: &entries,
        }];
        for version in [2, 3] {
            let encoded = encode_module_with_extensions(
                empty_input(),
                &extensions,
                header(version),
                WriteBudget::default(),
            )
            .expect("baseline");
            let exact = WriteBudget {
                max_objects: encoded.report.runtime_objects,
                max_bytes: encoded.report.file_bytes,
            };
            assert_eq!(
                encode_module_with_extensions(empty_input(), &extensions, header(version), exact)
                    .expect("exact budget")
                    .bytes,
                encoded.bytes
            );
            for (budget, resource) in [
                (
                    WriteBudget {
                        max_objects: exact.max_objects - 1,
                        ..exact
                    },
                    WriteResource::Objects,
                ),
                (
                    WriteBudget {
                        max_bytes: exact.max_bytes - 1,
                        ..exact
                    },
                    WriteResource::Bytes,
                ),
            ] {
                assert!(matches!(
                    encode_module_with_extensions(empty_input(), &extensions, header(version), budget),
                    Err(WriteError::Budget { resource: actual, .. }) if actual == resource
                ));
            }
        }
    }

    #[test]
    fn no_extensions_preserve_the_basic_writer_bytes_and_report() {
        for version in [2, 3] {
            let basic = encode_module(empty_input(), header(version), WriteBudget::default())
                .expect("basic");
            let extended = encode_module_with_extensions(
                empty_input(),
                &[],
                header(version),
                WriteBudget::default(),
            )
            .expect("empty extensions");
            assert_eq!(extended, basic);
        }
    }

    #[test]
    fn duplicate_extension_names_are_not_silently_merged() {
        let name = name("duplicate");
        let extensions = [
            ModuleExtensionInput {
                name: &name,
                entries: &[],
            },
            ModuleExtensionInput {
                name: &name,
                entries: &[],
            },
        ];
        assert!(matches!(
            encode_module_with_extensions(
                empty_input(),
                &extensions,
                header(3),
                WriteBudget::default()
            ),
            Err(WriteError::Contract {
                what: "duplicate persistent extension name"
            })
        ));
    }

    #[test]
    fn mutable_runtime_cells_refuse_before_compaction() {
        let name = name("notPersistent");
        let entries = [Obj::mk_ref(Obj::mk_nat(7))];
        let extensions = [ModuleExtensionInput {
            name: &name,
            entries: &entries,
        }];
        assert!(matches!(
            encode_module_with_extensions(
                empty_input(),
                &extensions,
                header(3),
                WriteBudget::default()
            ),
            Err(WriteError::Unsupported { .. })
        ));
    }

    #[test]
    fn expanded_mapped_address_range_is_checked_before_compaction() {
        let name = name("large");
        let entries = [Obj::mk_string(&"x".repeat(70_000))];
        let extensions = [ModuleExtensionInput {
            name: &name,
            entries: &entries,
        }];
        let header = OleanWriteHeader {
            base_addr: !(format::REGION_ALIGN as u64 - 1),
            ..header(3)
        };
        assert!(matches!(
            encode_module_with_extensions(
                empty_input(),
                &extensions,
                header,
                WriteBudget::default()
            ),
            Err(WriteError::Contract {
                what: "extended module mapped address range overflows"
            })
        ));
    }
}
