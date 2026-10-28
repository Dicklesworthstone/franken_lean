//! Native implementations of the pin's bootstrap string helpers.
//!
//! `String.Internal` declares these externs in Bootstrap.lean; their pinned
//! exports are in Search.lean (`posOfImpl`), Basic.lean (`offsetOfPosImpl`),
//! and Defs.lean (`pushnImpl`). Positions are UTF-8 byte offsets, while
//! `offsetOfPos` counts Unicode scalars and rounds an interior byte forward.
//! Char and Pos.Raw cross this VM boundary as their checked scalar/Nat payloads.
//!
//! The position-indexed rows port the pin's C runtime directly
//! (`src/runtime/object.cpp`, `lean_string_utf8_get` at 2219,
//! `lean_string_utf8_set` at 2423; `src/include/lean/lean.h`,
//! `lean_string_utf8_get_fast` at 1231, `lean_string_get_byte_fast` at 1238,
//! `lean_string_utf8_next_fast` at 1246). They read the string's own
//! NUL-terminated buffer in place, so one character costs O(1), never a copy.

use super::{
    BigNat, Inconclusive, IntrinsicFailure, IntrinsicResult, Obj, ResourceReason, ResourceUsage,
    Stop, ValueKind, VmRefusal, ensure_nat_bits, expect_arity, extract_utf8, finish_nat_result,
    nat_as_usize, nat_from_big_nat, scalar_code_point, string_value, type_mismatch, value_kind,
    with_nat_view, with_nat_views,
};

// Bound this count-driven allocation before reserving or repeating. This is
// a Golem output-memory ceiling, separate from Nat storage and Lean heartbeats.
const MAX_PUSHN_OUTPUT_BYTES: usize = 16 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Intrinsic {
    PosOf,
    OffsetOfPos,
    Pushn,
    /// `lean_string_utf8_get`: the checked lookup, `'A'` off any boundary.
    Utf8Get,
    /// `lean_string_utf8_get_fast`: the lookup whose proof rules out the end.
    Utf8GetFast,
    /// `lean_string_get_byte_fast`: one byte of the buffer, proof-bounded.
    GetByteFast,
    /// `lean_string_utf8_next_fast`: the advance whose proof rules out the end.
    Utf8NextFast,
    /// `lean_string_utf8_set`: replace the scalar starting at a boundary.
    Utf8Set,
    /// `lean_string_data`: the string's scalars, in order, as a list.
    Data,
    Front,
    PosMin,
    PosSub,
    SubstringToString,
    SubstringDrop,
    SubstringFront,
    SubstringExtract,
    SubstringBeq,
    SubstringIsEmpty,
    SubstringGet,
    SubstringPrev,
}

#[derive(Debug)]
pub(super) enum ResourceError {
    OutputLimit { allowed: u64, observed: u64 },
    Allocation { requested: usize },
}

impl Intrinsic {
    pub(super) fn for_row(row: &str) -> Option<Self> {
        Some(match row {
            "extern:String.Internal.posOf" => Self::PosOf,
            "extern:String.Internal.offsetOfPos" => Self::OffsetOfPos,
            "extern:String.Internal.pushn" => Self::Pushn,
            "extern:String.Internal.get" | "extern:String.Pos.Raw.get" | "extern:String.get" => {
                Self::Utf8Get
            }
            "extern:String.decodeChar" | "extern:String.Pos.Raw.get'" | "extern:String.get'" => {
                Self::Utf8GetFast
            }
            "extern:String.getUTF8Byte"
            | "extern:String.getUtf8Byte"
            | "extern:String.Internal.getUTF8Byte" => Self::GetByteFast,
            "extern:String.Pos.Raw.next'" | "extern:String.next'" | "extern:String.Pos.next" => {
                Self::Utf8NextFast
            }
            "extern:String.Pos.Raw.set" | "extern:String.set" | "extern:String.Pos.set" => {
                Self::Utf8Set
            }
            "extern:String.toList" | "extern:String.data" => Self::Data,
            "extern:String.Internal.front" => Self::Front,
            "extern:String.Pos.Raw.Internal.min" => Self::PosMin,
            "extern:String.Pos.Raw.Internal.sub" => Self::PosSub,
            "extern:Substring.Raw.Internal.toString" => Self::SubstringToString,
            "extern:Substring.Raw.Internal.drop" => Self::SubstringDrop,
            "extern:Substring.Raw.Internal.front" => Self::SubstringFront,
            "extern:Substring.Raw.Internal.extract" => Self::SubstringExtract,
            "extern:Substring.Raw.Internal.beq" => Self::SubstringBeq,
            "extern:Substring.Raw.Internal.isEmpty" => Self::SubstringIsEmpty,
            "extern:Substring.Raw.Internal.get" => Self::SubstringGet,
            "extern:Substring.Raw.Internal.prev" => Self::SubstringPrev,
            _ => return None,
        })
    }

    fn operation(self) -> &'static str {
        match self {
            Self::PosOf => "String.Internal.posOf",
            Self::OffsetOfPos => "String.Internal.offsetOfPos",
            Self::Pushn => "String.Internal.pushn",
            Self::Utf8Get => "String.Pos.Raw.get",
            Self::Utf8GetFast => "String.decodeChar",
            Self::GetByteFast => "String.getUTF8Byte",
            Self::Utf8NextFast => "String.Pos.Raw.next'",
            Self::Utf8Set => "String.Pos.Raw.set",
            Self::Data => "String.toList",
            Self::Front => "String.Internal.front",
            Self::PosMin => "String.Pos.Raw.Internal.min",
            Self::PosSub => "String.Pos.Raw.Internal.sub",
            Self::SubstringToString => "Substring.Raw.Internal.toString",
            Self::SubstringDrop => "Substring.Raw.Internal.drop",
            Self::SubstringFront => "Substring.Raw.Internal.front",
            Self::SubstringExtract => "Substring.Raw.Internal.extract",
            Self::SubstringBeq => "Substring.Raw.Internal.beq",
            Self::SubstringIsEmpty => "Substring.Raw.Internal.isEmpty",
            Self::SubstringGet => "Substring.Raw.Internal.get",
            Self::SubstringPrev => "Substring.Raw.Internal.prev",
        }
    }

    pub(super) fn invoke(
        self,
        row: &str,
        args: &[Obj],
        max_nat_magnitude_bytes: u64,
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        expect_arity(
            row,
            args,
            match self {
                Self::Pushn | Self::Utf8Set | Self::SubstringExtract => 3,
                Self::Data
                | Self::Front
                | Self::SubstringToString
                | Self::SubstringFront
                | Self::SubstringIsEmpty => 1,
                _ => 2,
            },
        )?;
        let operation = self.operation();
        match self {
            Self::Data => return data(&args[0], operation),
            Self::Front => {
                let buffer = string_buffer(&args[0], operation, 0)?;
                let code = if buffer.len() == 1 {
                    CHAR_DEFAULT_VALUE
                } else {
                    utf8_get_core(&buffer[..buffer.len() - 1], 0)
                        .ok_or(VmRefusal::InvalidStringObject)?
                };
                // Bootstrap's exported Lean implementation returns a boxed
                // character, unlike the C runtime's unboxed utf8_get row.
                return Ok(IntrinsicResult::owned(Obj::mk_nat(code as usize)));
            }
            Self::PosMin => {
                let left = with_nat_views(&args[0], &args[1], operation, |a, b| a.ble(b))?;
                return Ok(IntrinsicResult::owned(args[usize::from(!left)].clone_ref()));
            }
            Self::PosSub => {
                let difference = with_nat_views(&args[0], &args[1], operation, |a, b| {
                    ensure_nat_bits(max_nat_magnitude_bytes, u128::from(a.bit_length()))?;
                    Ok::<_, IntrinsicFailure>(a.sub(b))
                })??;
                return finish_nat_result(difference, max_nat_magnitude_bytes);
            }
            Self::SubstringToString
            | Self::SubstringDrop
            | Self::SubstringFront
            | Self::SubstringExtract
            | Self::SubstringBeq
            | Self::SubstringIsEmpty
            | Self::SubstringGet
            | Self::SubstringPrev => {
                return self.invoke_substring(args, max_nat_magnitude_bytes);
            }
            Self::Utf8Get
            | Self::Utf8GetFast
            | Self::GetByteFast
            | Self::Utf8NextFast
            | Self::Utf8Set => return self.invoke_positioned(operation, args),
            Self::PosOf | Self::OffsetOfPos | Self::Pushn => {}
        }
        let text = string_value(&args[0], operation, 0)?;
        let result = match self {
            Self::PosOf => {
                let scalar = scalar_code_point(&args[1], operation, 1)?;
                let character =
                    char::from_u32(scalar).ok_or(VmRefusal::NatOverflow { operation })?;
                // The pin returns rawEndPos when the character is absent.
                Obj::mk_nat(text.find(character).unwrap_or(text.len()))
            }
            Self::OffsetOfPos => {
                let position = nat_as_usize(&args[1], operation, 1)?.unwrap_or(usize::MAX);
                // Count starts strictly before the requested byte. This agrees
                // with advancing from zero until i >= pos, including interior
                // UTF-8 bytes and arbitrary-precision positions past the end.
                let offset = text
                    .char_indices()
                    .take_while(|(start, _)| *start < position)
                    .count();
                Obj::mk_nat(offset)
            }
            Self::Pushn => {
                let scalar = scalar_code_point(&args[1], operation, 1)?;
                let character =
                    char::from_u32(scalar).ok_or(VmRefusal::NatOverflow { operation })?;
                let count = nat_as_usize(&args[2], operation, 2)?;
                if count == Some(0) {
                    // Repeating zero times creates no expanded buffer, even
                    // when the already-existing source exceeds the ceiling.
                    args[0].clone_ref()
                } else {
                    let result = pushn(text, character, count, MAX_PUSHN_OUTPUT_BYTES)
                        .map_err(IntrinsicFailure::StringResource)?;
                    Obj::mk_string(&result)
                }
            }
            Self::Utf8Get
            | Self::Utf8GetFast
            | Self::GetByteFast
            | Self::Utf8NextFast
            | Self::Utf8Set
            | Self::Data
            | Self::Front
            | Self::PosMin
            | Self::PosSub
            | Self::SubstringToString
            | Self::SubstringDrop
            | Self::SubstringFront
            | Self::SubstringExtract
            | Self::SubstringBeq
            | Self::SubstringIsEmpty
            | Self::SubstringGet
            | Self::SubstringPrev => unreachable!("specialized rows return above"),
        };
        // The generated census specifies borrowed operands and an owned result
        // for all three rows, even when a small Nat uses an immediate object.
        Ok(IntrinsicResult::owned(result))
    }

    /// The generated ABI rows: `get`, `get_fast` and `get_byte_fast` return a
    /// `value` scalar; `next_fast` and `set` return an owned object. The
    /// position operand is borrowed and `set`'s character is a `value`.
    fn invoke_positioned(
        self,
        operation: &'static str,
        args: &[Obj],
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        let buffer = string_buffer(&args[0], operation, 0)?;
        // `buffer` ends with the pin's mandatory NUL; `size` excludes it.
        let size = buffer.len() - 1;
        let position = nat_as_usize(&args[1], operation, 1)?;
        let scalar = |value: u32| IntrinsicResult::scalar(Obj::mk_nat(value as usize));
        match self {
            Self::Utf8Get => {
                // A non-scalar Nat, the end, and an interior byte are all `'A'`.
                let code = position
                    .filter(|index| *index < size)
                    .and_then(|index| utf8_get_core(&buffer[..size], index))
                    .unwrap_or(CHAR_DEFAULT_VALUE);
                Ok(scalar(code))
            }
            Self::Utf8GetFast => {
                let index = fast_index(position, size)?;
                Ok(scalar(utf8_get_fast(buffer, index)))
            }
            Self::GetByteFast => {
                let index = fast_index(position, size)?;
                Ok(scalar(u32::from(buffer[index])))
            }
            Self::Utf8NextFast => {
                let index = fast_index(position, size)?;
                let next = index + utf8_fast_width(buffer[index]);
                Ok(IntrinsicResult::owned(Obj::mk_nat(next)))
            }
            Self::Utf8Set => {
                let code = scalar_code_point(&args[2], operation, 2)?;
                let character = char::from_u32(code).ok_or(VmRefusal::NatOverflow { operation })?;
                let Some(index) = position.filter(|index| *index < size) else {
                    return Ok(IntrinsicResult::owned(args[0].clone_ref()));
                };
                let lead = buffer[index];
                let Some(width) = utf8_first_byte_size(lead) else {
                    // The pin leaves the string unchanged at an interior byte.
                    return Ok(IntrinsicResult::owned(args[0].clone_ref()));
                };
                let mut encoded = [0; 4];
                let encoded = character.encode_utf8(&mut encoded).as_bytes();
                // `std::string::replace` clamps the replaced count to the end.
                let end = index.saturating_add(width).min(size);
                let mut bytes = Vec::with_capacity(size - (end - index) + encoded.len());
                bytes.extend_from_slice(&buffer[..index]);
                bytes.extend_from_slice(encoded);
                bytes.extend_from_slice(&buffer[end..size]);
                let text = String::from_utf8(bytes).map_err(|_| VmRefusal::InvalidStringObject)?;
                Ok(IntrinsicResult::owned(Obj::mk_string(&text)))
            }
            _ => {
                unreachable!("only positioned rows reach this port")
            }
        }
    }

    /// Native ports of the exports in Init.Data.String.Substring. The
    /// compiled Raw record has three object fields: String, start Nat, stop
    /// Nat. Pos.Raw's single-field wrapper is erased by the Reference ABI.
    fn invoke_substring(
        self,
        args: &[Obj],
        max_nat_magnitude_bytes: u64,
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        let operation = self.operation();
        let raw = Substring::read(&args[0], operation, 0)?;
        let bytes = string_buffer(&raw.string, operation, 0)?;
        let bytes = &bytes[..bytes.len() - 1];
        let position = |value: &Obj, argument| {
            with_nat_view(value, operation, argument, |value| {
                ensure_nat_bits(max_nat_magnitude_bytes, u128::from(value.bit_length()))?;
                Ok::<_, IntrinsicFailure>(value.to_owned())
            })?
        };
        let start = position(&raw.start, 0)?;
        let stop = position(&raw.stop, 0)?;
        let word = |value: &BigNat| value.to_u64().and_then(|v| usize::try_from(v).ok());
        let sum = |a: &BigNat, b: &BigNat| {
            let bits = if a.is_zero() && b.is_zero() {
                0
            } else {
                u128::from(a.bit_length().max(b.bit_length())) + 1
            };
            ensure_nat_bits(max_nat_magnitude_bytes, bits)?;
            Ok::<_, IntrinsicFailure>(a.add(b))
        };
        let result = match self {
            Self::SubstringToString => {
                // lean_string_utf8_extract tests the ABI tag, not whether
                // the mathematical Nat fits a host usize. On a 64-bit pin,
                // 2^63 is already a heap Nat and selects the whole string.
                let begin = raw.start.is_scalar().then(|| raw.start.unbox());
                let end = raw.stop.is_scalar().then(|| raw.stop.unbox());
                let text = extract_utf8(bytes, begin, end).ok_or(VmRefusal::InvalidStringObject)?;
                Obj::mk_string(&text)
            }
            Self::SubstringIsEmpty => Obj::mk_nat(usize::from(stop <= start)),
            Self::SubstringFront | Self::SubstringGet => {
                let offset = if self == Self::SubstringFront {
                    start
                } else {
                    sum(&start, &position(&args[1], 1)?)?
                };
                // The stop is intentionally not consulted: get/front are
                // relative to the backing String, even for empty substrings.
                let code = word(&offset)
                    .filter(|index| *index < bytes.len())
                    .and_then(|index| utf8_get_core(bytes, index))
                    .unwrap_or(CHAR_DEFAULT_VALUE);
                Obj::mk_nat(code as usize)
            }
            Self::SubstringPrev => {
                let relative = position(&args[1], 1)?;
                if relative.is_zero() {
                    Obj::mk_nat(0)
                } else {
                    let absolute = sum(&start, &relative)?;
                    let previous = match word(&absolute) {
                        Some(index) if index <= bytes.len() => {
                            let mut previous = index.saturating_sub(1);
                            while previous > 0 && utf8_first_byte_size(bytes[previous]).is_none() {
                                previous -= 1;
                            }
                            BigNat::from_u64(previous as u64).sub(&start)
                        }
                        // Outside the buffer the pin decrements the absolute
                        // position once; subtraction of start leaves p - 1.
                        _ => relative.sub(&BigNat::from_u64(1)),
                    };
                    nat_from_big_nat(&previous)
                }
            }
            Self::SubstringDrop => {
                let count = position(&args[1], 1)?;
                let mut advanced = start;
                let mut consumed = 0u64;
                let bound = count.to_u64().unwrap_or(u64::MAX);
                // At most one pass over the backing bytes. Once outside the
                // buffer, next advances by one: finish that suffix with Nat
                // arithmetic, so a huge count never creates a host loop.
                if let Some(mut index) = word(&advanced) {
                    while index < bytes.len() && consumed < bound && advanced != stop {
                        index += utf8_fast_width(bytes[index]);
                        advanced = BigNat::from_u64(index as u64);
                        consumed += 1;
                    }
                }
                if advanced != stop && consumed < bound {
                    let mut remaining = count.sub(&BigNat::from_u64(consumed));
                    if advanced < stop {
                        remaining = remaining.min(stop.sub(&advanced));
                    }
                    advanced = sum(&advanced, &remaining)?;
                }
                Substring::make(
                    raw.string.clone_ref(),
                    nat_from_big_nat(&advanced),
                    raw.stop,
                )
            }
            Self::SubstringExtract => {
                let begin = position(&args[1], 1)?;
                let end = position(&args[2], 2)?;
                if begin >= end {
                    Substring::make(Obj::mk_string(""), Obj::mk_nat(0), Obj::mk_nat(0))
                } else {
                    let begin = sum(&start, &begin)?.min(stop.clone());
                    let end = sum(&start, &end)?.min(stop);
                    Substring::make(
                        raw.string.clone_ref(),
                        nat_from_big_nat(&begin),
                        nat_from_big_nat(&end),
                    )
                }
            }
            Self::SubstringBeq => {
                let other = Substring::read(&args[1], operation, 1)?;
                let other_buffer = string_buffer(&other.string, operation, 1)?;
                let other_bytes = &other_buffer[..other_buffer.len() - 1];
                // repair replaces invalid positions by the backing string's
                // end before the byte-length and contents comparison.
                let repaired = |bytes: &[u8], a: Option<usize>, b: Option<usize>| {
                    let valid = |p: Option<usize>| {
                        p.filter(|p| {
                            *p == bytes.len()
                                || (*p < bytes.len() && utf8_first_byte_size(bytes[*p]).is_some())
                        })
                        .unwrap_or(bytes.len())
                    };
                    let a = valid(a);
                    let b = valid(b);
                    (a, b.saturating_sub(a))
                };
                let (a, size) = repaired(bytes, word(&start), word(&stop));
                let (b, other_size) = repaired(
                    other_bytes,
                    nat_as_usize(&other.start, operation, 1)?,
                    nat_as_usize(&other.stop, operation, 1)?,
                );
                Obj::mk_nat(usize::from(
                    size == other_size && bytes[a..a + size] == other_bytes[b..b + other_size],
                ))
            }
            _ => unreachable!("only substring rows reach this port"),
        };
        Ok(IntrinsicResult::owned(result))
    }
}

struct Substring {
    string: Obj,
    start: Obj,
    stop: Obj,
}

impl Substring {
    fn read(value: &Obj, operation: &'static str, argument: usize) -> Result<Self, VmRefusal> {
        if value_kind(value) != ValueKind::Ctor(0) || value.header().other != 3 {
            return Err(type_mismatch(operation, argument, "Substring.Raw", value));
        }
        let child = |index| {
            value
                .try_ctor_child(index)
                .ok_or_else(|| type_mismatch(operation, argument, "Substring.Raw", value))
        };
        Ok(Self {
            string: child(0)?,
            start: child(1)?,
            stop: child(2)?,
        })
    }

    fn make(string: Obj, start: Obj, stop: Obj) -> Obj {
        Obj::mk_ctor(0, vec![string, start, stop], &[])
    }
}

/// `lean_string_data` (`object.cpp:2171`): every scalar in order, each a
/// `List.cons` (tag 1, head and tail) ending in the fieldless tag-0
/// `List.nil` that compiled code builds. Heads are Nat scalars; the checked
/// adapter rebuilds each Char record around them.
fn data(value: &Obj, operation: &'static str) -> Result<IntrinsicResult, IntrinsicFailure> {
    let text = string_value(value, operation, 0)?;
    let mut list = Obj::mk_ctor(0, Vec::new(), &[]);
    for character in text.chars().rev() {
        list = Obj::mk_ctor(1, vec![Obj::mk_nat(character as usize), list], &[]);
    }
    Ok(IntrinsicResult::owned(list))
}

/// `lean_char_default_value` (`lean.h:1211`): the `Inhabited Char` value `'A'`.
const CHAR_DEFAULT_VALUE: u32 = 'A' as u32;

/// The string's complete NUL-terminated buffer, borrowed in place.
fn string_buffer<'a>(
    value: &'a Obj,
    operation: &'static str,
    argument: usize,
) -> Result<&'a [u8], VmRefusal> {
    if value_kind(value) != ValueKind::String {
        return Err(type_mismatch(operation, argument, "String", value));
    }
    let (size, _, _, bytes) = value
        .try_borrow_string_view()
        .ok_or(VmRefusal::InvalidStringObject)?;
    Ok(&bytes[..size])
}

/// The fast rows read `str[idx]` of the NUL-terminated buffer without a
/// bounds check; their proofs place `idx` strictly before the end. Reading the
/// terminator itself is defined, so `idx = size` keeps the pin's answer. Any
/// later byte, or a Nat beyond the machine word, is undefined behavior at the
/// pin and a typed range refusal here, never a guessed value.
fn fast_index(position: Option<usize>, size: usize) -> Result<usize, VmRefusal> {
    match position {
        Some(index) if index <= size => Ok(index),
        other => Err(VmRefusal::ArrayIndexOutOfBounds {
            index: other.unwrap_or(usize::MAX),
            size: size + 1,
        }),
    }
}

/// `lean_string_utf8_get_core` (`object.cpp:2177`), over the payload without
/// its terminator. Continuation bytes are not inspected, as at the pin.
fn utf8_get_core(bytes: &[u8], index: usize) -> Option<u32> {
    let size = bytes.len();
    let lead = u32::from(bytes[index]);
    let at = |offset: usize| u32::from(bytes[index + offset]);
    if lead & 0x80 == 0 {
        return Some(lead);
    }
    if lead & 0xe0 == 0xc0 && index + 1 < size {
        let result = ((lead & 0x1f) << 6) | (at(1) & 0x3f);
        if result >= 0x80 {
            return Some(result);
        }
    }
    if lead & 0xf0 == 0xe0 && index + 2 < size {
        let result = ((lead & 0x0f) << 12) | ((at(1) & 0x3f) << 6) | (at(2) & 0x3f);
        if result >= 0x800 && !(0xD800..=0xDFFF).contains(&result) {
            return Some(result);
        }
    }
    if lead & 0xf8 == 0xf0 && index + 3 < size {
        let result =
            ((lead & 0x07) << 18) | ((at(1) & 0x3f) << 12) | ((at(2) & 0x3f) << 6) | (at(3) & 0x3f);
        if (0x10000..=0x10FFFF).contains(&result) {
            return Some(result);
        }
    }
    None
}

/// `lean_string_utf8_get_fast` (`lean.h:1231`) with its cold half
/// (`object.cpp:2247`): an ASCII byte, including the terminator, is its own
/// scalar; the cold decoder's bounds run over the buffer including the NUL.
fn utf8_get_fast(buffer: &[u8], index: usize) -> u32 {
    let lead = buffer[index];
    if lead & 0x80 == 0 {
        return u32::from(lead);
    }
    utf8_get_core(buffer, index).unwrap_or(CHAR_DEFAULT_VALUE)
}

/// `lean_string_utf8_next_fast` and its cold half (`object.cpp:2348`): an
/// invalid lead byte, including a continuation byte, advances by one.
fn utf8_fast_width(lead: u8) -> usize {
    utf8_first_byte_size(lead).unwrap_or(1)
}

/// `get_utf8_first_byte_opt` (`utf8.cpp:147`): the width a lead byte declares.
fn utf8_first_byte_size(lead: u8) -> Option<usize> {
    if lead & 0x80 == 0 {
        Some(1)
    } else if lead & 0xe0 == 0xc0 {
        Some(2)
    } else if lead & 0xf0 == 0xe0 {
        Some(3)
    } else if lead & 0xf8 == 0xf0 {
        Some(4)
    } else {
        None
    }
}

fn pushn(
    mut text: String,
    character: char,
    count: Option<usize>,
    limit: usize,
) -> Result<String, ResourceError> {
    let requested = count
        .map(|count| text.len() as u128 + count as u128 * character.len_utf8() as u128)
        .unwrap_or(u128::MAX);
    if requested > limit as u128 {
        return Err(ResourceError::OutputLimit {
            allowed: limit as u64,
            observed: u64::try_from(requested).unwrap_or(u64::MAX),
        });
    }
    let requested = requested as usize;
    text.try_reserve_exact(requested - text.len())
        .map_err(|_| ResourceError::Allocation { requested })?;
    for _ in 0..count.expect("a bounded output has a machine-sized repetition count") {
        text.push(character);
    }
    Ok(text)
}

pub(super) fn resource_exhausted(error: ResourceError, location: &str) -> Stop {
    match error {
        ResourceError::OutputLimit { allowed, observed } => Stop::Inconclusive(
            Inconclusive::resource(ResourceUsage {
                reason: ResourceReason::Memory {
                    limit_bytes: allowed,
                },
                allowed,
                observed,
            })
            .with_progress(format!("String.Internal.pushn output at {location}")),
        ),
        ResourceError::Allocation { requested } => {
            Stop::Inconclusive(Inconclusive::dependency_unavailable(format!(
                "host buffer allocation for String.Internal.pushn: requested {requested} bytes at {location}"
            )))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn repeated_character_budget_counts_utf8_bytes_before_allocation() {
        assert_eq!(pushn("é".to_owned(), '🦀', Some(2), 10).unwrap(), "é🦀🦀");
        assert!(matches!(
            pushn("é".to_owned(), '🦀', Some(2), 9),
            Err(ResourceError::OutputLimit {
                allowed: 9,
                observed: 10,
            })
        ));
        assert_eq!(pushn(String::new(), '\0', Some(0), 0).unwrap(), "");
        assert!(matches!(
            pushn(String::new(), '\0', Some(1), 0),
            Err(ResourceError::OutputLimit {
                allowed: 0,
                observed: 1,
            })
        ));
        for count in [None, Some(usize::MAX)] {
            assert!(matches!(
                pushn("prefix".to_owned(), '🦀', count, MAX_PUSHN_OUTPUT_BYTES),
                Err(ResourceError::OutputLimit {
                    allowed,
                    observed: u64::MAX,
                }) if allowed == MAX_PUSHN_OUTPUT_BYTES as u64
            ));
        }
    }
}
