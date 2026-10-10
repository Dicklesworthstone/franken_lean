//! Native implementations of the pin's bootstrap string helpers.
//!
//! `String.Internal` declares these externs in Bootstrap.lean; their pinned
//! exports are in Search.lean (`posOfImpl`), Basic.lean (`offsetOfPosImpl`),
//! and Defs.lean (`pushnImpl`). Positions are UTF-8 byte offsets, while
//! `offsetOfPos` counts Unicode scalars and rounds an interior byte forward.
//! Char and Pos.Raw cross this VM boundary as their checked scalar/Nat payloads.

use super::{
    Inconclusive, IntrinsicFailure, IntrinsicResult, Obj, ResourceReason, ResourceUsage, Stop,
    VmRefusal, expect_arity, nat_as_usize, scalar_code_point, string_value,
};

// Bound this count-driven allocation before reserving or repeating. This is
// a Golem output-memory ceiling, separate from Nat storage and Lean heartbeats.
const MAX_PUSHN_OUTPUT_BYTES: usize = 16 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Intrinsic {
    PosOf,
    OffsetOfPos,
    Pushn,
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
            _ => return None,
        })
    }

    pub(super) fn invoke(
        self,
        row: &str,
        args: &[Obj],
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        expect_arity(row, args, if self == Self::Pushn { 3 } else { 2 })?;
        let operation = match self {
            Self::PosOf => "String.Internal.posOf",
            Self::OffsetOfPos => "String.Internal.offsetOfPos",
            Self::Pushn => "String.Internal.pushn",
        };
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
        };
        // The generated census specifies borrowed operands and an owned result
        // for all three rows, even when a small Nat uses an immediate object.
        Ok(IntrinsicResult::owned(result))
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
