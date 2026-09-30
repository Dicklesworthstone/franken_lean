//! Checker-owned division. Every limb walk and allocation uses the caller's
//! numeric budget; incomplete arithmetic never becomes a numeric verdict.

use super::*;

fn fixed_effective_len(value: &[u64], control: &mut Control<'_>) -> Result<usize, Halt> {
    let mut length = value.len();
    while length != 0 {
        control.step()?;
        if value[length - 1] != 0 {
            break;
        }
        length -= 1;
    }
    Ok(length)
}

fn compare_fixed(left: &[u64], right: &[u64], control: &mut Control<'_>) -> Result<Ordering, Halt> {
    let left_len = fixed_effective_len(left, control)?;
    control.step()?;
    match left_len.cmp(&right.len()) {
        Ordering::Equal => {}
        order => return Ok(order),
    }
    for index in (0..left_len).rev() {
        control.step()?;
        match left[index].cmp(&right[index]) {
            Ordering::Equal => {}
            order => return Ok(order),
        }
    }
    Ok(Ordering::Equal)
}

fn subtract_fixed(left: &mut [u64], right: &[u64], control: &mut Control<'_>) -> Result<(), Halt> {
    let mut borrow = false;
    for (index, left_limb) in left.iter_mut().enumerate() {
        control.step()?;
        let right_limb = right.get(index).copied().unwrap_or(0);
        let (partial, first_borrow) = left_limb.overflowing_sub(right_limb);
        let (value, second_borrow) = partial.overflowing_sub(u64::from(borrow));
        *left_limb = value;
        borrow = first_borrow || second_borrow;
    }
    if borrow {
        Err(Halt::Fault(NatFault::ArithmeticInvariant {
            task: control.task,
        }))
    } else {
        Ok(())
    }
}

fn bit_length(value: &[u64], control: &mut Control<'_>) -> Result<usize, Halt> {
    if value.is_empty() {
        return Ok(0);
    }
    control.step()?;
    let high_bits = 64usize - value[value.len() - 1].leading_zeros() as usize;
    value
        .len()
        .checked_sub(1)
        .and_then(|limbs| limbs.checked_mul(64))
        .and_then(|bits| bits.checked_add(high_bits))
        .ok_or({
            Halt::Stop(NatStop::OutputSizeOverflow {
                task: control.task,
                progress: control.progress,
            })
        })
}

// With remainder < divisor, each two-word numerator is strictly less than
// divisor * 2^64. Its quotient therefore fits one word, including when the
// divisor is u64::MAX. No primary-kernel arithmetic is used here.
fn div_rem_word(
    dividend: &[u64],
    divisor: u64,
    keep_quotient: bool,
    control: &mut Control<'_>,
) -> Result<(Option<Vec<u64>>, Vec<u64>), Halt> {
    let mut quotient = if keep_quotient {
        Some(zeroed(dividend.len(), control)?)
    } else {
        None
    };
    let mut remainder = 0_u64;
    for index in (0..dividend.len()).rev() {
        control.step()?;
        let numerator = (u128::from(remainder) << 64) | u128::from(dividend[index]);
        if let Some(quotient) = &mut quotient {
            quotient[index] = (numerator / u128::from(divisor)) as u64;
        }
        remainder = (numerator % u128::from(divisor)) as u64;
    }
    let quotient = match quotient {
        Some(quotient) => Some(trim(quotient, control)?),
        None => None,
    };
    let mut rest = control.reserve(usize::from(remainder != 0))?;
    if remainder != 0 {
        control.step()?;
        rest.push(remainder);
    }
    Ok((quotient, rest))
}

fn power_of_two_shift(
    divisor: &[u64],
    control: &mut Control<'_>,
) -> Result<Option<(usize, u32)>, Halt> {
    control.step()?;
    let Some((&high, low)) = divisor.split_last() else {
        return Ok(None);
    };
    if !high.is_power_of_two() {
        return Ok(None);
    }
    for word in low {
        control.step()?;
        if *word != 0 {
            return Ok(None);
        }
    }
    Ok(Some((low.len(), high.trailing_zeros())))
}

// Splitting at a bit boundary gives exactly n = q * 2^k + r, r < 2^k.
// The caller has established dividend > divisor, so the boundary is in range.
// In particular, modulo never allocates or computes the discarded quotient.
fn div_rem_power_of_two(
    dividend: &[u64],
    word_shift: usize,
    bit_shift: u32,
    keep_quotient: bool,
    control: &mut Control<'_>,
) -> Result<(Option<Vec<u64>>, Vec<u64>), Halt> {
    let quotient = if keep_quotient {
        let mut quotient = control.reserve(dividend.len() - word_shift)?;
        for index in word_shift..dividend.len() {
            control.step()?;
            let mut word = dividend[index] >> bit_shift;
            if bit_shift != 0 && index + 1 < dividend.len() {
                word |= dividend[index + 1] << (64 - bit_shift);
            }
            quotient.push(word);
        }
        Some(trim(quotient, control)?)
    } else {
        None
    };
    let mut remainder = control.reserve(word_shift + usize::from(bit_shift != 0))?;
    for word in &dividend[..word_shift] {
        control.step()?;
        remainder.push(*word);
    }
    if bit_shift != 0 {
        control.step()?;
        remainder.push(dividend[word_shift] & ((1_u64 << bit_shift) - 1));
    }
    Ok((quotient, trim(remainder, control)?))
}

pub(super) fn div_rem_limbs(
    dividend: &[u64],
    divisor: &[u64],
    keep_quotient: bool,
    control: &mut Control<'_>,
) -> Result<(Option<Vec<u64>>, Vec<u64>), Halt> {
    if divisor.is_empty() {
        let remainder = copy_limbs(dividend, control)?;
        return Ok((keep_quotient.then(Vec::new), remainder));
    }
    if dividend.is_empty() {
        return Ok((keep_quotient.then(Vec::new), Vec::new()));
    }
    match compare_limbs(dividend, divisor, control)? {
        Ordering::Less => {
            let remainder = copy_limbs(dividend, control)?;
            return Ok((keep_quotient.then(Vec::new), remainder));
        }
        Ordering::Equal => {
            let quotient = if keep_quotient {
                Some(one_limbs(control)?)
            } else {
                None
            };
            return Ok((quotient, Vec::new()));
        }
        Ordering::Greater => {}
    }

    if let [divisor] = divisor {
        return div_rem_word(dividend, *divisor, keep_quotient, control);
    }
    if let Some((word_shift, bit_shift)) = power_of_two_shift(divisor, control)? {
        return div_rem_power_of_two(dividend, word_shift, bit_shift, keep_quotient, control);
    }

    let bits = bit_length(dividend, control)?;
    let mut quotient = if keep_quotient {
        Some(zeroed(dividend.len(), control)?)
    } else {
        None
    };
    let remainder_width = divisor.len().checked_add(1).ok_or({
        Halt::Stop(NatStop::OutputSizeOverflow {
            task: control.task,
            progress: control.progress,
        })
    })?;
    let mut remainder = zeroed(remainder_width, control)?;

    for bit in (0..bits).rev() {
        control.step()?;
        let incoming = (dividend[bit / 64] >> (bit % 64)) & 1;
        let mut carry = incoming;
        for limb in &mut remainder {
            control.step()?;
            let next = *limb >> 63;
            *limb = (*limb << 1) | carry;
            carry = next;
        }
        if compare_fixed(&remainder, divisor, control)? != Ordering::Less {
            subtract_fixed(&mut remainder, divisor, control)?;
            if let Some(quotient) = &mut quotient {
                control.step()?;
                quotient[bit / 64] |= 1u64 << (bit % 64);
            }
        }
    }

    let quotient = match quotient {
        Some(quotient) => Some(trim(quotient, control)?),
        None => None,
    };
    Ok((quotient, trim(remainder, control)?))
}
