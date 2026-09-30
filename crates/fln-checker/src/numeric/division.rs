//! Checker-owned division. Every limb walk and allocation uses the caller's
//! numeric budget; incomplete arithmetic never becomes a numeric verdict.

use super::*;

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

    div_rem_multiword(dividend, divisor, keep_quotient, control)
}

// Normalize so the top divisor word is at least 2^63. With base B = 2^64,
// dividing a two-word prefix by that word overestimates each quotient digit
// by at most two. Checking the next divisor word removes all but a possible
// one-digit excess; a subtract-and-add-back resolves that final uncertainty.
// No estimate is ever published as an arithmetic result.
fn div_rem_multiword(
    dividend: &[u64],
    divisor: &[u64],
    keep_quotient: bool,
    control: &mut Control<'_>,
) -> Result<(Option<Vec<u64>>, Vec<u64>), Halt> {
    let width = divisor.len();
    let shift = divisor[width - 1].leading_zeros();
    let work_width = width.checked_add(1).ok_or({
        Halt::Stop(NatStop::OutputSizeOverflow {
            task: control.task,
            progress: control.progress,
        })
    })?;
    let mut divisor_words = control.reserve(width)?;
    let mut carry = 0;
    for word in divisor {
        control.step()?;
        divisor_words.push((*word << shift) | carry);
        carry = if shift == 0 { 0 } else { *word >> (64 - shift) };
    }
    // The shift is chosen from the highest divisor word, so it cannot overflow.
    if carry != 0 {
        return Err(Halt::Fault(NatFault::ArithmeticInvariant {
            task: control.task,
        }));
    }
    // Only the current remainder plus one incoming word is mutable. Reading
    // normalized dividend words on demand avoids copying an arbitrarily large
    // dividend, especially when modulo discards the quotient altogether.
    let mut window = control.reserve(work_width)?;
    let first_position = dividend.len() - width;
    for index in first_position..=dividend.len() {
        control.step()?;
        window.push(normalized_word(dividend, index, shift));
    }
    let quotient_width = first_position + 1;
    let mut quotient = if keep_quotient {
        Some(zeroed(quotient_width, control)?)
    } else {
        None
    };
    for position in (0..quotient_width).rev() {
        control.step()?;
        let mut digit = estimate_digit(&window, &divisor_words, control)?;
        if subtract_product(&mut window, &divisor_words, digit, control)? {
            // The prefix estimate was one too large. Restoring one divisor
            // cancels the borrow out of the window, with wrapping only here.
            digit = digit
                .checked_sub(1)
                .ok_or(Halt::Fault(NatFault::ArithmeticInvariant {
                    task: control.task,
                }))?;
            add_back(&mut window, &divisor_words, control)?;
        }
        if window[width] != 0 {
            return Err(Halt::Fault(NatFault::ArithmeticInvariant {
                task: control.task,
            }));
        }
        if let Some(quotient) = &mut quotient {
            control.step()?;
            quotient[position] = digit;
        }
        if position != 0 {
            // Advance the remainder by one base-B digit. This is deliberately
            // an explicit budgeted walk, not an unmetered bulk memory move.
            for index in (1..=width).rev() {
                control.step()?;
                window[index] = window[index - 1];
            }
            control.step()?;
            window[0] = normalized_word(dividend, position - 1, shift);
        }
    }
    // Reuse the n+1-word window for the canonical remainder.
    window.truncate(width);
    if shift != 0 {
        for index in 0..width {
            control.step()?;
            let high = window.get(index + 1).copied().unwrap_or(0);
            window[index] = (window[index] >> shift) | (high << (64 - shift));
        }
    }
    let quotient = match quotient {
        Some(quotient) => Some(trim(quotient, control)?),
        None => None,
    };
    Ok((quotient, trim(window, control)?))
}

// The caller meters each read. index == value.len() is the one extra leading
// word; all other reads refer to the original immutable dividend.
fn normalized_word(value: &[u64], index: usize, shift: u32) -> u64 {
    let mut word = value.get(index).copied().unwrap_or(0) << shift;
    if shift != 0 && index != 0 {
        word |= value[index - 1] >> (64 - shift);
    }
    word
}

fn estimate_digit(window: &[u64], divisor: &[u64], control: &mut Control<'_>) -> Result<u64, Halt> {
    control.step()?;
    let width = divisor.len();
    let high = window[width];
    let next = window[width - 1];
    let divisor_high = divisor[width - 1];
    // The previous remainder is below the divisor. Its leading word can be
    // equal (not greater), in which case the two-word quotient may exceed u64.
    let (mut digit, mut remainder) = match high.cmp(&divisor_high) {
        Ordering::Less => {
            let prefix = (u128::from(high) << 64) | u128::from(next);
            (
                (prefix / u128::from(divisor_high)) as u64,
                prefix % u128::from(divisor_high),
            )
        }
        Ordering::Equal => (u64::MAX, u128::from(next) + u128::from(divisor_high)),
        Ordering::Greater => {
            return Err(Halt::Fault(NatFault::ArithmeticInvariant {
                task: control.task,
            }));
        }
    };
    while remainder < (1_u128 << 64) {
        control.step()?;
        if u128::from(digit) * u128::from(divisor[width - 2])
            <= (remainder << 64) | u128::from(window[width - 2])
        {
            break;
        }
        digit -= 1;
        remainder += u128::from(divisor_high);
    }
    Ok(digit)
}

// Subtract digit * divisor in place and report whether it borrowed out of
// the window. The multiply carry plus subtraction borrow stays <= digit,
// so even at u64::MAX the next product fits u128 and the carry fits u64.
fn subtract_product(
    window: &mut [u64],
    divisor: &[u64],
    digit: u64,
    control: &mut Control<'_>,
) -> Result<bool, Halt> {
    let mut carry = 0_u128;
    for (index, word) in divisor.iter().enumerate() {
        control.step()?;
        let product = u128::from(digit) * u128::from(*word) + carry;
        let (difference, borrow) = window[index].overflowing_sub(product as u64);
        window[index] = difference;
        carry = (product >> 64) + u128::from(borrow);
    }
    control.step()?;
    let (difference, borrow) = window[divisor.len()].overflowing_sub(carry as u64);
    window[divisor.len()] = difference;
    Ok(borrow)
}

fn add_back(window: &mut [u64], divisor: &[u64], control: &mut Control<'_>) -> Result<(), Halt> {
    let mut carry = 0_u128;
    for (index, word) in divisor.iter().enumerate() {
        control.step()?;
        let sum = u128::from(window[index]) + u128::from(*word) + carry;
        window[index] = sum as u64;
        carry = sum >> 64;
    }
    control.step()?;
    window[divisor.len()] = window[divisor.len()].wrapping_add(carry as u64);
    Ok(())
}
