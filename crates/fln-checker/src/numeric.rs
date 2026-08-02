//! Independent arbitrary-precision natural arithmetic for checker judgments.
//!
//! Values use canonical little-endian `u64` limbs: zero is the empty vector and
//! every nonzero value has a nonzero final limb. The implementation is
//! deliberately simple and checker-owned. It shares neither the primary
//! kernel's arithmetic nor the suite bignum crate's semantic path.
//!
//! This module is only the numeric substrate for KR-313. It does not recognize
//! expression heads, normalize operands, enforce the closed-term gate, or admit
//! declarations.

use std::cmp::Ordering;

/// The exact exponent ceiling used by the pinned KR-313 reduction table.
pub const REDUCE_POW_MAX_EXP: u64 = 1 << 24;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NatValue {
    limbs_le: Vec<u64>,
}

impl NatValue {
    pub const fn zero() -> NatValue {
        NatValue {
            limbs_le: Vec::new(),
        }
    }

    pub fn one() -> NatValue {
        NatValue { limbs_le: vec![1] }
    }

    pub fn from_u64(value: u64) -> NatValue {
        if value == 0 {
            NatValue::zero()
        } else {
            NatValue {
                limbs_le: vec![value],
            }
        }
    }

    pub fn from_limbs_le(limbs_le: Vec<u64>) -> Result<NatValue, NatValueError> {
        if limbs_le.last() == Some(&0) {
            Err(NatValueError::NonCanonical)
        } else {
            Ok(NatValue { limbs_le })
        }
    }

    pub fn limbs_le(&self) -> &[u64] {
        &self.limbs_le
    }

    pub fn is_zero(&self) -> bool {
        self.limbs_le.is_empty()
    }

    pub fn to_u64(&self) -> Option<u64> {
        match self.limbs_le.as_slice() {
            [] => Some(0),
            [value] => Some(*value),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatValueError {
    NonCanonical,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatOperation {
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    Gcd,
    Power,
    BitAnd,
    BitOr,
    BitXor,
    ShiftLeft,
    ShiftRight,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatTask {
    Compare,
    Successor,
    Binary(NatOperation),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatComparison {
    Less,
    Equal,
    Greater,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatOperand {
    Unary,
    Left,
    Right,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NatBudget {
    pub max_steps: u64,
    /// Aggregate limb capacity successfully reserved during one operation.
    pub max_materialized_limbs: u64,
}

impl NatBudget {
    pub const fn new(max_steps: u64, max_materialized_limbs: u64) -> NatBudget {
        NatBudget {
            max_steps,
            max_materialized_limbs,
        }
    }

    pub const fn unlimited() -> NatBudget {
        NatBudget::new(u64::MAX, u64::MAX)
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct NatProgress {
    pub steps: u64,
    pub materialized_limbs: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NatResult<T> {
    pub value: T,
    pub progress: NatProgress,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatLimit {
    Steps,
    MaterializedLimbs,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NatStop {
    Resource {
        task: NatTask,
        limit: NatLimit,
        allowed: u64,
        observed: u64,
        progress: NatProgress,
    },
    Cancelled {
        task: NatTask,
        polls: u64,
        progress: NatProgress,
    },
    OutputSizeOverflow {
        task: NatTask,
        progress: NatProgress,
    },
    AllocationFailed {
        task: NatTask,
        requested_limbs: u64,
        progress: NatProgress,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NatFault {
    NonCanonicalOperand { operand: NatOperand },
    ArithmeticInvariant { task: NatTask },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NatRefusal {
    PowExponentAbovePinCap { cap: u64 },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NatOutcome<T> {
    Complete(NatResult<T>),
    Refused {
        refusal: NatRefusal,
        progress: NatProgress,
    },
    Inconclusive(NatStop),
    InternalFault(NatFault),
}

enum Halt {
    Refused(NatRefusal),
    Stop(NatStop),
    Fault(NatFault),
}

struct Control<'a> {
    task: NatTask,
    budget: NatBudget,
    progress: NatProgress,
    polls: u64,
    cancelled: &'a mut dyn FnMut() -> bool,
}

impl<'a> Control<'a> {
    fn new(
        task: NatTask,
        budget: NatBudget,
        cancelled: &'a mut dyn FnMut() -> bool,
    ) -> Control<'a> {
        Control {
            task,
            budget,
            progress: NatProgress::default(),
            polls: 0,
            cancelled,
        }
    }

    fn poll(&mut self) -> Result<(), Halt> {
        self.polls = self.polls.saturating_add(1);
        if (self.cancelled)() {
            return Err(Halt::Stop(NatStop::Cancelled {
                task: self.task,
                polls: self.polls,
                progress: self.progress,
            }));
        }
        Ok(())
    }

    fn step(&mut self) -> Result<(), Halt> {
        self.poll()?;
        let observed = self.progress.steps.saturating_add(1);
        if observed > self.budget.max_steps {
            return Err(Halt::Stop(NatStop::Resource {
                task: self.task,
                limit: NatLimit::Steps,
                allowed: self.budget.max_steps,
                observed,
                progress: self.progress,
            }));
        }
        self.progress.steps = observed;
        Ok(())
    }

    fn reserve(&mut self, limb_count: usize) -> Result<Vec<u64>, Halt> {
        self.poll()?;
        let requested_limbs = u64::try_from(limb_count).map_err(|_| {
            Halt::Stop(NatStop::OutputSizeOverflow {
                task: self.task,
                progress: self.progress,
            })
        })?;
        let observed = self
            .progress
            .materialized_limbs
            .checked_add(requested_limbs)
            .ok_or({
                Halt::Stop(NatStop::OutputSizeOverflow {
                    task: self.task,
                    progress: self.progress,
                })
            })?;
        if observed > self.budget.max_materialized_limbs {
            return Err(Halt::Stop(NatStop::Resource {
                task: self.task,
                limit: NatLimit::MaterializedLimbs,
                allowed: self.budget.max_materialized_limbs,
                observed,
                progress: self.progress,
            }));
        }
        let mut output = Vec::new();
        output.try_reserve_exact(limb_count).map_err(|_| {
            Halt::Stop(NatStop::AllocationFailed {
                task: self.task,
                requested_limbs,
                progress: self.progress,
            })
        })?;
        self.progress.materialized_limbs = observed;
        Ok(output)
    }
}

fn outcome<T>(result: Result<NatResult<T>, Halt>, progress: NatProgress) -> NatOutcome<T> {
    match result {
        Ok(result) => NatOutcome::Complete(result),
        Err(Halt::Refused(refusal)) => NatOutcome::Refused { refusal, progress },
        Err(Halt::Stop(stop)) => NatOutcome::Inconclusive(stop),
        Err(Halt::Fault(fault)) => NatOutcome::InternalFault(fault),
    }
}

fn validate_operand(
    value: &NatValue,
    operand: NatOperand,
    control: &mut Control<'_>,
) -> Result<(), Halt> {
    control.step()?;
    if value.limbs_le.last() == Some(&0) {
        Err(Halt::Fault(NatFault::NonCanonicalOperand { operand }))
    } else {
        Ok(())
    }
}

fn finish_value(limbs_le: Vec<u64>, control: &Control<'_>) -> Result<NatResult<NatValue>, Halt> {
    if limbs_le.last() == Some(&0) {
        return Err(Halt::Fault(NatFault::ArithmeticInvariant {
            task: control.task,
        }));
    }
    Ok(NatResult {
        value: NatValue { limbs_le },
        progress: control.progress,
    })
}

fn trim(mut value: Vec<u64>, control: &mut Control<'_>) -> Result<Vec<u64>, Halt> {
    while value.last() == Some(&0) {
        control.step()?;
        value.pop();
    }
    Ok(value)
}

fn copy_limbs(value: &[u64], control: &mut Control<'_>) -> Result<Vec<u64>, Halt> {
    let mut output = control.reserve(value.len())?;
    for limb in value {
        control.step()?;
        output.push(*limb);
    }
    Ok(output)
}

fn one_limbs(control: &mut Control<'_>) -> Result<Vec<u64>, Halt> {
    let mut output = control.reserve(1)?;
    control.step()?;
    output.push(1);
    Ok(output)
}

fn compare_limbs(left: &[u64], right: &[u64], control: &mut Control<'_>) -> Result<Ordering, Halt> {
    control.step()?;
    match left.len().cmp(&right.len()) {
        Ordering::Equal => {}
        order => return Ok(order),
    }
    for (left, right) in left.iter().rev().zip(right.iter().rev()) {
        control.step()?;
        match left.cmp(right) {
            Ordering::Equal => {}
            order => return Ok(order),
        }
    }
    Ok(Ordering::Equal)
}

fn add_limbs(left: &[u64], right: &[u64], control: &mut Control<'_>) -> Result<Vec<u64>, Halt> {
    let width = left.len().max(right.len());
    let capacity = width.checked_add(1).ok_or({
        Halt::Stop(NatStop::OutputSizeOverflow {
            task: control.task,
            progress: control.progress,
        })
    })?;
    let mut output = control.reserve(capacity)?;
    let mut carry = 0u128;
    for index in 0..width {
        control.step()?;
        let sum = u128::from(left.get(index).copied().unwrap_or(0))
            + u128::from(right.get(index).copied().unwrap_or(0))
            + carry;
        output.push(sum as u64);
        carry = sum >> 64;
    }
    if carry != 0 {
        control.step()?;
        output.push(carry as u64);
    }
    Ok(output)
}

fn successor_limbs(value: &[u64], control: &mut Control<'_>) -> Result<Vec<u64>, Halt> {
    let capacity = value.len().checked_add(1).ok_or({
        Halt::Stop(NatStop::OutputSizeOverflow {
            task: control.task,
            progress: control.progress,
        })
    })?;
    let mut output = control.reserve(capacity)?;
    let mut carry = true;
    for limb in value {
        control.step()?;
        if carry {
            let (next, overflow) = limb.overflowing_add(1);
            output.push(next);
            carry = overflow;
        } else {
            output.push(*limb);
        }
    }
    if carry {
        control.step()?;
        output.push(1);
    }
    Ok(output)
}

fn subtract_limbs(
    left: &[u64],
    right: &[u64],
    control: &mut Control<'_>,
) -> Result<Vec<u64>, Halt> {
    if compare_limbs(left, right, control)? != Ordering::Greater {
        return Ok(Vec::new());
    }
    let mut output = control.reserve(left.len())?;
    let mut borrow = false;
    for (index, left_limb) in left.iter().copied().enumerate() {
        control.step()?;
        let right_limb = right.get(index).copied().unwrap_or(0);
        let (partial, first_borrow) = left_limb.overflowing_sub(right_limb);
        let (value, second_borrow) = partial.overflowing_sub(u64::from(borrow));
        output.push(value);
        borrow = first_borrow || second_borrow;
    }
    if borrow {
        return Err(Halt::Fault(NatFault::ArithmeticInvariant {
            task: control.task,
        }));
    }
    trim(output, control)
}

fn multiply_limbs(
    left: &[u64],
    right: &[u64],
    control: &mut Control<'_>,
) -> Result<Vec<u64>, Halt> {
    if left.is_empty() || right.is_empty() {
        return Ok(Vec::new());
    }
    let width = left.len().checked_add(right.len()).ok_or({
        Halt::Stop(NatStop::OutputSizeOverflow {
            task: control.task,
            progress: control.progress,
        })
    })?;
    let mut output = control.reserve(width)?;
    for _ in 0..width {
        control.step()?;
        output.push(0);
    }
    for (left_index, left_limb) in left.iter().copied().enumerate() {
        let mut carry = 0u128;
        for (right_index, right_limb) in right.iter().copied().enumerate() {
            control.step()?;
            let index = left_index + right_index;
            let product =
                u128::from(left_limb) * u128::from(right_limb) + u128::from(output[index]) + carry;
            output[index] = product as u64;
            carry = product >> 64;
        }
        output[left_index + right.len()] = carry as u64;
    }
    trim(output, control)
}

fn bitwise_limbs(
    operation: NatOperation,
    left: &[u64],
    right: &[u64],
    control: &mut Control<'_>,
) -> Result<Vec<u64>, Halt> {
    let width = if operation == NatOperation::BitAnd {
        left.len().min(right.len())
    } else {
        left.len().max(right.len())
    };
    let mut output = control.reserve(width)?;
    for index in 0..width {
        control.step()?;
        let left = left.get(index).copied().unwrap_or(0);
        let right = right.get(index).copied().unwrap_or(0);
        output.push(match operation {
            NatOperation::BitAnd => left & right,
            NatOperation::BitOr => left | right,
            NatOperation::BitXor => left ^ right,
            _ => {
                return Err(Halt::Fault(NatFault::ArithmeticInvariant {
                    task: control.task,
                }));
            }
        });
    }
    trim(output, control)
}

fn shift_count(value: &[u64], control: &mut Control<'_>) -> Result<Option<u64>, Halt> {
    control.step()?;
    Ok(match value {
        [] => Some(0),
        [value] => Some(*value),
        _ => None,
    })
}

fn shift_left_limbs(
    value: &[u64],
    count: &[u64],
    control: &mut Control<'_>,
) -> Result<Vec<u64>, Halt> {
    if value.is_empty() {
        return Ok(Vec::new());
    }
    let Some(count) = shift_count(count, control)? else {
        return Err(Halt::Stop(NatStop::OutputSizeOverflow {
            task: control.task,
            progress: control.progress,
        }));
    };
    let word_shift = count / 64;
    let word_shift = usize::try_from(word_shift).map_err(|_| {
        Halt::Stop(NatStop::OutputSizeOverflow {
            task: control.task,
            progress: control.progress,
        })
    })?;
    let bit_shift = (count % 64) as u32;
    let capacity = value
        .len()
        .checked_add(word_shift)
        .and_then(|width| width.checked_add(usize::from(bit_shift != 0)))
        .ok_or({
            Halt::Stop(NatStop::OutputSizeOverflow {
                task: control.task,
                progress: control.progress,
            })
        })?;
    let mut output = control.reserve(capacity)?;
    for _ in 0..word_shift {
        control.step()?;
        output.push(0);
    }
    if bit_shift == 0 {
        for limb in value {
            control.step()?;
            output.push(*limb);
        }
        return Ok(output);
    }
    let mut carry = 0;
    for limb in value {
        control.step()?;
        output.push((*limb << bit_shift) | carry);
        carry = *limb >> (64 - bit_shift);
    }
    control.step()?;
    output.push(carry);
    trim(output, control)
}

fn shift_right_limbs(
    value: &[u64],
    count: &[u64],
    control: &mut Control<'_>,
) -> Result<Vec<u64>, Halt> {
    let Some(count) = shift_count(count, control)? else {
        return Ok(Vec::new());
    };
    let word_shift = count / 64;
    let Ok(word_shift) = usize::try_from(word_shift) else {
        return Ok(Vec::new());
    };
    if word_shift >= value.len() {
        return Ok(Vec::new());
    }
    let bit_shift = (count % 64) as u32;
    let width = value.len() - word_shift;
    let mut output = control.reserve(width)?;
    for index in word_shift..value.len() {
        control.step()?;
        let mut limb = value[index] >> bit_shift;
        if bit_shift != 0 && index + 1 < value.len() {
            limb |= value[index + 1] << (64 - bit_shift);
        }
        output.push(limb);
    }
    trim(output, control)
}

fn zeroed(width: usize, control: &mut Control<'_>) -> Result<Vec<u64>, Halt> {
    let mut output = control.reserve(width)?;
    for _ in 0..width {
        control.step()?;
        output.push(0);
    }
    Ok(output)
}

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

fn div_rem_limbs(
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

fn gcd_limbs(left: &[u64], right: &[u64], control: &mut Control<'_>) -> Result<Vec<u64>, Halt> {
    if left.is_empty() {
        return copy_limbs(right, control);
    }
    if right.is_empty() {
        return copy_limbs(left, control);
    }
    let mut left = copy_limbs(left, control)?;
    let mut right = copy_limbs(right, control)?;
    while !right.is_empty() {
        control.step()?;
        let (_, remainder) = div_rem_limbs(&left, &right, false, control)?;
        left = right;
        right = remainder;
    }
    Ok(left)
}

fn power_limbs(
    base: &[u64],
    exponent: &[u64],
    control: &mut Control<'_>,
) -> Result<Vec<u64>, Halt> {
    let Some(mut exponent) = shift_count(exponent, control)? else {
        return Err(Halt::Refused(NatRefusal::PowExponentAbovePinCap {
            cap: REDUCE_POW_MAX_EXP,
        }));
    };
    if exponent > REDUCE_POW_MAX_EXP {
        return Err(Halt::Refused(NatRefusal::PowExponentAbovePinCap {
            cap: REDUCE_POW_MAX_EXP,
        }));
    }
    if exponent == 0 {
        return one_limbs(control);
    }
    if base.is_empty() {
        return Ok(Vec::new());
    }
    if base == [1] {
        return one_limbs(control);
    }

    let mut result = one_limbs(control)?;
    let mut factor = copy_limbs(base, control)?;
    while exponent != 0 {
        control.step()?;
        if exponent & 1 != 0 {
            result = multiply_limbs(&result, &factor, control)?;
        }
        exponent >>= 1;
        if exponent != 0 {
            factor = multiply_limbs(&factor, &factor, control)?;
        }
    }
    Ok(result)
}

pub fn compare(left: &NatValue, right: &NatValue, budget: NatBudget) -> NatOutcome<NatComparison> {
    compare_with(left, right, budget, || false)
}

pub fn compare_with(
    left: &NatValue,
    right: &NatValue,
    budget: NatBudget,
    mut cancelled: impl FnMut() -> bool,
) -> NatOutcome<NatComparison> {
    let mut control = Control::new(NatTask::Compare, budget, &mut cancelled);
    let result = (|| {
        validate_operand(left, NatOperand::Left, &mut control)?;
        validate_operand(right, NatOperand::Right, &mut control)?;
        let value = match compare_limbs(&left.limbs_le, &right.limbs_le, &mut control)? {
            Ordering::Less => NatComparison::Less,
            Ordering::Equal => NatComparison::Equal,
            Ordering::Greater => NatComparison::Greater,
        };
        Ok(NatResult {
            value,
            progress: control.progress,
        })
    })();
    outcome(result, control.progress)
}

pub fn successor(value: &NatValue, budget: NatBudget) -> NatOutcome<NatValue> {
    successor_with(value, budget, || false)
}

pub fn successor_with(
    value: &NatValue,
    budget: NatBudget,
    mut cancelled: impl FnMut() -> bool,
) -> NatOutcome<NatValue> {
    let mut control = Control::new(NatTask::Successor, budget, &mut cancelled);
    let result = (|| {
        validate_operand(value, NatOperand::Unary, &mut control)?;
        let result = successor_limbs(&value.limbs_le, &mut control)?;
        finish_value(result, &control)
    })();
    outcome(result, control.progress)
}

pub fn binary(
    operation: NatOperation,
    left: &NatValue,
    right: &NatValue,
    budget: NatBudget,
) -> NatOutcome<NatValue> {
    binary_with(operation, left, right, budget, || false)
}

pub fn binary_with(
    operation: NatOperation,
    left: &NatValue,
    right: &NatValue,
    budget: NatBudget,
    mut cancelled: impl FnMut() -> bool,
) -> NatOutcome<NatValue> {
    let mut control = Control::new(NatTask::Binary(operation), budget, &mut cancelled);
    let result = (|| {
        validate_operand(left, NatOperand::Left, &mut control)?;
        validate_operand(right, NatOperand::Right, &mut control)?;
        let result = match operation {
            NatOperation::Add => add_limbs(&left.limbs_le, &right.limbs_le, &mut control)?,
            NatOperation::Subtract => {
                subtract_limbs(&left.limbs_le, &right.limbs_le, &mut control)?
            }
            NatOperation::Multiply => {
                multiply_limbs(&left.limbs_le, &right.limbs_le, &mut control)?
            }
            NatOperation::Divide => {
                let (quotient, _) =
                    div_rem_limbs(&left.limbs_le, &right.limbs_le, true, &mut control)?;
                quotient.ok_or(Halt::Fault(NatFault::ArithmeticInvariant {
                    task: control.task,
                }))?
            }
            NatOperation::Modulo => {
                let (_, remainder) =
                    div_rem_limbs(&left.limbs_le, &right.limbs_le, false, &mut control)?;
                remainder
            }
            NatOperation::Gcd => gcd_limbs(&left.limbs_le, &right.limbs_le, &mut control)?,
            NatOperation::Power => power_limbs(&left.limbs_le, &right.limbs_le, &mut control)?,
            NatOperation::BitAnd | NatOperation::BitOr | NatOperation::BitXor => {
                bitwise_limbs(operation, &left.limbs_le, &right.limbs_le, &mut control)?
            }
            NatOperation::ShiftLeft => {
                shift_left_limbs(&left.limbs_le, &right.limbs_le, &mut control)?
            }
            NatOperation::ShiftRight => {
                shift_right_limbs(&left.limbs_le, &right.limbs_le, &mut control)?
            }
        };
        finish_value(result, &control)
    })();
    outcome(result, control.progress)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_noncanonical_private_operand_is_an_internal_fault() {
        let malformed = NatValue {
            limbs_le: vec![1, 0],
        };
        assert_eq!(
            successor(&malformed, NatBudget::unlimited()),
            NatOutcome::InternalFault(NatFault::NonCanonicalOperand {
                operand: NatOperand::Unary,
            })
        );
    }

    #[test]
    fn either_noncanonical_binary_operand_is_an_internal_fault() {
        let malformed = NatValue {
            limbs_le: vec![1, 0],
        };
        let valid = NatValue::one();
        assert_eq!(
            binary(
                NatOperation::Add,
                &malformed,
                &valid,
                NatBudget::unlimited(),
            ),
            NatOutcome::InternalFault(NatFault::NonCanonicalOperand {
                operand: NatOperand::Left,
            })
        );
        assert_eq!(
            binary(
                NatOperation::Add,
                &valid,
                &malformed,
                NatBudget::unlimited(),
            ),
            NatOutcome::InternalFault(NatFault::NonCanonicalOperand {
                operand: NatOperand::Right,
            })
        );
    }
}
