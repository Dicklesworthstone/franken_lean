//! Stable structural ordering with charged comparisons and index moves.
//!
//! Rank refinement keeps the last permutation, so completed natural runs can
//! survive the next closure-id remap. The signature comparator is unchanged;
//! original row indices break exact ties to reproduce the former stable sort
//! even when a remap merges previously distinct signatures. No source row or
//! owner is moved, and a failed local sort cannot publish a new canonical id.

use super::*;
use std::cmp::Ordering;

fn compare_slice<T: Ord>(
    left: &[T],
    right: &[T],
    limits: IngressLimits,
    visited: &mut usize,
) -> Result<Ordering, IngressError> {
    for (left, right) in left.iter().zip(right) {
        charge_catalog_node(visited, limits)?;
        let order = left.cmp(right);
        if order != Ordering::Equal {
            return Ok(order);
        }
    }
    charge_catalog_node(visited, limits)?;
    Ok(left.len().cmp(&right.len()))
}

fn compare(
    rows: &[(Option<usize>, ClosureSignature)],
    left: usize,
    right: usize,
    limits: IngressLimits,
    visited: &mut usize,
) -> Result<Ordering, IngressError> {
    let left_value = &rows
        .get(left)
        .ok_or_else(|| unsupported("unknown callback signature row"))?
        .1;
    let right_value = &rows
        .get(right)
        .ok_or_else(|| unsupported("unknown callback signature row"))?
        .1;
    let order = compare_slice(
        &left_value.parameters,
        &right_value.parameters,
        limits,
        visited,
    )?;
    if order != Ordering::Equal {
        return Ok(order);
    }
    let order = compare_slice(
        &left_value.parameter_ownership,
        &right_value.parameter_ownership,
        limits,
        visited,
    )?;
    if order != Ordering::Equal {
        return Ok(order);
    }
    charge_catalog_node(visited, limits)?;
    let order = left_value.result.cmp(&right_value.result);
    if order != Ordering::Equal {
        return Ok(order);
    }
    charge_catalog_node(visited, limits)?;
    let order = left_value
        .result_ownership
        .cmp(&right_value.result_ownership);
    if order != Ordering::Equal {
        return Ok(order);
    }
    charge_catalog_node(visited, limits)?;
    Ok(left.cmp(&right))
}

fn push_index(
    output: &mut Vec<usize>,
    value: usize,
    limits: IngressLimits,
    visited: &mut usize,
) -> Result<(), IngressError> {
    charge_catalog_node(visited, limits)?;
    reserve(output, limits.fir.max_closure_types)?;
    output.push(value);
    Ok(())
}

pub(in crate::runtime::callables) fn stable_order(
    rows: &[(Option<usize>, ClosureSignature)],
    order: &mut Vec<usize>,
    limits: IngressLimits,
    visited: &mut usize,
) -> Result<(), IngressError> {
    if rows.len() != order.len() {
        return Err(unsupported("callback signature ordering arity"));
    }
    if rows.len() > limits.fir.max_closure_types {
        return Err(IngressError::ResourceLimit {
            resource: IngressResource::ProgramTables,
            limit: limits.fir.max_closure_types,
            observed: rows.len(),
        });
    }
    if order.len() < 2 {
        return Ok(());
    }

    // Every run is nondecreasing in the exact row order. Reversing only strict
    // descending runs retains stable equal-class ordering, including before
    // the first merge. Runs partition the original bounded permutation.
    let mut runs = Vec::new();
    let mut start = 0;
    while start < order.len() {
        let mut end = start + 1;
        if end < order.len() {
            let descending =
                compare(rows, order[start], order[end], limits, visited)? == Ordering::Greater;
            end += 1;
            while end < order.len() {
                let comparison = compare(rows, order[end - 1], order[end], limits, visited)?;
                if (comparison == Ordering::Greater) != descending {
                    break;
                }
                end += 1;
            }
            if descending {
                let mut left = start;
                let mut right = end - 1;
                while left < right {
                    // A swap moves two row indices. Both charges precede the
                    // mutation, so exhaustion leaves a valid local permutation.
                    charge_catalog_node(visited, limits)?;
                    charge_catalog_node(visited, limits)?;
                    order.swap(left, right);
                    left += 1;
                    right -= 1;
                }
            }
        }
        push_index(&mut runs, end, limits, visited)?;
        start = end;
    }
    if runs.len() == 1 {
        return Ok(());
    }

    // Pairwise natural merges take at most ceil(log2(run_count)) rounds. The
    // two fallible bounded buffers are reused; no recursion or comparator
    // callback can continue after a failed budget charge.
    let mut output = Vec::new();
    let mut next_runs = Vec::new();
    while runs.len() > 1 {
        output.clear();
        next_runs.clear();
        let mut start = 0;
        let mut run = 0;
        while run < runs.len() {
            let middle = runs[run];
            let end = runs.get(run + 1).copied().unwrap_or(middle);
            let mut left = start;
            let mut right = middle;
            while left < middle && right < end {
                let row = if compare(rows, order[left], order[right], limits, visited)?
                    != Ordering::Greater
                {
                    let row = order[left];
                    left += 1;
                    row
                } else {
                    let row = order[right];
                    right += 1;
                    row
                };
                push_index(&mut output, row, limits, visited)?;
            }
            for &row in &order[left..middle] {
                push_index(&mut output, row, limits, visited)?;
            }
            for &row in &order[right..end] {
                push_index(&mut output, row, limits, visited)?;
            }
            push_index(&mut next_runs, end, limits, visited)?;
            start = end;
            run += 2;
        }
        std::mem::swap(order, &mut output);
        std::mem::swap(&mut runs, &mut next_runs);
    }
    Ok(())
}

#[cfg(test)]
mod tests;
