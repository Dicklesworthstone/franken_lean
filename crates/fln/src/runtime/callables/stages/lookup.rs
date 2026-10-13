//! Resolve completed lambda syntax to its current metadata slot during one
//! capture-refinement pass. Results and ownership stay in the live table.
use super::*;
use std::collections::HashMap;

pub(super) struct LambdaIndex {
    prefix: usize,
    latest: HashMap<Expr, usize>,
}

impl LambdaIndex {
    pub(super) fn new(preparation: &mut Preparation<'_>) -> Result<Self, IngressError> {
        let prefix = preparation.lambdas.len();
        let limit = preparation.limits.max_lambda_bindings;
        if prefix > limit {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::LambdaBindings,
                limit,
                observed: prefix,
            });
        }
        let mut latest = HashMap::new();
        latest
            .try_reserve(prefix)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::LambdaBindings,
                requested: prefix,
            })?;
        for index in 0..prefix {
            preparation.tick()?;
            // Match the former reverse scan even if a syntax key has more
            // than one row. The table's completed prefix never changes keys
            // during capture refinement; only its metadata can be refined.
            latest.insert(preparation.lambdas[index].lambda.clone(), index);
        }
        Ok(Self { prefix, latest })
    }

    pub(super) fn get(
        &self,
        preparation: &mut Preparation<'_>,
        source: &Expr,
    ) -> Result<Option<usize>, IngressError> {
        if preparation.lambdas.len() < self.prefix {
            return Err(unsupported("capture lambda prefix changed"));
        }
        // A query may discover additional metadata after this pass starts.
        // Search that live tail first, retaining latest-row precedence without
        // persisting an index across preparation or layout-discovery phases.
        for index in (self.prefix..preparation.lambdas.len()).rev() {
            preparation.tick()?;
            if preparation.lambdas[index].lambda == *source {
                return Ok(Some(index));
            }
        }
        preparation.tick()?;
        Ok(self.latest.get(source).copied())
    }
}

#[cfg(test)]
mod tests;
