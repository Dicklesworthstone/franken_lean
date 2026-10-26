//! The pin's pretty-printer options as its delaborator reads them: the `getPP*` functions of
//! vendored `Lean/PrettyPrinter/Delaborator/Options.lean`, with the defaults they derive from
//! `pp.all`. They are read from a scope's options, where `set_option` records a value only for
//! an option `fln_elab::source::scope::options` honors; every other option is at the pin's
//! default there, so reading it here gives the pin's reading of it.
use fln_core::name::Name;
use fln_core::options::KVMap;

/// The options the printer reads, each named for its `getPP*` reader.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PpOptions {
    /// `getPPAll`.
    pub all: bool,
    /// `getPPExplicit`: applications in explicit mode, `@f a b`, with every argument.
    pub explicit: bool,
    /// `getPPUniverses`: a constant's universe levels, `List.map.{0, 0}`.
    pub universes: bool,
    /// `getPPProofs`: proofs inside a term shown rather than `⋯`.
    pub proofs: bool,
    /// Whether `pp.proofs` is set at all: `delabCore` turns it on for a term that is itself a
    /// proof only when it is not (`pp.proofs.get? opts == none`, vendored
    /// `PrettyPrinter/Delaborator/Basic.lean:510-514`).
    pub proofs_set: bool,
    /// `getPPCoercions`: coercions as `↑x`, and numerals as literals.
    pub coercions: bool,
    /// `getPPCoercionsTypes`: a coercion as `(↑x : T)`.
    pub coercions_types: bool,
    /// `getPPNotation`: app unexpanders and the notations of the builtin delaborators.
    pub notation: bool,
    /// `getPPFullNames`.
    pub full_names: bool,
    /// `getPPPrivateNames`.
    pub private_names: bool,
    /// `getPPFunBinderTypes`.
    pub fun_binder_types: bool,
    /// `getPPPiBinderNames`.
    pub pi_binder_names: bool,
    /// `getPPPiBinderNamesHygienic`.
    pub pi_binder_names_hygienic: bool,
    /// `getPPForalls`: a proposition's binders as `∀`.
    pub foralls: bool,
    /// `getPPLetVarTypes`.
    pub let_var_types: bool,
    /// `getPPNumericTypes`: a numeric literal ascribed its type, `(2 : Nat)`.
    pub numeric_types: bool,
    /// `getPPNatLit`: a raw literal as `nat_lit n`.
    pub nat_lit: bool,
    /// `getPPFieldNotation`.
    pub field_notation: bool,
    /// `getPPStructureInstances`.
    pub structure_instances: bool,
    /// `getPPStructureInstanceType`: a structure instance as `{ x := a : T }`.
    pub structure_instance_types: bool,
    /// `getPPInstances`: an instance argument in explicit mode, or `_`.
    pub instances: bool,
    /// `getPPInstanceTypes`: an instance argument in explicit mode as `(i : C α)`.
    pub instance_types: bool,
    /// `getPPBeta`: the term is beta-reduced before it is printed.
    pub beta: bool,
    /// `getPPMatch`.
    pub match_: bool,
    /// `getPPTagAppFns`: it tags heads for the InfoView, and turns off field notation in
    /// explicit mode (`delabAppCore`).
    pub tag_app_fns: bool,
}

impl Default for PpOptions {
    fn default() -> Self {
        Self::read(&KVMap::new())
    }
}

impl PpOptions {
    /// The options as the pin's readers see `options`.
    pub fn read(options: &KVMap) -> Self {
        let get = |key: &str, default: bool| {
            options.get_bool(&Name::from_components(key.split('.')), default)
        };
        let all = get("pp.all", false);
        let numeric_types = get("pp.numericTypes", false);
        Self {
            all,
            explicit: get("pp.explicit", all),
            universes: get("pp.universes", all),
            proofs: get("pp.proofs", all),
            proofs_set: options.contains(&Name::from_components(["pp", "proofs"])),
            coercions: get("pp.coercions", !all),
            coercions_types: get("pp.coercions.types", false),
            notation: get("pp.notation", !all),
            full_names: get("pp.fullNames", all),
            private_names: get("pp.privateNames", all),
            fun_binder_types: get("pp.funBinderTypes", all),
            pi_binder_names: get("pp.piBinderNames", all),
            pi_binder_names_hygienic: get("pp.piBinderNames.hygienic", false),
            foralls: get("pp.foralls", true),
            let_var_types: get("pp.letVarTypes", all),
            numeric_types,
            nat_lit: get("pp.natLit", numeric_types && !all),
            field_notation: get("pp.fieldNotation", !all),
            structure_instances: get("pp.structureInstances", !all),
            structure_instance_types: get("pp.structureInstanceTypes", all),
            instances: get("pp.instances", true),
            instance_types: get("pp.instanceTypes", false),
            beta: get("pp.beta", false),
            match_: get("pp.match", !all),
            tag_app_fns: get("pp.tagAppFns", all),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::options::DataValue;

    fn set(entries: &[(&str, bool)]) -> PpOptions {
        let mut options = KVMap::new();
        for (key, value) in entries {
            options.insert(
                Name::from_components(key.split('.')),
                DataValue::OfBool(*value),
            );
        }
        PpOptions::read(&options)
    }

    /// `pp.all`'s implications, and an explicit setting of an implied option overriding them, as
    /// `getPP*` reads them (`o.get name (getPPAll o)`).
    #[test]
    fn pp_all_implies_what_the_pins_readers_derive_from_it() {
        let default = PpOptions::default();
        assert!(!default.explicit && !default.universes && !default.proofs);
        assert!(default.coercions && default.notation && default.field_notation);
        let all = set(&[("pp.all", true)]);
        assert!(all.explicit && all.universes && all.proofs && all.full_names);
        assert!(all.fun_binder_types && all.pi_binder_names && all.let_var_types);
        assert!(!all.coercions && !all.notation && !all.field_notation);
        assert!(!all.structure_instances && all.structure_instance_types && !all.match_);
        assert!(
            !all.nat_lit,
            "`pp.natLit` defaults to `numericTypes && !all`"
        );
        let partial = set(&[
            ("pp.all", true),
            ("pp.universes", false),
            ("pp.explicit", false),
            ("pp.structureInstances", true),
        ]);
        assert!(!partial.universes && !partial.explicit && partial.structure_instances);
        assert!(!partial.notation && partial.full_names);
        assert!(set(&[("pp.numericTypes", true)]).nat_lit);
    }
}
