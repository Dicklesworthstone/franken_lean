#!/usr/bin/env -S python3 -I -S
"""Fail-closed evidence utilities for FrankenLean's shell quality gates.

This is test/CI apparatus, not a FrankenLean runtime component.  It centralizes the
parts that shell is particularly bad at: JSON encoding and validation, bounded
subprocess capture that continues draining after truncation, process-tree cancellation,
canonical input hashing, and write-once artifact manifests.

Published files are claimed with no-follow ``O_EXCL`` opens and never overwritten.
An interrupted write deliberately remains invalid at its final path: validation fails
closed, the evidence is retained, and no cleanup/deletion is attempted.
"""

from __future__ import annotations

import argparse
import ctypes
import datetime as dt
import errno
import fcntl
import hashlib
import hmac
import json
import os
import platform
import re
import resource
import select
import signal
import stat
import subprocess
import sys
import sysconfig
import threading
import time
from functools import partial
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping, Sequence


PASS = 0
FAIL = 1
SETUP_FAILURE = 2
INCONCLUSIVE = 3
CANCELLED = 4

RUN_SCHEMAS = {"fln.check/2", "fln.e2e/2"}
VERIFICATION_MANIFEST_SCHEMA = "fln.verification-manifest/2"
VERIFICATION_MANIFEST_PATH = "ci/VERIFICATION_MANIFEST.jsonl"
CHECK_HUMAN_SCHEMA = "fln.check-human/1"
CHECK_HUMAN_LOG = "human.semantic.log"
# Frozen with the migration commit. This binds both the complete adopted ID set
# and which adopted beads were still open at adoption time. Expanding or
# weakening the grandfathered set therefore requires an explicit validator
# change, not merely recomputing a self-described manifest hash.
VERIFICATION_ADOPTION_AUTHORITY_HASH = (
    "sha256:30b15f035857461b2798c624c2e35f52dba0626af0667c9a2f845c074729cbbc"
)
VERIFICATION_CLAIM_TYPES = frozenset(
    {"invariant", "proof", "bounded_model", "statistical", "slo", "benchmark"}
)
VERIFICATION_EVIDENCE_KINDS = frozenset(
    {
        "unit",
        "property",
        "metamorphic",
        "fuzz",
        "mutation",
        "fault",
        "mock",
        "no_mock_e2e",
        "proof",
        "benchmark",
    }
)
VERIFICATION_COVERAGE_ARRAY_FIELDS = (
    "requirement_ids",
    "claim_ids",
    "invariant_ids",
    "parity_rows",
    "behavior_notes",
    "gate_ids",
    "unit",
    "boundary",
    "error",
    "resource",
    "cancellation",
    "failure_atomicity",
    "property",
    "metamorphic",
    "fuzz",
    "mutation",
    "fault",
    "scenarios",
    "negative_recovery",
    "artifacts",
)
VERIFICATION_COVERAGE_REQUIRED_FIELDS = frozenset(
    {
        "requirement_ids",
        "claim_ids",
        "gate_ids",
        "unit",
        "boundary",
        "error",
        "resource",
        "cancellation",
        "failure_atomicity",
        "scenarios",
        "negative_recovery",
        "artifacts",
    }
)

# --- Sealed compiler environment (bead fln-evidence-runner-bootstrap-btk) ----
# Ambient channels that can alter what the pinned compiler does (cap-lints
# injection, wrapper substitution, alternate-toolchain selection, rustflags in
# every spelling). Presence of ANY of these when the sealed-cargo lane is
# requested is a typed setup fault — rejected before any repo-controlled
# compilation, never silently scrubbed.
HOSTILE_COMPILER_ENV_EXACT = frozenset(
    {
        "RUSTFLAGS",
        "CARGO_ENCODED_RUSTFLAGS",
        "CARGO_BUILD_RUSTFLAGS",
        "CARGO_BUILD_RUSTC",
        "CARGO_BUILD_RUSTC_WRAPPER",
        "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
        "CARGO_BUILD_RUSTDOC",
        "CARGO_BUILD_TARGET",
        "RUSTC",
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
        "RUSTDOC",
        "RUSTDOCFLAGS",
        "RUSTUP_TOOLCHAIN",
        "CARGO",
    }
)
HOSTILE_COMPILER_ENV_PREFIXES = (
    "CARGO_TARGET_",  # CARGO_TARGET_<TRIPLE>_RUSTFLAGS / _LINKER / _RUNNER …
    "CARGO_ALIAS_",
    "CARGO_UNSTABLE_",
    "CARGO_REGISTRIES_",
    "CARGO_PROFILE_",
)
# Python's isolated mode ignores every interpreter configuration channel in
# this family. Record the names that were present so isolation never becomes
# silent environment scrubbing.
PYTHON_CONFIGURATION_ENV_EXACT = frozenset(
    {
        "PYTHONPATH",
        "PYTHONHOME",
        "PYTHONSTARTUP",
        "PYTHONEXECUTABLE",
        "PYTHONUSERBASE",
        "PYTHONNOUSERSITE",
        "PYTHONSAFEPATH",
    }
)
PYTHON_CONFIGURATION_ENV_PREFIXES = ("PYTHON",)
# Compiler state intentionally replaced by the sealed-cargo lane. Python
# configuration is not in this set: the interpreter envelope rejects it
# before target spawn instead of silently sanitizing it.
SEALED_ENV_OVERRIDDEN = frozenset({"CARGO_HOME", "CARGO_TARGET_DIR"})
# Ambient variables admitted into the sealed child environment as-is. PATH is
# REBUILT (pinned toolchain bin first), never inherited.
SEALED_ENV_ALLOWLIST = frozenset(
    {"HOME", "USER", "LOGNAME", "SHELL", "TERM", "LANG", "TZ", "TMPDIR"}
)
SEALED_PATH_TAIL = "/usr/local/bin:/usr/bin:/bin"
SEALED_HOST_TRIPLES = {
    "x86_64": "x86_64-unknown-linux-gnu",
    "aarch64": "aarch64-unknown-linux-gnu",
}
SEALED_RUSTC_PROBE_TIMEOUT_S = 30
CHECK_STAGE_ORDER = [
    "evidence-self-test",
    "verification-manifest",
    "shellcheck",
    "fmt",
    "check",
    "clippy",
    "test",
    "tribunal-manifest-inventory",
    "epoch-lab-test",
    "epoch-lab-live-verify",
    "structure-guard",
    "vendor-tree",
    "ubs",
]
CHECK_SELF_TEST_ORDER = [*CHECK_STAGE_ORDER, "cancel-term"]
E2E_STEP_ORDERS = {
    "unsafe_note_clippy": [
        "clippy_report",
        "baseline_match",
        "undeclared_site_mutant",
        "undeclared_site_recovery",
        "stale_declaration_mutant",
        "stale_declaration_recovery",
    ],
    "contract_handoff": [
        "cold_regeneration_a",
        "cold_regeneration_b",
        "canonical_join",
        "generated_compile",
        "markdown_only_mutant",
        "markdown_only_recovery",
        "constants_only_mutant",
        "constants_only_recovery",
        "policy_omission_mutant",
        "policy_omission_recovery",
        "stale_policy_mutant",
        "stale_policy_recovery",
        "duplicate_policy_mutant",
        "duplicate_policy_recovery",
        "incompatible_schema_mutant",
        "incompatible_schema_recovery",
        "mixed_pin_mutant",
        "mixed_pin_recovery",
        "mixed_reference_mutant",
        "mixed_reference_recovery",
        "host_target_substitution_mutant",
        "host_target_substitution_recovery",
        "partial_publication_mutant",
        "partial_publication_recovery",
        "cancelled_publication_mutant",
        "cancelled_publication_recovery",
        "resource_exhaustion_mutant",
        "resource_exhaustion_recovery",
        "suppressed_drift_mutant",
        "suppressed_drift_recovery",
        "reference_path_mutant",
        "reference_path_recovery",
        "mock_consumer_mutant",
        "mock_consumer_recovery",
        "final_handoff",
    ],
    "closure_audit": [
        "build_guard",
        "freeze_guard",
        "real_closure",
        "copy_seeded_fixture",
        "seeded_registry_package",
        "copy_recovery_fixture",
        "closure_recovery",
        "final_real_recheck",
    ],
    "structure_gate": [
        "build_guard",
        "verify_built_guard",
        "freeze_guard",
        "verify_frozen_guard",
        "real_workspace",
        "robot_setup_failure",
        "copy_unacknowledged",
        "seeded_unacknowledged",
        "copy_acknowledged",
        "seeded_acknowledged",
        "copy_dependency_recovery",
        "dependency_recovery",
        "copy_unledgered",
        "seeded_unledgered",
        "copy_ledgered_recovery",
        "ledger_recovery",
        "copy_exported",
        "seeded_export",
        "copy_export_recovery",
        "export_recovery",
        "copy_nested_cargo_config",
        "seeded_nested_cargo_config",
        "copy_legacy_toolchain",
        "seeded_legacy_toolchain",
        "copy_decoy_toolchain",
        "seeded_decoy_toolchain",
        "copy_config_recovery",
        "config_recovery",
        "crate_dir_invocation",
        "tool_dir_invocation",
        "resource_exhaustion",
        "resource_recovery",
        "cancellation",
        "cancellation_recovery",
        "final_real_recheck",
    ],
    "environment_collision": [
        "collision_positive",
        "collision_mutant",
        "collision_recovery",
    ],
    "environment_resource_collision": [
        "resource_positive",
        "resource_mutant",
        "resource_recovery",
    ],
    "declaration_tag_matrix": [
        "declaration_tag_matrix",
    ],
    "declaration_membership": [
        "declaration_membership",
    ],
    "extension_descriptor_matrix": [
        "extension_descriptor_matrix",
    ],
    "env_snapshots": [
        "environment_suite",
        "environment_state",
        "declaration_admission",
        "extension_merge_refusals",
        "set_union",
        "extension_state_mutant",
        "extension_state_recovery",
        "set_union_mutant",
        "set_union_recovery",
        "declaration_membership_mutant",
        "declaration_membership_recovery",
        "declaration_tag_mutant",
        "declaration_tag_recovery",
        "extension_descriptor_mutant",
        "extension_descriptor_recovery",
        "extension_descriptor_validation_deferred_mutant",
        "extension_descriptor_validation_deferred_recovery",
        "extension_ancestry_only_length_mutant",
        "extension_ancestry_only_length_recovery",
        "declaration_budget_check_omission_mutant",
        "declaration_budget_check_omission_recovery",
        "declaration_cancellation_as_resource_mutant",
        "declaration_cancellation_as_resource_recovery",
        "declaration_plan_base_binding_omission_mutant",
        "declaration_plan_base_binding_omission_recovery",
        "declaration_bytes_unit_hardcoded_mutant",
        "declaration_bytes_unit_hardcoded_recovery",
        "checkpoint_base_digest_collision_mutant",
        "checkpoint_base_digest_collision_recovery",
        "checkpoint_prefix_digest_collision_mutant",
        "checkpoint_prefix_digest_collision_recovery",
        "checkpoint_schema_omission_mutant",
        "checkpoint_schema_omission_recovery",
        "checkpoint_cumulative_facts_omission_mutant",
        "checkpoint_cumulative_facts_omission_recovery",
        "checkpoint_entry_identity_omission_mutant",
        "checkpoint_entry_identity_omission_recovery",
        "declaration_tag_matrix",
        "declaration_membership",
        "extension_descriptor_matrix",
        "environment_collision",
        "environment_resource_collision",
    ],
    "verdict_schema": [
        "positive",
        "failure",
        "recovery",
        "final_real_recheck",
    ],
    "kernel_replay": [
        "decoder_suite",
        "admission_replay",
        "census_floor",
        "corruption",
        "corruption_recovery",
        "resource_exhaustion",
        "resource_recovery",
        "cancellation",
        "cancellation_recovery",
        "internal_fault_probe",
        "final_real_recheck",
    ],
    "vellum_naming_no_mock_e2e": [
        "registry_gate",
        "collision_model",
        "drift_guard",
        "surface_scan",
        "copy_fixture",
        "scratch_baseline",
        "seeded_stale_doc",
        "restore_stale_doc",
        "recovery_stale_doc",
        "seeded_registry_conflict",
        "restore_registry_conflict",
        "recovery_registry_conflict",
        "seeded_generated_drift",
        "restore_generated_drift",
        "recovery_generated_drift",
        "seeded_stale_candidate",
        "quarantine_candidate",
        "verify_publication_intact",
        "recovery_stale_candidate",
        "determinism_scan_a",
        "determinism_scan_b",
        "determinism_byte_compare",
        "final_real_recheck",
    ],
}
SHA256_HEX = re.compile(r"[0-9a-f]{64}")

VERDICT_SEMANTIC_SCHEMA = "fln.e2e.verdict-semantic"
VERDICT_TELEMETRY_SCHEMA = "fln.e2e.verdict-telemetry"
VERDICT_SCHEMA_VERSION = 1
VERDICT_WIRE_MAGIC = b"FLNVRDCT"
VERDICT_WIRE_HEADER_BYTES = 13
VERDICT_MAX_SEMANTIC_BYTES = 65_536
VERDICT_MAX_TELEMETRY_BYTES = 4_096
VERDICT_MAX_ENCODED_BYTES = 256 * 1024 * 1024
VERDICT_MAX_WORKERS = 41
VERDICT_FAILURE_MARKER = (
    "FLN_VERDICT_E2E_EXPECTED_FAILURE: unknown proof opcode 255 at byte 21"
)

ENVIRONMENT_COLLISION_SCHEMA = "fln.e2e.environment-collision"
ENVIRONMENT_COLLISION_VERSION = 2
ENVIRONMENT_COLLISION_THREADS = (1, 8, 32)
ENVIRONMENT_COLLISION_CARDINALITY = 96
ENVIRONMENT_COLLISION_TEST = (
    "pmap::tests::environment_collision_e2e_emits_detailed_real_path_evidence"
)
ENVIRONMENT_COLLISION_MUTANT_MARKER = (
    "collision enumeration diverged: threads=1"
)
ENVIRONMENT_COLLISION_FIELDS = {
    "schema",
    "version",
    "run_id",
    "bead",
    "claim_id",
    "claim_type",
    "invariant_id",
    "invariant_relation",
    "gate_id",
    "gate_relation",
    "parity_ledger_row",
    "data_grade",
    "epoch",
    "mode",
    "profile",
    "platform",
    "seed",
    "cache_state",
    "canonical_input_root",
    "scenario",
    "schedule_id",
    "status",
    "cwd",
    "argv",
    "stdout_artifact",
    "stderr_artifact",
    "collision_cardinality",
    "collision_hash",
    "threads",
    "workers_built",
    "distinct_insertion_orders",
    "representative_insertion_order",
    "worker_insertion_orders",
    "expected_enumeration",
    "actual_enumeration",
    "worker_enumerations",
    "expected_root",
    "actual_root",
    "worker_roots",
    "enumeration_insert_operations",
    "environment_insert_operations",
    "environment_duplicate_checks",
    "observed_enumeration_nodes",
    "observed_environment_entries",
    "theoretical_fresh_node_bound_per_insert",
    "theoretical_replaced_node_bound_per_insert",
    "operation_budget",
    "bucket_policy",
    "lookup_complexity",
    "insert_complexity",
    "resource_followup",
    "monotonic_start_us",
    "monotonic_end_us",
    "duration_us",
    "timing_used_as_gate",
    "process_exit",
    "signal",
    "first_divergence",
    "cleanup_status",
    "final_state",
}

ENVIRONMENT_RESOURCE_COLLISION_SCHEMA = "fln.e2e.environment-resource-collision"
ENVIRONMENT_RESOURCE_COLLISION_VERSION = 1
ENVIRONMENT_RESOURCE_COLLISION_THREADS = (1, 8, 32)
ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY = 1_000
ENVIRONMENT_RESOURCE_COLLISION_TEST = (
    "pmap::tests::environment_collision_resource_e2e_emits_detailed_evidence"
)
DECLARATION_TAG_MATRIX_SCHEMA = "fln.e2e.declaration-tag-matrix"
DECLARATION_TAG_MATRIX_TEST = (
    "environment::tests::"
    "declaration_tag_matrix_e2e_emits_detailed_real_path_evidence"
)
DECLARATION_MEMBERSHIP_SCHEMA = "fln.e2e.declaration-membership"
DECLARATION_MEMBERSHIP_TEST = (
    "environment::tests::"
    "declaration_membership_matrix_e2e_emits_detailed_real_path_evidence"
)
EXTENSION_DESCRIPTOR_MATRIX_SCHEMA = "fln.e2e.extension-descriptor-matrix"
EXTENSION_DESCRIPTOR_MATRIX_TEST = (
    "extensions::tests::"
    "extension_descriptor_matrix_e2e_emits_detailed_real_path_evidence"
)
ENVIRONMENT_STATE_SCHEMA = "fln.e2e.environment-state"
ENVIRONMENT_STATE_TEST = (
    "extensions::tests::environment_state_e2e_emits_detailed_real_path_evidence"
)
DECLARATION_ADMISSION_SCHEMA = "fln.e2e.declaration-admission"
DECLARATION_ADMISSION_SUMMARY_SCHEMA = "fln.e2e.declaration-admission-summary"
DECLARATION_ADMISSION_TEST = (
    "environment::tests::"
    "declaration_admission_e2e_emits_detailed_real_path_evidence"
)
DECLARATION_ADMISSION_ARGV = (
    "cargo test --locked -q -p fln-env "
    "environment::tests::"
    "declaration_admission_e2e_emits_detailed_real_path_evidence "
    "-- --exact --nocapture"
)
DECLARATION_ADMISSION_INPUT_ROOT = (
    "2c9b97e5b882fa9495b69e462c8fbf2d"
    "b35a1e4cb0ea3953a357a6549756e388"
)
DECLARATION_ADMISSION_BASE_ROOT = (
    "36c2a8439e46a92cdd1ed0e0eebaa5ff"
    "16728730342e5f13a4994eb199392b04"
)
DECLARATION_ADMISSION_UNBOUNDED_BUDGET = {
    "max_level_params": (1 << 64) - 1,
    "max_mutual_rows": (1 << 64) - 1,
    "max_constructor_rows": (1 << 64) - 1,
    "max_recursor_rules": (1 << 64) - 1,
    "max_canonical_bytes": (1 << 64) - 1,
    "max_expr_nodes": (1 << 64) - 1,
    "max_expanded_weight": (1 << 64) - 1,
}
DECLARATION_ADMISSION_REFUSALS = (
    (
        "level_params",
        True,
        "declaration-preflight",
        3,
        "produced nodes",
        "level_params",
    ),
    (
        "mutual_rows",
        True,
        "declaration-preflight",
        3,
        "produced nodes",
        "mutual_rows",
    ),
    (
        "constructor_rows",
        True,
        "declaration-preflight",
        3,
        "produced nodes",
        "constructor_rows",
    ),
    (
        "recursor_rules",
        True,
        "declaration-preflight",
        3,
        "produced nodes",
        "recursor_rules",
    ),
    (
        "canonical_bytes",
        True,
        "declaration-preflight",
        49,
        "input bytes",
        "canonical_bytes",
    ),
    (
        "expr_nodes",
        False,
        "term-weight-preflight",
        1,
        "produced nodes",
        "produced nodes",
    ),
    (
        "expanded_weight",
        False,
        "term-weight-preflight",
        1,
        "expanded weight",
        "expanded weight",
    ),
)
DECLARATION_ADMISSION_RECOVERIES = (
    (
        "level_params",
        {
            "level_params": 3,
            "mutual_rows": 0,
            "constructor_rows": 0,
            "recursor_rules": 0,
            "canonical_bytes": 108,
            "expressions": 1,
            "expr_nodes": 1,
            "expanded_weight": 1,
            "max_logical_depth": 1,
        },
        "e943a96e436d76198c42827054fb8cfe0330eb32b2d7a414e94c0e58f84b0610",
        "7d7a4b653fc6472bd51122d6b0cbc61122290f6f445a55f2b0372e198f0de4a6",
    ),
    (
        "mutual_rows",
        {
            "level_params": 0,
            "mutual_rows": 3,
            "constructor_rows": 0,
            "recursor_rules": 0,
            "canonical_bytes": 119,
            "expressions": 2,
            "expr_nodes": 2,
            "expanded_weight": 2,
            "max_logical_depth": 1,
        },
        "72dc754d4e3c0b612fd6ba8f95ade80ca32218b25d1ff59826bffa311a9c52cb",
        "9317645e979403f913e9a970aaed3267003d2caad9a12281c81464c9c0b5c720",
    ),
    (
        "constructor_rows",
        {
            "level_params": 0,
            "mutual_rows": 0,
            "constructor_rows": 3,
            "recursor_rules": 0,
            "canonical_bytes": 142,
            "expressions": 1,
            "expr_nodes": 1,
            "expanded_weight": 1,
            "max_logical_depth": 1,
        },
        "89625df1d9a219a607e34fd5d104dd2772a3b548a382e7d1b0fbb534c171bf58",
        "b5a9f4ac94ec73b878077be1d6d8f056cf6ec73f5a07a7ee554975604dea1ac5",
    ),
    (
        "recursor_rules",
        {
            "level_params": 0,
            "mutual_rows": 0,
            "constructor_rows": 0,
            "recursor_rules": 3,
            "canonical_bytes": 162,
            "expressions": 4,
            "expr_nodes": 4,
            "expanded_weight": 4,
            "max_logical_depth": 1,
        },
        "fca53bc92f871456aae85b68feae2cda602bbed512bf85398782ebf1b0c10ecb",
        "cc710f134162ab3a2b81dda84207de356e5951a41e9714284caa1f040fd613ef",
    ),
    (
        "canonical_bytes",
        {
            "level_params": 0,
            "mutual_rows": 0,
            "constructor_rows": 0,
            "recursor_rules": 0,
            "canonical_bytes": 51,
            "expressions": 1,
            "expr_nodes": 1,
            "expanded_weight": 1,
            "max_logical_depth": 1,
        },
        "d5394a6026d58bbdab954a26875bc0d638d900b2684ce6577285c7d4207ba16f",
        "87ecc4a3c635622312e76fe052d3fdddd1317b9f08d429f318140eaf7986562f",
    ),
    (
        "expr_nodes",
        {
            "level_params": 0,
            "mutual_rows": 0,
            "constructor_rows": 0,
            "recursor_rules": 0,
            "canonical_bytes": 51,
            "expressions": 1,
            "expr_nodes": 1,
            "expanded_weight": 1,
            "max_logical_depth": 1,
        },
        "5be901abbb47830e0e9012425f3a884496396ad6f07e737f6e35c8ba3cf497cf",
        "6571f8d9c64ec46adb0c37087013877154b93eed6119a95fc7e8a6f95e072680",
    ),
    (
        "expanded_weight",
        {
            "level_params": 0,
            "mutual_rows": 0,
            "constructor_rows": 0,
            "recursor_rules": 0,
            "canonical_bytes": 51,
            "expressions": 1,
            "expr_nodes": 1,
            "expanded_weight": 1,
            "max_logical_depth": 1,
        },
        "bf7355fea0d48ce916cd0902653737891fa9679c7b6715bf35a7c9e6daf5129d",
        "99eaf30ea59a11de8559ed638cfa14f3383546f2c450b2e841c5fd568967cbdb",
    ),
)
ENVIRONMENT_IDENTITY_VERSION = 1
DECLARATION_TAG_GOLDENS = {
    ("definition_safety", "unsafe"): (
        "definition",
        0,
        286,
        "157d1d61733828db775de4ee898c84ab608f57ca609965b7d8aba3ef9e3a1a5e",
        "e6e48d3267b42c87425ac704373120f0c4624c591f6c3218412cdfd5464443ab",
    ),
    ("definition_safety", "safe"): (
        "definition",
        1,
        286,
        "e3a242872a3ffd8c515331f5821c1b42f81780060413feb33f2d63ca8aeb697d",
        "5995ca5cc9f678192cb1700abb6bc18a87af673a6f3285cc9d55caa9b20bb6b0",
    ),
    ("definition_safety", "partial"): (
        "definition",
        2,
        286,
        "00a37c5b26ce2df45b79a0e5ddc0b32fe7ba3fd16e2267a8b199a3a2a5421f52",
        "5a313316b29da1dab36b88cd02d1d52b96b025a3cb6b9682d0ba10eb59ae76d1",
    ),
    ("quot_kind", "type"): (
        "quotient",
        0,
        157,
        "d85f3e7116bf264784bad45e2d9a9acc9ad69ca15c2387f73d390b51c1a52674",
        "64a010c5b799b51b464f4394db8f06a4d7f0c8f98a89bc634cddf3936f3a431f",
    ),
    ("quot_kind", "ctor"): (
        "quotient",
        1,
        157,
        "7a209bee80a459d0eddd0e82ced0b96345895dfdf11cb420729783eff42fe0a0",
        "d8fc3394629ba859ee37b56dd6d937d787aa86b607b02941091a8699983e0589",
    ),
    ("quot_kind", "lift"): (
        "quotient",
        2,
        157,
        "706326aa022cfa4b76f80ea32c04ad0aef70d796da8762b86771b3b4d42937ad",
        "804e0ddc5baea6f095d63662b95d303a11c7f33cc92c8d5c77efeb96df021706",
    ),
    ("quot_kind", "ind"): (
        "quotient",
        3,
        157,
        "32cecea0df45330f5ea249486eb8c0dd4ff236dc27ca90e79122de9f7e3d365a",
        "7e0d5346e053845bda23a4fb2f3edf80f7daa3f86898a129d66d0531e0e22066",
    ),
}
ENVIRONMENT_RESOURCE_COLLISION_INPUT_ROOT = (
    "fln-fixture:fe1a2f87707d8edea65e8d4d61db5a1882c838b3e1975ec55b136af78f154dfe"
)
ENVIRONMENT_RESOURCE_COLLISION_HASH = "955ee3fb336886cc"
ENVIRONMENT_RESOURCE_COLLISION_ROOT = (
    "0da9877d9661335524ca1609c621ea2f422477497f686f85192276e1eb05cee7"
)
ENVIRONMENT_RESOURCE_COLLISION_RECOVERY_ROOT = (
    "e4e233d685c5ee4e14cd844d572b2edf4e9d06c866725687ea420328acccdea1"
)
ENVIRONMENT_RESOURCE_COLLISION_MUTANT_MARKER = (
    "assertion `left == right` failed\n  left: 28\n right: 36"
)
ENVIRONMENT_RESOURCE_COLLISION_INSERTION_ROOTS = {
    1: (
        "fln-fixture:08b7f939ec36c28d93fed144bb9a730d2503ec099edf0bb96a2721bdfc60e325",
    ),
    8: (
        "fln-fixture:99505071fe809c63f3697903ffec2eda89e6c01863753411d836949edbc7a2e6",
        "fln-fixture:8b04654a127358f5e2c8eb41f6b1cc7c13dc8b446158aa38d8aa1f9183865de5",
        "fln-fixture:bc8b3d07a5bc1aac1d29cecbae910d3038d8513cc1ff82d45ffb825cdc0eeb03",
        "fln-fixture:42f2d932971f941232fa0816cd9f98b5d904f8e204d39ee9f094d5fbc16d9fd7",
        "fln-fixture:1fbe351925b9c7471949e52d40348549e32b9693940ebc053e119abb079cfdcc",
        "fln-fixture:83cfa2c1a11bacabe8c9a7db97d3dd8feff2337d682f09e44a878c4307783409",
        "fln-fixture:758772e6db8c89facab28fa52f2438b06d12bb1f87eb67c3ec3334484fdb36ea",
        "fln-fixture:347431134d05dfe0684f987276f9ea0af399fdd8cda5908f7be63f1b27679a0a",
    ),
    32: (
        "fln-fixture:dc8dfffd8012c09e9ce97bff90702d1dc0bd3f23b005086126c2e0e669df821a",
        "fln-fixture:8851bb87719923be75013cff4ef4732c27b1ad6a82315e2f54e6268aa2f498cc",
        "fln-fixture:fd3712db2016ece30d8475037e1229f560bb485d3038a21988099612d8ae3413",
        "fln-fixture:c25f4e4895ec135269205442c0f598a76cd6d7dcb461c82caa3a841ccae2fe42",
        "fln-fixture:75c3b37eb151113836a8185f0242a50d9a290574f7f6553b845d52b68d11d90a",
        "fln-fixture:d5b92dcbe784c645232d77e9f7f970143e8c9eab45d29bdff3dcaf510b55f78d",
        "fln-fixture:a5889ad8e06e4adc20cb5295e4586ea53c3287bba0027131ae2c38d657397cf3",
        "fln-fixture:c835c428ac132b9aa01a612b95c72205f194392707184c5cf084888ab2782a08",
        "fln-fixture:a2b3bdd0e6a2faac7afa1228cadf7f5d1b78b4b38e75aa8a583adfdf8fa4bfc0",
        "fln-fixture:7f97ee3ac100deee413ad5b2be458fbe58e7ffe72f44075e524100fcceb09dd7",
        "fln-fixture:fa7efe8ab864ea61ca56f6a9a8dbe710aab8cc28631599d23f13bdf7eafb622e",
        "fln-fixture:2f2792a3cc195756d88edd8591a905a2f17ea7b709369069ada462d1ad0236cd",
        "fln-fixture:845b34ac7ca419fc02974b6ecfb524de75b61b7bb4c96839c2aab506bc3636db",
        "fln-fixture:bf437a9fc884c07f167dc1c1a319c5cd62f2ef3889f4b476c7f98657b79f821c",
        "fln-fixture:35d9052b65b94ae647d57af45a275df3e8d0c4c0bc47d2075503360da781907a",
        "fln-fixture:b436bdbb426509d697ed7553a624d2d02444ac27144bf961926b28618cbdb54d",
        "fln-fixture:2d967bc6d3f7b5d9a60b5491f85c6d8947e51b350566e5fe48aeb48ec5ff0ef6",
        "fln-fixture:15e7bf1d442d3efa38ffa2101f57317ce3d238c740c3309f69c3bbcf7374d619",
        "fln-fixture:812e68d06a379f613d766067e62dc2b7372250ac3c457cb0b388fd8f01953121",
        "fln-fixture:eef976e9839c50a6287ac3882ad0f1e42a5e6dae2d5fd634880eabb17465a664",
        "fln-fixture:f129e4e550b451ffa6e304a2482ff09b82200f4f69d4736fd17d7cf60081f5c5",
        "fln-fixture:c921b3088bce5c6a6389f02ace3a6fe2fde45d74de5d1236a60423d3c74a725c",
        "fln-fixture:efd74cfe56fc7b3c9249b88d5a24bf7dd3cd746150ef5fdb284cea69139ef45f",
        "fln-fixture:a918832f110875da273bac6892cfe0442bcc562504643bed55e6eadf70e5ef31",
        "fln-fixture:22603dbfa9666ee2c1fd9e6f054aa61b81262458fec4f18c22e4400f8394e64a",
        "fln-fixture:8b203ad6ccc731d032c23568280c3aa210dffffbdde97f13787df711d4c476c6",
        "fln-fixture:7c98700104a2894bbd06b7caff021252fe24d53b73fd6db8247df57731e65d02",
        "fln-fixture:d6deb752327aac38c2bd8d7a5f729e454a861b67cb24c1deb1b491f57875c0fd",
        "fln-fixture:ca0a0d538ebcc735c82df9f0a3402d4c9678926954368b7c2e463b48afcffab1",
        "fln-fixture:fef909b8b7aed09f264d00a87c263db945590bce848429488901d0f6e07336f2",
        "fln-fixture:4749f2b23180c6a7ba4bab54cfe4f7fa6eff17be58af01d6102ac85710bf57aa",
        "fln-fixture:c436f1f87725a813b5bc206d23e260a9fd3559006d8535556a92f28492ebbc2f",
    ),
}
ENVIRONMENT_RESOURCE_COLLISION_FIELDS = {
    "schema",
    "version",
    "run_id",
    "bead",
    "claim_id",
    "claim_type",
    "invariant_id",
    "invariant_relation",
    "gate_id",
    "gate_relation",
    "parity_ledger_row",
    "data_grade",
    "epoch",
    "mode",
    "profile",
    "platform",
    "seed",
    "cache_state",
    "canonical_input_root",
    "scenario",
    "schedule_id",
    "status",
    "cwd",
    "argv",
    "stdout_artifact",
    "stderr_artifact",
    "collision_cardinality",
    "collision_hash",
    "threads",
    "workers_built",
    "distinct_insertion_orders",
    "representative_insertion_order",
    "worker_insertion_order_roots",
    "expected_order",
    "actual_order",
    "worker_enumeration_roots",
    "expected_root",
    "actual_root",
    "worker_roots",
    "expected_recovery_root",
    "actual_recovery_root",
    "worker_recovery_roots",
    "representation_tier",
    "secondary_identity",
    "secondary_hashing",
    "secondary_identity_collision_behavior",
    "promotion_cardinality",
    "demotion_cardinality",
    "comparisons",
    "fresh_map_nodes",
    "fresh_collision_nodes",
    "cloned_inline_entries",
    "final_collision_nodes",
    "snapshot_root_arc_bumps",
    "snapshot_shared_collision_nodes",
    "append_shared_collision_nodes",
    "append_fresh_nodes",
    "max_lookup_comparisons",
    "budget",
    "bounds",
    "resources",
    "monotonic_start_us",
    "monotonic_end_us",
    "duration_us",
    "timing_used_as_gate",
    "process_exit",
    "signal",
    "first_divergence",
    "cleanup_status",
    "final_state",
}

KERNEL_ADMISSION_SCHEMA = "fln.e2e.kernel-admission"
KERNEL_ADMISSION_FAULT_SCHEMA = "fln.e2e.kernel-admission-fault"
KERNEL_ADMISSION_VERSION = 2
KERNEL_ADMISSION_THREADS = (1, 8, 32)
KERNEL_ADMISSION_TESTS = (
    "prelude_replays_through_the_kernel",
    "admission_fault_matrix_is_typed_and_atomic",
)
KERNEL_ADMISSION_BUDGET_STEPS = 10_000_000
KERNEL_ADMISSION_BUDGET_DEPTH = 4_096
# The pinned Init.Prelude verdict census (beads franken_lean-irm +
# franken_lean-ap6). Moves only with a deliberate, bead-tracked change.
KERNEL_ADMISSION_CENSUS = {
    "decls_total": 2204,
    "checked": 2198,
    "accepted": 2198,
    "rejected_total": 0,
    "inconclusive": 0,
    "artifact_incomplete": 6,
    "nested_partial_blocks": 0,
    "nested_full_blocks": 1,
}
# The typed artifact-incomplete census at the pin (bead
# franken_lean-artifact-incomplete-private-refs-sgt): six non-safe
# implementation helpers whose private auxiliaries the pin's serializer
# discarded. Each row is (declaration, safety, missing references) in
# canonical order; the witness digest binds the exact finding set
# (fln-env decl_closure, tag fln.artifact-incomplete-witness/2 — version 2
# binds the structural Name rather than its display form, which was not
# injective; bead franken_lean-f6br). These rows
# are inconclusive-family outcomes: never checked, never cacheable, never
# environment-admissible — and never folded into a success total.
KERNEL_ADMISSION_ARTIFACT_WITNESS = (
    "c7fa135fc4f85a21488bfc2393cbe4f7fa81b13205dbf18023ced322b829e015"
)
KERNEL_ADMISSION_ARTIFACT_ROWS = (
    (
        "Lean.Name.hash._override",
        "unsafe",
        ("_private.Init.Prelude.0.Lean.Name.hash._proof_1",),
    ),
    (
        "Lean.Name.num._override",
        "unsafe",
        ("_private.Init.Prelude.0.Lean.Name.hash._proof_2",),
    ),
    (
        "Lean.Syntax.getHeadInfo?._unsafe_rec",
        "partial",
        ("_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1",),
    ),
    (
        "Lean.Syntax.getTailPos?._unsafe_rec",
        "partial",
        ("_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1",),
    ),
    (
        "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
        "partial",
        ("_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1",),
    ),
    (
        "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
        "partial",
        ("_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop.match_1",),
    ),
)
# The named single-defect admission mutants (bead franken_lean-ap6): every
# one must be killed by a typed rejection in the fault matrix.
KERNEL_ADMISSION_MUTANTS = (
    "tampered_recursor_rhs",
    "nonpositive_ctor_field",
    "inverted_universe_ctor_field",
    "quotient_missing_member",
    "definition_type_swap",
    "mutual_membership_mismatch",
)
KERNEL_ADMISSION_RESOURCE_PHASES = {
    "resource_boundary_exact_accept": "accepted",
    "resource_exhaustion_steps": "inconclusive:Steps",
    "resource_exhaustion_depth": "inconclusive:Depth",
    "resource_recovery": "accepted",
}
_KERNEL_ADMISSION_COMMON_FIELDS = {
    "schema",
    "version",
    "run_id",
    "bead",
    "claim_id",
    "claim_type",
    "invariant_id",
    "invariant_relation",
    "determinism_invariant",
    "gate_id",
    "gate_relation",
    "parity_ledger_row",
    "data_grade",
    "epoch",
    "mode",
    "profile",
    "platform",
    "seed",
    "cache_state",
    "canonical_input_root",
    "scenario",
    "cwd",
    "argv",
    "stdout_artifact",
    "stderr_artifact",
    "phase",
    "status",
    "budget_steps",
    "budget_depth",
    "monotonic_start_us",
    "monotonic_end_us",
    "duration_us",
    "timing_used_as_gate",
    "process_exit",
    "signal",
    "first_divergence",
    "cleanup_status",
    "final_state",
}
KERNEL_ADMISSION_FIELDS = _KERNEL_ADMISSION_COMMON_FIELDS | {
    "threads",
    "decls_total",
    "units_total",
    "units_checked",
    "units_cyclic",
    "checked",
    "accepted",
    "rejected_total",
    "inconclusive",
    "artifact_incomplete",
    "artifact_incomplete_witness",
    "nested_partial_blocks",
    "nested_full_blocks",
    "verdict_stream_digest",
    "final_logical_root",
    "steps_used_total",
    "max_depth_seen",
}
# The per-declaration artifact-incomplete rows carry the shared governance
# prefix (no supervisor/timing tail — they are census rows, not phases) plus
# the finding facts and the authority denials.
KERNEL_ADMISSION_ARTIFACT_ROW_FIELDS = (
    _KERNEL_ADMISSION_COMMON_FIELDS
    - {
        "status",
        "budget_steps",
        "budget_depth",
        "monotonic_start_us",
        "monotonic_end_us",
        "duration_us",
        "timing_used_as_gate",
        "process_exit",
        "signal",
        "first_divergence",
        "cleanup_status",
        "final_state",
    }
) | {
    "declaration",
    "safety",
    "missing_references",
    "witness",
    "outcome",
    "authority",
    "kernel_checked",
    "cacheable",
    "environment_admissible",
    "evidence_grade",
}
KERNEL_ADMISSION_FAULT_FIELDS = _KERNEL_ADMISSION_COMMON_FIELDS | {
    "mutant_id",
    "target",
    "expected_outcome",
    "actual_outcome",
    "reject_class",
    "message_excerpt",
    "steps_used",
    "max_depth",
    "root_before",
    "root_after",
    "atomicity_held",
    "recovery_outcome",
}

MAX_RECORD_BYTES = 1_048_576
MAX_LOG_BYTES = 67_108_864
MAX_EXEC_STATUS_BYTES = 4096
STOPPED_GATE_READY_TOKEN = b"fln-private-ready-v1\n"
STOPPED_GATE_RELEASE_TOKEN = b"fln-private-release-v1\n"
SUPERVISOR_TEST_FAULT_POINTS = {
    "none",
    "admission_fd_exhaustion",
    "capture_stdout",
    "capture_stderr",
    "metadata_parent_open",
    "readiness_publication",
    "thread_start_stdout",
    "thread_start_stderr",
}
PROCESS_GROUP_FREEZE_ATTEMPTS = 8
PROCESS_GROUP_FREEZE_TIMEOUT_S = 10.0
PROCESS_GROUP_KILL_ATTEMPTS = 2000
PROCESS_GROUP_KILL_TIMEOUT_S = 10.0
MAX_PROCESS_IDENTITY_WAIT_MS = 30_000
# A caller may consume one full identity-bind budget before starting two full
# launch-release attempts.  The guardian must remain inert across that entire
# bounded handoff, with a small scheduling margin, or equal deadlines race.
GUARDIAN_LAUNCH_RELEASE_TIMEOUT_MS = MAX_PROCESS_IDENTITY_WAIT_MS * 3 + 5_000
SECRET_KEY = re.compile(
    r"(?i)(authorization|bearer|password|passwd|secret|token|api[_-]?key|private[_-]?key)"
)


class EvidenceError(RuntimeError):
    """A fail-closed evidence production or validation error."""


class SetupTimeoutError(EvidenceError):
    """The target never reached its inert admission state within setup budget."""


class SetupCancelledError(EvidenceError):
    """Cancellation won before the target was released to execute."""


class SealedCompilerRejection(EvidenceError):
    """The sealed-cargo lane refused to run: hostile or unverifiable ambient
    compiler environment. Carries the typed reason token for the terminal
    envelope and the partial sealing facts gathered before rejection."""

    def __init__(
        self, reason_token: str, detail: str, facts: dict[str, Any] | None = None
    ) -> None:
        super().__init__(detail)
        self.reason_token = reason_token
        self.facts = facts


class SealedInterpreterRejection(EvidenceError):
    """The evidence supervisor refused to run under an unsealed or hostile
    Python configuration. The trusted interpreter still publishes a typed
    terminal envelope, but the target is never spawned."""

    def __init__(
        self, reason_token: str, detail: str, facts: dict[str, Any]
    ) -> None:
        super().__init__(detail)
        self.reason_token = reason_token
        self.facts = facts


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat(timespec="milliseconds")


def overridden_python_environment(environ: Mapping[str, str]) -> list[str]:
    """Return ambient Python configuration names ignored by ``-I`` and refused.

    Values are deliberately never copied into evidence: names prove the
    attempted channel was classified, while values may contain host data.
    """

    return sorted(
        name
        for name in environ
        if name in PYTHON_CONFIGURATION_ENV_EXACT
        or any(
            name.startswith(prefix)
            for prefix in PYTHON_CONFIGURATION_ENV_PREFIXES
        )
    )


def effective_interpreter_identity(
    environ: Mapping[str, str] | None = None,
) -> dict[str, Any]:
    """Bind the Python authority that computes hashes and verdicts."""

    source_environment = os.environ if environ is None else environ
    stdlib_prefix = Path(sysconfig.get_path("stdlib")).resolve()
    return {
        "executable": str(Path(sys.executable).resolve()),
        "version": platform.python_version(),
        "stdlib_prefix": str(stdlib_prefix),
        "base_prefix": str(Path(sys.base_prefix).resolve()),
        "exec_prefix": str(Path(sys.exec_prefix).resolve()),
        "flags": {
            "isolated": bool(sys.flags.isolated),
            "ignore_environment": bool(sys.flags.ignore_environment),
            "no_site": bool(sys.flags.no_site),
            "no_user_site": bool(sys.flags.no_user_site),
            "safe_path": bool(sys.flags.safe_path),
        },
        "overridden_env": overridden_python_environment(source_environment),
    }


def prepare_sealed_interpreter(
    environ: Mapping[str, str],
) -> dict[str, Any]:
    """Prove the interpreter authority before any supervised target starts.

    ``-I -S`` is structural authority, not an environment sanitizer. Python
    configuration variables remain visible so their attempted use can be
    rejected and recorded by name without retaining their values.
    """

    facts = effective_interpreter_identity(environ)
    expected_flags = {
        "isolated": True,
        "ignore_environment": True,
        "no_site": True,
        "no_user_site": True,
        "safe_path": True,
    }
    if facts["flags"] != expected_flags:
        raise SealedInterpreterRejection(
            "sealed_interpreter_unsealed_startup",
            "evidence interpreter requires isolated no-site startup",
            facts,
        )
    if facts["overridden_env"]:
        raise SealedInterpreterRejection(
            "sealed_interpreter_hostile_environment",
            "hostile Python configuration channels present: "
            + ",".join(facts["overridden_env"]),
            facts,
        )
    return facts


def canonical_json(value: Any) -> bytes:
    return (
        json.dumps(
            value,
            allow_nan=False,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )
        + "\n"
    ).encode("utf-8")


def reject_json_constant(value: str) -> None:
    raise EvidenceError(f"non-finite JSON number is forbidden: {value}")


def unique_json_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, item in pairs:
        if key in value:
            raise EvidenceError(f"duplicate JSON key: {key}")
        value[key] = item
    return value


def parse_json(data: bytes | str, *, subject: str) -> Any:
    try:
        return json.loads(
            data,
            object_pairs_hook=unique_json_object,
            parse_constant=reject_json_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise EvidenceError(f"malformed JSON in {subject}: {error}") from error


def lexical_absolute(path: Path) -> Path:
    """Return an absolute lexical path without following a symlink component."""
    return Path(os.path.abspath(os.fspath(path)))


def require_within(path: Path, root: Path, *, label: str) -> Path:
    absolute = lexical_absolute(path)
    root_absolute = lexical_absolute(root)
    try:
        absolute.relative_to(root_absolute)
    except ValueError as error:
        raise EvidenceError(f"{label} escapes artifact root: {absolute}") from error
    return absolute


def require_exact_artifact_path(
    path: Path, art_dir: Path, filename: str, *, label: str
) -> Path:
    """Bind a canonical bundle control file to the artifact-directory root."""
    root = lexical_absolute(art_dir)
    absolute = require_within(path, root, label=label)
    expected = root / filename
    if absolute != expected:
        raise EvidenceError(f"{label} must be exactly {expected}")
    return absolute


def open_directory_nofollow(path: Path, *, create: bool) -> tuple[Path, int]:
    """Open a directory through no-follow dirfds, optionally creating components."""
    absolute = lexical_absolute(path)
    if os.name != "posix" or not hasattr(os, "O_NOFOLLOW"):
        raise EvidenceError("evidence publication requires POSIX O_NOFOLLOW support")
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC
    descriptor = os.open(absolute.anchor, flags)
    try:
        for component in absolute.parts[1:]:
            try:
                child = os.open(component, flags, dir_fd=descriptor)
            except FileNotFoundError:
                if not create:
                    raise
                try:
                    os.mkdir(component, 0o755, dir_fd=descriptor)
                except FileExistsError:
                    # A racing creator is accepted only if the no-follow open below
                    # proves that it created a real directory, not a symlink.
                    pass
                child = os.open(component, flags, dir_fd=descriptor)
            os.close(descriptor)
            descriptor = child
        return absolute, descriptor
    except BaseException:
        os.close(descriptor)
        raise


def open_regular_nofollow(path: Path) -> tuple[Path, int]:
    absolute = lexical_absolute(path)
    _parent, parent_fd = open_directory_nofollow(absolute.parent, create=False)
    try:
        descriptor = os.open(
            absolute.name,
            os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC,
            dir_fd=parent_fd,
        )
    finally:
        os.close(parent_fd)
    facts = os.fstat(descriptor)
    if not stat.S_ISREG(facts.st_mode):
        os.close(descriptor)
        raise EvidenceError(f"evidence path is not a regular file: {absolute}")
    return absolute, descriptor


_TEST_MUTATE_DURING_READ: Path | None = None


def stable_file_facts(
    path: Path, *, max_bytes: int | None = None
) -> tuple[bytes, int, str]:
    """Read one immutable snapshot and reject concurrent mutation."""
    global _TEST_MUTATE_DURING_READ
    absolute, descriptor = open_regular_nofollow(path)
    try:
        before = os.fstat(descriptor)
        if max_bytes is not None and before.st_size > max_bytes:
            raise EvidenceError(f"file exceeds {max_bytes} bytes: {absolute}")
        chunks: list[bytes] = []
        digest = hashlib.sha256()
        total = 0
        while True:
            block = os.read(descriptor, 1_048_576)
            if not block:
                break
            total += len(block)
            if max_bytes is not None and total > max_bytes:
                raise EvidenceError(f"file exceeds {max_bytes} bytes: {absolute}")
            digest.update(block)
            chunks.append(block)
        if (
            _TEST_MUTATE_DURING_READ is not None
            and absolute == _TEST_MUTATE_DURING_READ
        ):
            # Planted REAL mutation for the mutation-during-initial-hashing
            # scenario (bead fln-evidence-runner-bootstrap-btk): one byte is
            # appended through an independent descriptor while this snapshot
            # is still open, so the ordinary stability law below must fire on
            # genuinely changed kernel metadata — nothing here is simulated.
            _TEST_MUTATE_DURING_READ = None
            with open(absolute, "ab") as mutator:
                mutator.write(b"\n")
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    stable_fields = ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns")
    if any(getattr(before, field) != getattr(after, field) for field in stable_fields):
        raise EvidenceError(f"file changed while being read: {absolute}")
    if total != before.st_size:
        raise EvidenceError(f"file size changed while being read: {absolute}")
    return b"".join(chunks), total, digest.hexdigest()


def stable_symlink_facts(path: Path) -> tuple[bytes, int, str]:
    absolute = lexical_absolute(path)
    before = absolute.lstat()
    if not stat.S_ISLNK(before.st_mode):
        raise EvidenceError(f"canonical link changed type: {absolute}")
    target = os.fsencode(os.readlink(absolute))
    after = absolute.lstat()
    stable_fields = ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns")
    if any(getattr(before, field) != getattr(after, field) for field in stable_fields):
        raise EvidenceError(f"symlink changed while being read: {absolute}")
    return target, len(target), hashlib.sha256(target).hexdigest()


def write_new(path: Path, data: bytes, mode: int = 0o644) -> None:
    """Claim an absent path with O_EXCL and durably write it exactly once.

    A failed write deliberately leaves an invalid/incomplete final path.  It is never
    renamed over another producer's file and is rejected by bundle validation.
    """
    absolute = lexical_absolute(path)
    _parent, parent_fd = open_directory_nofollow(absolute.parent, create=True)
    try:
        descriptor = os.open(
            absolute.name,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC,
            mode,
            dir_fd=parent_fd,
        )
    except BaseException:
        os.close(parent_fd)
        raise
    try:
        view = memoryview(data)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                raise EvidenceError(f"short write while publishing {absolute}")
            view = view[written:]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
        os.fsync(parent_fd)
        os.close(parent_fd)


def prepare_atomic_file(parent_fd: int, data: bytes, mode: int = 0o644) -> int:
    if not hasattr(os, "O_TMPFILE"):
        raise EvidenceError("atomic evidence publication requires Linux O_TMPFILE")
    descriptor = os.open(
        ".",
        os.O_WRONLY | os.O_TMPFILE | os.O_CLOEXEC,
        mode,
        dir_fd=parent_fd,
    )
    try:
        view = memoryview(data)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                raise EvidenceError("short write while preparing atomic evidence")
            view = view[written:]
        os.fsync(descriptor)
        return descriptor
    except BaseException:
        os.close(descriptor)
        raise


def link_prepared_atomic_file(
    parent_fd: int,
    descriptor: int,
    name: str,
    *,
    test_fail_after_link: bool = False,
) -> bool:
    try:
        os.link(
            f"/proc/self/fd/{descriptor}",
            name,
            dst_dir_fd=parent_fd,
            follow_symlinks=True,
        )
    except FileExistsError:
        return False
    if test_fail_after_link:
        raise EvidenceError("injected failure after atomic link")
    os.fsync(parent_fd)
    return True


def write_atomic_new(path: Path, data: bytes, mode: int = 0o644) -> None:
    """Publish complete bytes at an absent final name in one atomic link step."""
    absolute = lexical_absolute(path)
    _parent, parent_fd = open_directory_nofollow(absolute.parent, create=True)
    descriptor: int | None = None
    try:
        descriptor = prepare_atomic_file(parent_fd, data, mode)
        if not link_prepared_atomic_file(parent_fd, descriptor, absolute.name):
            raise FileExistsError(absolute)
    finally:
        if descriptor is not None:
            os.close(descriptor)
        os.close(parent_fd)


def write_signal_committed_atomic_new(
    path: Path,
    data: bytes,
    mode: int = 0o644,
    *,
    decision_path: Path | None = None,
    restore_signal_state: bool = True,
    test_fail_after_link: bool = False,
    test_marker_pause: tuple[Path, Path] | None = None,
) -> None:
    """Race cancellation and commit on one write-once cross-process decision."""
    absolute = lexical_absolute(path)
    decision_absolute = (
        lexical_absolute(decision_path) if decision_path is not None else None
    )
    if (
        decision_absolute is not None
        and decision_absolute.parent != absolute.parent
    ):
        raise EvidenceError("commit decision and final marker must share a directory")
    _parent, parent_fd = open_directory_nofollow(absolute.parent, create=True)
    descriptor: int | None = None
    watched = (signal.SIGHUP, signal.SIGINT, signal.SIGTERM)
    old_handlers = {signum: signal.getsignal(signum) for signum in watched}
    previous_mask: set[signal.Signals] | None = None
    try:
        descriptor = prepare_atomic_file(parent_fd, data, mode)
        previous_mask = signal.pthread_sigmask(signal.SIG_BLOCK, watched)
        if any(signum in signal.sigpending() for signum in watched):
            for signum in watched:
                signal.signal(signum, signal.SIG_IGN)
            signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)
            previous_mask = None
            raise EvidenceError("signal arrived before atomic evidence commit")
        # The pending-signal sample is the commit point. Later watched signals are
        # blocked locally, while the shared decision path also arbitrates signals
        # already observed by the parent shell.
        for signum in watched:
            signal.signal(signum, signal.SIG_IGN)
        if decision_absolute is None:
            if not link_prepared_atomic_file(
                parent_fd,
                descriptor,
                absolute.name,
                test_fail_after_link=test_fail_after_link,
            ):
                raise FileExistsError(absolute)
        else:
            decision_won = link_prepared_atomic_file(
                parent_fd,
                descriptor,
                decision_absolute.name,
                test_fail_after_link=test_fail_after_link,
            )
            if not decision_won:
                decision_data, _size, _digest = stable_file_facts(decision_absolute)
                if not hmac.compare_digest(decision_data, data):
                    raise EvidenceError("cancellation won the bundle decision race")
            if test_marker_pause is not None:
                # Boundary-injection hook (bead fln-evidence-runner-bootstrap-btk):
                # hold the window between the linked decision and the canonical
                # marker open so a deterministic signal can be delivered to the
                # supervising shell. Watched signals are already ignored here, so
                # the pause cannot be interrupted; the decision has already won,
                # so the signal must lose and the bundle must still commit.
                pause_ready, pause_release = test_marker_pause
                write_new(lexical_absolute(pause_ready), b"0 0\n")
                pause_deadline = time.monotonic() + 180.0
                while True:
                    try:
                        release_data, _release_size, _release_digest = (
                            stable_file_facts(
                                lexical_absolute(pause_release), max_bytes=64
                            )
                        )
                    except (EvidenceError, FileNotFoundError):
                        release_data = b""
                    if release_data:
                        break
                    if time.monotonic() >= pause_deadline:
                        raise EvidenceError(
                            "marker-link pause release timed out"
                        )
                    time.sleep(0.005)
            try:
                os.link(
                    decision_absolute.name,
                    absolute.name,
                    src_dir_fd=parent_fd,
                    dst_dir_fd=parent_fd,
                    follow_symlinks=False,
                )
            except FileExistsError:
                marker_data, _size, _digest = stable_file_facts(absolute)
                if not hmac.compare_digest(marker_data, data):
                    raise EvidenceError("bundle marker disagrees with commit decision")
            os.fsync(parent_fd)
    finally:
        if previous_mask is not None:
            signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)
        if restore_signal_state:
            for signum, handler in old_handlers.items():
                signal.signal(signum, handler)
        if descriptor is not None:
            os.close(descriptor)
        os.close(parent_fd)


def append_record(
    path: Path, record: dict[str, Any], *, must_be_new: bool = False
) -> None:
    """Append and fsync one canonically encoded NDJSON record."""
    data = canonical_json(record)
    if len(data) > MAX_RECORD_BYTES:
        raise EvidenceError(f"record exceeds {MAX_RECORD_BYTES} bytes")
    absolute = lexical_absolute(path)
    _parent, parent_fd = open_directory_nofollow(absolute.parent, create=True)
    flags = os.O_WRONLY | os.O_APPEND | os.O_CREAT | os.O_NOFOLLOW | os.O_CLOEXEC
    if must_be_new:
        flags |= os.O_EXCL
    try:
        descriptor = os.open(absolute.name, flags, 0o644, dir_fd=parent_fd)
    except BaseException:
        os.close(parent_fd)
        raise
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise EvidenceError(f"NDJSON path is not a regular file: {absolute}")
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        written = os.write(descriptor, data)
        if written != len(data):
            raise EvidenceError(f"short append while writing {absolute}")
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
        os.fsync(parent_fd)
        os.close(parent_fd)


def redact_arg(arg: str) -> tuple[str, bool]:
    if "=" in arg:
        key, _value = arg.split("=", 1)
        if SECRET_KEY.search(key):
            return f"{key}=<redacted>", True
    if SECRET_KEY.search(arg) and (":" in arg or " " in arg or len(arg) > 80):
        return "<redacted>", True
    return arg, False


def redacted_argv(argv: Sequence[str]) -> tuple[list[str], bool]:
    result: list[str] = []
    redacted = False
    redact_next = False
    for arg in argv:
        if redact_next:
            result.append("<redacted>")
            redacted = True
            redact_next = False
            continue
        rendered, changed = redact_arg(arg)
        result.append(rendered)
        redacted = redacted or changed
        if arg.startswith("-") and SECRET_KEY.search(arg) and "=" not in arg:
            redact_next = True
    return result, redacted


class BoundedCapture:
    def __init__(self, limit: int) -> None:
        if limit < 256:
            raise EvidenceError("capture limit must be at least 256 bytes")
        self.limit = limit
        self.total = 0
        self.digest = hashlib.sha256()
        self._small: bytearray | None = bytearray()
        self._head = bytearray()
        self._tail = bytearray()
        self._head_limit = limit // 2
        self._tail_limit = limit - self._head_limit
        self._lock = threading.Lock()

    def feed(self, data: bytes) -> None:
        with self._lock:
            self.total += len(data)
            self.digest.update(data)
            if self._small is not None:
                if len(self._small) + len(data) <= self.limit:
                    self._small.extend(data)
                    return
                combined = bytes(self._small) + data
                self._head.extend(combined[: self._head_limit])
                self._tail.extend(combined[-self._tail_limit :])
                self._small = None
                return
            if len(self._head) < self._head_limit:
                need = self._head_limit - len(self._head)
                self._head.extend(data[:need])
                data = data[need:]
            if data:
                combined_tail = bytes(self._tail) + data
                self._tail = bytearray(combined_tail[-self._tail_limit :])

    @property
    def truncated(self) -> bool:
        return self._small is None

    def render(self) -> tuple[bytes, int, int]:
        with self._lock:
            if self._small is not None:
                data = bytes(self._small)
                return data, len(data), 0
            omitted = max(0, self.total - len(self._head) - len(self._tail))
            marker = f"\n...[{omitted} bytes omitted; {self.total} total]...\n".encode()
            available = max(0, self.limit - len(marker))
            head_len = min(len(self._head), available // 2)
            tail_len = min(len(self._tail), available - head_len)
            data = bytes(self._head[:head_len]) + marker + bytes(self._tail[-tail_len:])
            if len(data) > self.limit:
                raise EvidenceError("internal capture bound violation")
            return data, head_len, tail_len

    def facts(
        self, artifact: str, retained: int, head: int, tail: int
    ) -> dict[str, Any]:
        return {
            "artifact": artifact,
            "sha256": self.digest.hexdigest(),
            "retained_sha256": None,
            "total_bytes": self.total,
            "retained_bytes": retained,
            "head_bytes": head,
            "tail_bytes": tail,
            "truncated": self.truncated or retained != self.total,
        }


def drain(pipe: Any, capture: BoundedCapture, errors: list[str], label: str) -> None:
    try:
        while True:
            block = pipe.read(65_536)
            if not block:
                break
            capture.feed(block)
    except BaseException as error:  # thread failure must become typed harness failure
        errors.append(f"{label} drain failed: {error}")
    finally:
        try:
            pipe.close()
        except OSError as error:
            errors.append(f"{label} close failed: {error}")


class StoppedExecProcess:
    """Minimal Popen-compatible handle for a target forked inert before exec."""

    def __init__(self, pid: int, stdout_descriptor: int, stderr_descriptor: int):
        self.pid = pid
        try:
            self.stdout = os.fdopen(stdout_descriptor, "rb", buffering=0)
        except BaseException:
            os.close(stdout_descriptor)
            os.close(stderr_descriptor)
            raise
        try:
            self.stderr = os.fdopen(stderr_descriptor, "rb", buffering=0)
        except BaseException:
            self.stdout.close()
            os.close(stderr_descriptor)
            raise
        self.returncode: int | None = None

    def poll(self) -> int | None:
        if self.returncode is not None:
            return self.returncode
        try:
            waited_pid, status = os.waitpid(self.pid, os.WNOHANG)
        except InterruptedError:
            return None
        if waited_pid == 0:
            return None
        if waited_pid != self.pid:
            raise EvidenceError("reaped an unexpected stopped-exec child")
        self.returncode = os.waitstatus_to_exitcode(status)
        return self.returncode

    def wait(self, timeout: float | None = None) -> int:
        if self.returncode is not None:
            return self.returncode
        deadline = time.monotonic() + timeout if timeout is not None else None
        while True:
            try:
                if deadline is None:
                    waited_pid, status = os.waitpid(self.pid, 0)
                else:
                    waited_pid, status = os.waitpid(self.pid, os.WNOHANG)
            except InterruptedError:
                continue
            if waited_pid == self.pid:
                self.returncode = os.waitstatus_to_exitcode(status)
                return self.returncode
            if waited_pid != 0:
                raise EvidenceError("reaped an unexpected stopped-exec child")
            if deadline is not None and time.monotonic() >= deadline:
                raise subprocess.TimeoutExpired(self.pid, timeout)
            time.sleep(0.005)

    def kill(self) -> None:
        if self.poll() is not None:
            return
        try:
            os.kill(self.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass


def spawn_stopped_exec(
    argv: Sequence[str],
    cwd: Path,
    expected_parent_pid: int,
    *,
    target_signal_mask: set[signal.Signals],
    test_before_stop_delay_ms: int = 0,
    test_gate_mode: str = "normal",
    env: dict[str, str] | None = None,
) -> tuple[StoppedExecProcess, int, int, int]:
    """Fork an inert future target with no intervening interpreter or user exec."""
    try:
        task_ids = {
            int(entry.name)
            for entry in Path("/proc/self/task").iterdir()
            if entry.name.isdecimal()
        }
    except OSError as error:
        raise EvidenceError("cannot prove stopped-target fork thread state") from error
    if threading.active_count() != 1 or task_ids != {os.getpid()}:
        raise EvidenceError("stopped target fork requires a single-threaded supervisor")
    opened_descriptors: list[int] = []
    try:
        stdout_read, stdout_write = os.pipe2(os.O_CLOEXEC)
        opened_descriptors.extend((stdout_read, stdout_write))
        stderr_read, stderr_write = os.pipe2(os.O_CLOEXEC)
        opened_descriptors.extend((stderr_read, stderr_write))
        exec_read, exec_write = os.pipe2(os.O_CLOEXEC)
        opened_descriptors.extend((exec_read, exec_write))
        gate_ready_read, gate_ready_write = os.pipe2(os.O_CLOEXEC)
        opened_descriptors.extend((gate_ready_read, gate_ready_write))
        gate_release_read, gate_release_write = os.pipe2(os.O_CLOEXEC)
        opened_descriptors.extend((gate_release_read, gate_release_write))
        null_descriptor = os.open(os.devnull, os.O_RDONLY | os.O_CLOEXEC)
        opened_descriptors.append(null_descriptor)
    except BaseException:
        for descriptor in opened_descriptors:
            os.close(descriptor)
        raise
    try:
        child_pid = os.fork()
    except BaseException:
        for descriptor in opened_descriptors:
            os.close(descriptor)
        raise
    if child_pid == 0:
        try:
            default_signals = {
                signal.SIGHUP,
                signal.SIGINT,
                signal.SIGTERM,
                signal.SIGPIPE,
            }
            for signal_name in ("SIGXFZ", "SIGXFSZ"):
                candidate = getattr(signal, signal_name, None)
                if candidate is not None:
                    default_signals.add(candidate)
            for signum in default_signals:
                signal.signal(signum, signal.SIG_DFL)
            os.dup2(null_descriptor, 0, inheritable=True)
            os.dup2(stdout_write, 1, inheritable=True)
            os.dup2(stderr_write, 2, inheritable=True)
            os.dup2(exec_write, 3, inheritable=False)
            retained_descriptors = {gate_ready_write, gate_release_read}
            for raw_descriptor in os.listdir("/proc/self/fd"):
                descriptor = int(raw_descriptor)
                if descriptor > 3 and descriptor not in retained_descriptors:
                    try:
                        os.close(descriptor)
                    except OSError as error:
                        if error.errno != errno.EBADF:
                            raise
            os.setsid()
            arm_parent_death_kill(expected_parent_pid)
            os.chdir(cwd)
            if test_before_stop_delay_ms:
                time.sleep(test_before_stop_delay_ms / 1000)
            if test_gate_mode == "exit_before_stop":
                os._exit(SETUP_FAILURE)
            ready_view = memoryview(STOPPED_GATE_READY_TOKEN)
            while ready_view:
                written = os.write(gate_ready_write, ready_view)
                if written <= 0:
                    raise EvidenceError("private gate readiness made no progress")
                ready_view = ready_view[written:]
            os.close(gate_ready_write)
            if test_gate_mode == "never_stop":
                while True:
                    time.sleep(60)
            os.kill(os.getpid(), signal.SIGSTOP)
        except BaseException:
            os._exit(SETUP_FAILURE)
        if test_gate_mode == "die_after_stop":
            os.kill(os.getpid(), signal.SIGKILL)
        try:
            release = bytearray()
            while len(release) <= len(STOPPED_GATE_RELEASE_TOKEN):
                block = os.read(
                    gate_release_read,
                    len(STOPPED_GATE_RELEASE_TOKEN) + 1 - len(release),
                )
                if not block:
                    break
                release.extend(block)
            os.close(gate_release_read)
            if not hmac.compare_digest(bytes(release), STOPPED_GATE_RELEASE_TOKEN):
                raise EvidenceError("private stopped-target release token mismatch")
            signal.pthread_sigmask(signal.SIG_SETMASK, target_signal_mask)
            if env is not None:
                os.execvpe(argv[0], list(argv), env)
            else:
                os.execvp(argv[0], list(argv))
            raise EvidenceError("stopped target exec unexpectedly returned")
        except BaseException as error:
            try:
                write_exec_failure_status(3, error)
            except BaseException:
                pass
            try:
                os.close(3)
            except OSError:
                pass
            os._exit(SETUP_FAILURE)
    try:
        for descriptor in (
            stdout_write,
            stderr_write,
            exec_write,
            gate_ready_write,
            gate_release_read,
            null_descriptor,
        ):
            os.close(descriptor)
        process = StoppedExecProcess(child_pid, stdout_read, stderr_read)
    except BaseException as construction_error:
        for descriptor in (
            stdout_read,
            stderr_read,
            exec_read,
            gate_ready_read,
            gate_release_write,
            stdout_write,
            stderr_write,
            exec_write,
            gate_ready_write,
            gate_release_read,
            null_descriptor,
        ):
            try:
                os.close(descriptor)
            except OSError:
                pass
        try:
            os.kill(child_pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        cleanup_deadline = time.monotonic() + 2.0
        while time.monotonic() < cleanup_deadline:
            try:
                waited_pid, _status = os.waitpid(child_pid, os.WNOHANG)
            except InterruptedError:
                continue
            except ChildProcessError:
                raise construction_error
            if waited_pid == child_pid:
                raise construction_error
            time.sleep(0.005)
        raise EvidenceError(
            "stopped-target construction failed and child did not reap in time"
        ) from construction_error
    return process, exec_read, gate_ready_read, gate_release_write


def write_exec_failure_status(descriptor: int, error: BaseException) -> None:
    """Report a pre-target exec failure without placing raw argv in evidence."""
    error_number = error.errno if isinstance(error, OSError) else None
    payload = canonical_json(
        {
            "schema": "fln.exec-status/1",
            "status": "failed",
            "error_type": type(error).__name__,
            "errno": error_number,
            "errno_name": errno.errorcode.get(error_number) if error_number else None,
        }
    )
    if len(payload) > MAX_EXEC_STATUS_BYTES:
        raise EvidenceError("exec failure status exceeded its fixed protocol bound")
    offset = 0
    while offset < len(payload):
        try:
            written = os.write(descriptor, payload[offset:])
        except InterruptedError:
            continue
        if written <= 0:
            raise EvidenceError("exec failure status pipe made no progress")
        offset += written


def process_alive(pid: int) -> bool:
    facts = proc_stat_facts(pid)
    return facts is not None and facts[0] != "Z"


def proc_stat_facts(pid: int) -> tuple[str, int, int] | None:
    """Return Linux process state, process group, and start ticks."""
    try:
        data = Path(f"/proc/{pid}/stat").read_text(encoding="ascii")
    except OSError as error:
        if error.errno in {errno.ENOENT, errno.ESRCH}:
            return None
        raise EvidenceError(f"cannot inspect process {pid}: {error}") from error
    except UnicodeError as error:
        raise EvidenceError(f"cannot inspect process {pid}: {error}") from error
    close = data.rfind(")")
    if close < 0:
        raise EvidenceError(f"malformed Linux stat record for process {pid}")
    fields = data[close + 2 :].split()
    if len(fields) < 20:
        raise EvidenceError(f"short Linux stat record for process {pid}")
    try:
        return fields[0], int(fields[2]), int(fields[19])
    except ValueError as error:
        raise EvidenceError(f"malformed Linux stat facts for process {pid}") from error


def child_subreaper_enabled() -> bool:
    """Return this process's Linux child-subreaper state."""
    if sys.platform != "linux":
        raise EvidenceError("process-tree supervision currently requires Linux")
    libc = ctypes.CDLL(None, use_errno=True)
    current = ctypes.c_int()
    # Linux prctl(PR_GET_CHILD_SUBREAPER, &current).
    if libc.prctl(37, ctypes.byref(current), 0, 0, 0) != 0:
        error_number = ctypes.get_errno()
        raise EvidenceError(
            f"cannot inspect child subreaper state: errno {error_number}"
        )
    return current.value != 0


def set_child_subreaper(enabled: bool) -> None:
    """Set this process's Linux child-subreaper state."""
    if sys.platform != "linux":
        raise EvidenceError("process-tree supervision currently requires Linux")
    libc = ctypes.CDLL(None, use_errno=True)
    # Linux prctl(PR_SET_CHILD_SUBREAPER, enabled).
    if libc.prctl(36, int(enabled), 0, 0, 0) != 0:
        error_number = ctypes.get_errno()
        raise EvidenceError(f"cannot set child subreaper state: errno {error_number}")


def enable_child_subreaper() -> None:
    """Make orphaned grandchildren observable and reapable by this supervisor."""
    if not child_subreaper_enabled():
        set_child_subreaper(True)


def arm_parent_death_signal(expected_parent_pid: int, signum: int) -> None:
    """Deliver a fixed signal if this process's exact launching parent exits."""
    if sys.platform != "linux":
        raise EvidenceError("parent-death containment currently requires Linux")
    if expected_parent_pid <= 1 or expected_parent_pid == os.getpid():
        raise EvidenceError("parent-death identity is malformed")
    if signum <= 0 or signum >= signal.NSIG:
        raise EvidenceError("parent-death signal is malformed")
    if os.getppid() != expected_parent_pid:
        raise EvidenceError("launcher parent changed before parent-death binding")
    libc = ctypes.CDLL(None, use_errno=True)
    # Linux prctl(PR_SET_PDEATHSIG, signum). The second parent check closes the
    # race where the parent exits after the first check but before prctl.
    if libc.prctl(1, signum, 0, 0, 0) != 0:
        error_number = ctypes.get_errno()
        raise EvidenceError(
            f"cannot arm launcher parent-death signal: errno {error_number}"
        )
    if os.getppid() != expected_parent_pid:
        os.kill(os.getpid(), signum)
        raise EvidenceError("launcher parent changed during parent-death binding")


def arm_parent_death_kill(expected_parent_pid: int) -> None:
    """Kill this process if its exact launching parent exits."""
    arm_parent_death_signal(expected_parent_pid, signal.SIGKILL)


def proc_children(pid: int) -> set[int]:
    task_root = Path(f"/proc/{pid}/task")
    try:
        task_paths = list(task_root.iterdir())
    except OSError as error:
        if error.errno in {errno.ENOENT, errno.ESRCH}:
            return set()
        raise EvidenceError(f"cannot inspect descendants of {pid}: {error}") from error
    children: set[int] = set()
    for task_path in task_paths:
        try:
            raw = (task_path / "children").read_text(encoding="ascii").strip()
        except OSError as error:
            if error.errno in {errno.ENOENT, errno.ESRCH}:
                continue
            raise EvidenceError(
                f"cannot inspect task descendants of {pid}: {error}"
            ) from error
        except UnicodeError as error:
            raise EvidenceError(
                f"cannot inspect task descendants of {pid}: {error}"
            ) from error
        if not raw:
            continue
        try:
            children.update(int(value) for value in raw.split())
        except ValueError as error:
            raise EvidenceError(f"malformed Linux children list for {pid}") from error
    return children


def descendant_closure(roots: Iterable[int]) -> set[int]:
    pending = list(roots)
    found: set[int] = set()
    while pending:
        parent = pending.pop()
        for child in proc_children(parent):
            if child not in found:
                found.add(child)
                pending.append(child)
    return found


def live_process_group_members(pgid: int) -> set[int]:
    members: set[int] = set()
    for entry in Path("/proc").iterdir():
        if not entry.name.isdecimal():
            continue
        pid = int(entry.name)
        facts = proc_stat_facts(pid)
        if facts is not None and facts[0] != "Z" and facts[1] == pgid:
            members.add(pid)
    return members


ProcessHandles = dict[int, tuple[int, int]]


def open_process_handle(
    pid: int, *, expected_parent_pid: int | None = None
) -> tuple[int, int] | None:
    """Bind a Linux PID to its lifetime before it can be signalled."""
    if not hasattr(os, "pidfd_open") or not hasattr(signal, "pidfd_send_signal"):
        raise EvidenceError("process supervision requires Linux pidfd support")
    if expected_parent_pid is not None and pid not in proc_children(
        expected_parent_pid
    ):
        return None
    facts = proc_stat_facts(pid)
    if facts is None or facts[0] == "Z":
        return None
    try:
        descriptor = os.pidfd_open(pid, 0)
    except ProcessLookupError:
        return None
    repeated = proc_stat_facts(pid)
    if (
        repeated is None
        or repeated[0] == "Z"
        or repeated[2] != facts[2]
        or (
            expected_parent_pid is not None
            and pid not in proc_children(expected_parent_pid)
        )
    ):
        os.close(descriptor)
        return None
    return facts[2], descriptor


def bind_direct_child_until(
    pid: int,
    expected_parent_pid: int,
    deadline: float,
    *,
    open_handle: Callable[[], tuple[int, int] | None] | None = None,
    cancelled: Callable[[], bool] | None = None,
) -> tuple[int, int]:
    """Retry a lifetime bind while the same live direct child is still unreaped."""
    if open_handle is None:
        open_handle = partial(
            open_process_handle, pid, expected_parent_pid=expected_parent_pid
        )
    initial_facts = proc_stat_facts(pid)
    if (
        initial_facts is None
        or initial_facts[0] == "Z"
        or pid not in proc_children(expected_parent_pid)
    ):
        raise EvidenceError("process disappeared before identity binding")
    initial_start_ticks = initial_facts[2]
    while True:
        if cancelled is not None and cancelled():
            raise SetupCancelledError("cancelled before process identity binding")
        handle = open_handle()
        if handle is not None:
            if handle[0] != initial_start_ticks:
                os.close(handle[1])
                raise EvidenceError("process identity changed before binding")
            return handle
        facts = proc_stat_facts(pid)
        if (
            facts is None
            or facts[0] == "Z"
            or facts[2] != initial_start_ticks
            or pid not in proc_children(expected_parent_pid)
        ):
            raise EvidenceError("process identity changed before binding")
        if time.monotonic() >= deadline:
            raise EvidenceError("process identity did not stabilize in time")
        time.sleep(0.005)


def admit_stopped_session_leader_until(
    pid: int,
    expected_parent_pid: int,
    deadline: float,
    *,
    gate_ready_descriptor: int,
    cancelled: Callable[[], bool] | None = None,
) -> tuple[int, int]:
    """Bind one direct child and prove its private setup gate plus stopped state."""
    try:
        handle = bind_direct_child_until(
            pid,
            expected_parent_pid,
            deadline,
            cancelled=cancelled,
        )
    except EvidenceError as error:
        if (
            not isinstance(error, SetupCancelledError)
            and time.monotonic() >= deadline
            and str(error) == "process identity did not stabilize in time"
        ):
            raise SetupTimeoutError(
                "child identity did not stabilize within setup budget"
            ) from error
        raise
    try:
        gate_ready = bytearray()
        gate_ready_eof = False
        while True:
            if cancelled is not None and cancelled():
                raise SetupCancelledError("cancelled before stopped-child admission")
            while not gate_ready_eof:
                try:
                    block = os.read(
                        gate_ready_descriptor,
                        len(STOPPED_GATE_READY_TOKEN) + 1 - len(gate_ready),
                    )
                except BlockingIOError:
                    break
                except InterruptedError:
                    continue
                if not block:
                    gate_ready_eof = True
                    break
                gate_ready.extend(block)
                if len(gate_ready) > len(STOPPED_GATE_READY_TOKEN):
                    raise EvidenceError("private gate readiness token exceeded bound")
            if gate_ready_eof and not hmac.compare_digest(
                bytes(gate_ready), STOPPED_GATE_READY_TOKEN
            ):
                raise EvidenceError("private gate readiness token mismatch")
            facts = proc_stat_facts(pid)
            if (
                facts is None
                or facts[0] == "Z"
                or facts[2] != handle[0]
                or pid not in proc_children(expected_parent_pid)
            ):
                raise EvidenceError("stopped child changed before admission")
            try:
                session_id = os.getsid(pid)
            except ProcessLookupError as error:
                raise EvidenceError(
                    "stopped child disappeared before session admission"
                ) from error
            if (
                gate_ready_eof
                and facts[0] == "t"
            ):
                raise EvidenceError("ptrace stop cannot satisfy stopped-target admission")
            if (
                gate_ready_eof
                and facts[0] == "T"
                and facts[1] == pid
                and session_id == pid
                and time.monotonic() < deadline
            ):
                return handle
            if time.monotonic() >= deadline:
                raise SetupTimeoutError(
                    "child did not reach stopped session-leader admission in time"
                )
            time.sleep(0.005)
    except BaseException:
        os.close(handle[1])
        raise


def close_process_handles(handles: ProcessHandles) -> None:
    for _start_ticks, descriptor in handles.values():
        os.close(descriptor)
    handles.clear()


def process_handle_alive(pid: int, handle: tuple[int, int]) -> bool:
    facts = proc_stat_facts(pid)
    return facts is not None and facts[0] != "Z" and facts[2] == handle[0]


def remember_process(
    pid: int, handles: ProcessHandles, *, expected_parent_pid: int | None = None
) -> bool:
    current = handles.get(pid)
    if current is not None:
        if process_handle_alive(pid, current):
            return True
        os.close(current[1])
        del handles[pid]
    opened = open_process_handle(pid)
    if opened is None:
        return False
    if expected_parent_pid is not None and pid not in proc_children(expected_parent_pid):
        os.close(opened[1])
        return False
    handles[pid] = opened
    return True


def signal_process_handle(
    pid: int, handle: tuple[int, int], signum: int
) -> bool:
    if not process_handle_alive(pid, handle):
        return False
    try:
        signal.pidfd_send_signal(handle[1], signum, None, 0)
        return True
    except ProcessLookupError:
        return False


def live_tree_members(root_pid: int, known: ProcessHandles) -> set[int]:
    # While the leader lives, walk beneath it. Once an intermediate exits, Linux's
    # subreaper reparents its surviving descendants directly to this process.
    for pid, handle in list(known.items()):
        if not process_handle_alive(pid, handle):
            os.close(handle[1])
            del known[pid]
    roots: set[int] = set()
    if root_pid in known and process_handle_alive(root_pid, known[root_pid]):
        roots.add(root_pid)
    roots.update(proc_children(os.getpid()))
    pending = list(roots)
    visited: set[int] = set()
    while pending:
        pid = pending.pop()
        if pid == os.getpid() or pid in visited:
            continue
        if pid == root_pid and pid in known and process_handle_alive(pid, known[pid]):
            visited.add(pid)
            for child in proc_children(pid):
                if child not in visited:
                    pending.append(child)
            continue
        parent_pid = next(
            (
                candidate
                for candidate in ({root_pid, os.getpid()} | visited)
                if pid in proc_children(candidate)
            ),
            None,
        )
        if parent_pid is None or not remember_process(
            pid, known, expected_parent_pid=parent_pid
        ):
            continue
        visited.add(pid)
        for child in proc_children(pid):
            if child not in visited:
                pending.append(child)
    # Once a lifetime was admitted through a proven parent edge, keep it in scope
    # across subreaper/init reparenting until its pidfd-bound identity is dead.
    return {
        pid
        for pid, handle in known.items()
        if pid != os.getpid() and process_handle_alive(pid, handle)
    }


def reap_adopted_children(exclude_pid: int | None = None) -> None:
    for child_pid in proc_children(os.getpid()):
        if child_pid == exclude_pid:
            continue
        try:
            os.waitpid(child_pid, os.WNOHANG)
        except ChildProcessError:
            continue


def graceful_signal_targets(
    root_pid: int, live: set[int], *, root_only: bool
) -> list[int]:
    return sorted(({root_pid} & live) if root_only else live)


def terminate_tree(
    proc: Any,
    first_signal: int,
    grace_s: float,
    known: ProcessHandles,
    *,
    graceful_root_only: bool = False,
) -> tuple[bool, bool, list[int]]:
    term_sent = False
    kill_sent = False
    live = live_tree_members(proc.pid, known)
    graceful_targets = graceful_signal_targets(
        proc.pid, live, root_only=graceful_root_only
    )
    for pid in graceful_targets:
        term_sent = signal_process_handle(pid, known[pid], first_signal) or term_sent
    deadline = time.monotonic() + grace_s
    while time.monotonic() < deadline:
        proc.poll()
        reap_adopted_children(proc.pid)
        live = live_tree_members(proc.pid, known)
        if not live:
            break
        # The graceful signal is a one-shot snapshot operation. Re-sending it, or
        # signalling descendants created during cooperative cleanup, can interrupt
        # a child's cancellation finalizer after that child re-arms its handlers.
        # Dynamic discovery remains active for the forced-cleanup fixed point below.
        time.sleep(0.02)
    live = live_tree_members(proc.pid, known)
    if live:
        # Freeze the bound tree before forced termination. Once every discovered
        # process is stopped, no member can fork across the final descendant scan.
        freeze_deadline = time.monotonic() + max(0.25, grace_s)
        while time.monotonic() < freeze_deadline:
            for pid in live:
                signal_process_handle(pid, known[pid], signal.SIGSTOP)
            time.sleep(0.01)
            repeated = live_tree_members(proc.pid, known)
            all_stopped = all(
                (facts := proc_stat_facts(pid)) is not None
                and facts[0] in {"T", "t"}
                and facts[2] == known[pid][0]
                for pid in repeated
            )
            if repeated == live and all_stopped:
                live = repeated
                break
            live = repeated
        for pid in live:
            kill_sent = (
                signal_process_handle(pid, known[pid], signal.SIGKILL) or kill_sent
            )
        kill_deadline = time.monotonic() + max(0.25, grace_s)
        while time.monotonic() < kill_deadline:
            proc.poll()
            reap_adopted_children(proc.pid)
            live = live_tree_members(proc.pid, known)
            if not live:
                break
            for pid in live:
                signal_process_handle(pid, known[pid], signal.SIGKILL)
            time.sleep(0.02)
    survivors = sorted(live_tree_members(proc.pid, known))
    return term_sent, kill_sent, survivors


def _run_supervised_impl(
    *,
    argv: Sequence[str],
    cwd: Path,
    metadata_path: Path,
    stdout_path: Path,
    stderr_path: Path,
    readiness_path: Path,
    artifact_root: Path,
    capture_bytes: int,
    output_budget_bytes: int,
    timeout_ms: int,
    grace_ms: int,
    stage_id: str,
    planted: bool,
    setup_timeout_ms: int = MAX_PROCESS_IDENTITY_WAIT_MS,
    semantic_failure_exits: Sequence[int] = (),
    cancel_after_ms: int | None = None,
    restore_signal_state: bool = True,
    test_terminal_delay_ms: int = 0,
    test_terminal_ready_path: Path | None = None,
    guardian_identity: tuple[int, int] | None = None,
    initial_signal_mask: set[signal.Signals] | None = None,
    test_before_stop_delay_ms: int = 0,
    test_before_release_delay_ms: int = 0,
    test_gate_mode: str = "normal",
    test_fault_point: str = "none",
    sealed_cargo: bool = False,
    suite_lock_path: Path | None = None,
    sealed_build_root: Path | None = None,
) -> int:
    if not argv:
        raise EvidenceError("supervisor requires a non-empty argv")
    if sealed_cargo and (suite_lock_path is None or sealed_build_root is None):
        raise EvidenceError(
            "sealed-cargo supervision requires --suite-lock and --sealed-build-root"
        )
    for label, value in (
        ("capture-bytes", capture_bytes),
        ("output-budget-bytes", output_budget_bytes),
        ("setup-timeout-ms", setup_timeout_ms),
        ("timeout-ms", timeout_ms),
        ("grace-ms", grace_ms),
    ):
        if value <= 0:
            raise EvidenceError(f"{label} must be positive")
    if output_budget_bytes < capture_bytes:
        raise EvidenceError(
            "output budget must be at least the per-stream capture bound"
        )
    if test_terminal_delay_ms < 0:
        raise EvidenceError("test terminal delay must be non-negative")
    if cancel_after_ms is not None and cancel_after_ms < 0:
        raise EvidenceError("cancel-after-ms must be non-negative")
    if test_before_stop_delay_ms < 0:
        raise EvidenceError("test before-stop delay must be non-negative")
    if test_before_release_delay_ms < 0:
        raise EvidenceError("test before-release delay must be non-negative")
    if test_gate_mode not in {
        "normal",
        "exit_before_stop",
        "never_stop",
        "die_after_stop",
    }:
        raise EvidenceError("unknown stopped-gate test mode")
    if test_fault_point not in SUPERVISOR_TEST_FAULT_POINTS:
        raise EvidenceError("unknown supervisor fault point")
    if (
        test_before_stop_delay_ms != 0
        or test_before_release_delay_ms != 0
        or test_gate_mode != "normal"
        or test_terminal_delay_ms != 0
        or test_terminal_ready_path is not None
        or test_fault_point != "none"
    ) and not planted:
        raise EvidenceError("supervisor fault controls require --planted evidence")
    if initial_signal_mask is None:
        raise EvidenceError("supervisor requires an explicit target signal mask")
    if test_terminal_ready_path is not None:
        test_terminal_ready_path = require_within(
            test_terminal_ready_path,
            artifact_root,
            label="test terminal readiness",
        )
    semantic_exits = sorted(set(semantic_failure_exits))
    if any(
        not isinstance(value, int)
        or isinstance(value, bool)
        or value <= 0
        or value > 255
        for value in semantic_exits
    ):
        raise EvidenceError(
            "semantic failure exits must be unique integers from 1 through 255"
        )
    artifact_root = lexical_absolute(artifact_root)
    artifact_paths: list[Path] = []
    for label, path in (
        ("metadata", metadata_path),
        ("stdout", stdout_path),
        ("stderr", stderr_path),
        ("readiness", readiness_path),
    ):
        artifact_paths.append(require_within(path, artifact_root, label=label))
    if len({path.parent for path in artifact_paths}) != 1:
        raise EvidenceError("supervisor artifacts must share one directory")
    if len({path.name for path in artifact_paths}) != len(artifact_paths):
        raise EvidenceError("supervisor artifact paths must be distinct")
    for artifact_path in artifact_paths:
        try:
            artifact_path.lstat()
        except FileNotFoundError:
            continue
        raise EvidenceError(f"supervisor artifact already exists: {artifact_path}")

    started_ns = time.monotonic_ns()
    started_utc = utc_now()
    usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    stdout_capture = BoundedCapture(capture_bytes)
    stderr_capture = BoundedCapture(capture_bytes)
    errors: list[str] = []
    cancel_signal: int | None = None
    termination_reason: str | None = None
    term_sent = False
    kill_sent = False
    proc: StoppedExecProcess | None = None
    out_thread: threading.Thread | None = None
    err_thread: threading.Thread | None = None
    out_thread_started = False
    err_thread_started = False
    exec_status_read: int | None = None
    exec_status_write: int | None = None
    gate_ready_read: int | None = None
    gate_release_write: int | None = None
    exec_status_buffer = bytearray()
    exec_status_complete = False
    exec_success_observed_live = False
    target_exec_failure: dict[str, Any] | None = None
    sealed_rejection: str | None = None
    sealed_interpreter_rejection: str | None = None
    sealed_compiler_facts: dict[str, Any] | None = None
    sealed_interpreter_facts: dict[str, Any] | None = None
    child_env: dict[str, str] | None = None
    child_exit: int | None = None
    child_signal: str | None = None
    readiness_ns: int | None = None
    release_decision_ns: int | None = None
    setup_deadline_ns = started_ns + setup_timeout_ms * 1_000_000
    execution_started_ns: int | None = None
    setup_finished_ns: int | None = None
    child_terminal_observed_ns: int | None = None
    child_reaped_ns: int | None = None
    synthetic_cancel_deadline_ns: int | None = None
    termination_decision_ns: int | None = None
    watched_signals = (signal.SIGHUP, signal.SIGINT, signal.SIGTERM)
    supervisor_runtime_signal_mask = set(initial_signal_mask).difference(
        watched_signals
    )
    old_handlers: dict[int, Any] = {
        signum: signal.getsignal(signum) for signum in watched_signals
    }
    old_sigchld_handler = signal.getsignal(signal.SIGCHLD)
    known_descendants: ProcessHandles = {}
    survivors: list[int] = []
    readiness_published = False
    supervisor_pid = os.getpid()
    supervisor_initial_facts = proc_stat_facts(supervisor_pid)
    supervisor_start_ticks = (
        supervisor_initial_facts[2] if supervisor_initial_facts is not None else 0
    )
    wrapper_pid, wrapper_start_ticks = (
        guardian_identity
        if guardian_identity is not None
        else (supervisor_pid, supervisor_start_ticks)
    )

    def remember_signal(signum: int, _frame: Any) -> None:
        nonlocal cancel_signal
        if cancel_signal is None:
            cancel_signal = signum

    def poll_exec_status() -> None:
        nonlocal exec_status_complete, exec_success_observed_live
        nonlocal target_exec_failure
        if exec_status_read is None or exec_status_complete:
            return
        while True:
            try:
                block = os.read(exec_status_read, MAX_EXEC_STATUS_BYTES + 1)
            except BlockingIOError:
                return
            except InterruptedError:
                continue
            if not block:
                exec_status_complete = True
                if exec_status_buffer:
                    status = parse_json(
                        bytes(exec_status_buffer), subject="target exec status"
                    )
                    if (
                        not isinstance(status, dict)
                        or status.get("schema") != "fln.exec-status/1"
                        or status.get("status") != "failed"
                    ):
                        raise EvidenceError("malformed target exec failure status")
                    target_exec_failure = status
                elif proc is not None and proc.poll() is None:
                    exec_success_observed_live = True
                return
            exec_status_buffer.extend(block)
            if len(exec_status_buffer) > MAX_EXEC_STATUS_BYTES:
                raise EvidenceError("target exec status exceeded its protocol bound")

    def join_drainers() -> None:
        streams = (
            (out_thread, out_thread_started, proc.stdout if proc is not None else None),
            (err_thread, err_thread_started, proc.stderr if proc is not None else None),
        )
        for thread, started, stream in streams:
            if thread is not None and started:
                try:
                    thread.join(max(1.0, grace_ms / 1000 + 1.0))
                except RuntimeError as error:
                    errors.append(f"capture drainer join failed: {error}")
            elif stream is not None and not stream.closed:
                try:
                    stream.close()
                except OSError as error:
                    errors.append(f"unstarted capture stream close failed: {error}")
        if any(
            thread is not None and started and thread.is_alive()
            for thread, started in (
                (out_thread, out_thread_started),
                (err_thread, err_thread_started),
            )
        ):
            errors.append("capture drainer did not terminate after child exit")

    def cleanup_failed_child(first_signal: int) -> None:
        nonlocal term_sent, kill_sent, survivors, child_exit, child_signal
        nonlocal child_reaped_ns, child_terminal_observed_ns
        nonlocal gate_ready_read, gate_release_write
        if proc is None:
            return
        for descriptor_name, descriptor in (
            ("private readiness", gate_ready_read),
            ("private release", gate_release_write),
        ):
            if descriptor is not None:
                try:
                    os.close(descriptor)
                except OSError as error:
                    errors.append(f"{descriptor_name} gate close failed: {error}")
        gate_ready_read = None
        gate_release_write = None
        try:
            if proc.poll() is None and proc.pid not in known_descendants:
                # The unreaped direct child keeps its numeric PID reserved. This
                # fallback is lifetime-safe even if pidfd admission itself failed.
                if proc.pid in proc_children(supervisor_pid):
                    proc.kill()
                    kill_sent = True
                else:
                    errors.append("failed child lost direct-parent containment")
            else:
                sent_term, sent_kill, remaining = terminate_tree(
                    proc,
                    first_signal,
                    grace_ms / 1000,
                    known_descendants,
                    graceful_root_only=True,
                )
                term_sent = term_sent or sent_term
                kill_sent = kill_sent or sent_kill
                survivors = remaining
        except BaseException as error:
            errors.append(
                f"process-tree cleanup failure: {type(error).__name__}: {error}"
            )
            # The direct child PID cannot be reused before this owner reaps it.
            # If it established the promised private session, its process-group
            # number is equally reserved and safely contains ordinary descendants.
            try:
                facts = proc_stat_facts(proc.pid)
                if facts is not None and facts[1] == proc.pid:
                    os.killpg(proc.pid, signal.SIGKILL)
                    kill_sent = True
            except (OSError, EvidenceError) as fallback_error:
                errors.append(f"fallback group kill failed: {fallback_error}")
            try:
                proc.kill()
                kill_sent = True
            except (OSError, EvidenceError) as fallback_error:
                errors.append(f"fallback child kill failed: {fallback_error}")
        try:
            child_return = proc.wait(timeout=max(1.0, grace_ms / 1000 + 1.0))
        except (subprocess.TimeoutExpired, ChildProcessError) as error:
            errors.append(f"child reap failed after supervisor failure: {error}")
            try:
                if process_alive(proc.pid):
                    survivors = sorted(set(survivors) | {proc.pid})
            except EvidenceError as inspection_error:
                errors.append(f"failed child liveness check failed: {inspection_error}")
        else:
            child_reaped_ns = time.monotonic_ns()
            child_terminal_observed_ns = (
                child_terminal_observed_ns or child_reaped_ns
            )
            if child_return < 0:
                child_signal = signal.Signals(-child_return).name
            else:
                child_exit = child_return
        try:
            poll_exec_status()
        except BaseException as error:
            errors.append(
                f"exec status collection failure: {type(error).__name__}: {error}"
            )
        try:
            join_drainers()
        except BaseException as error:
            errors.append(
                f"capture cleanup failure: {type(error).__name__}: {error}"
            )

    rendered_argv, had_redaction = redacted_argv(argv)
    try:
        enable_child_subreaper()
        signal.signal(signal.SIGCHLD, signal.SIG_DFL)
        for signum in watched_signals:
            signal.signal(signum, remember_signal)
        setup_deadline = setup_deadline_ns / 1_000_000_000
        sealed_interpreter_facts = prepare_sealed_interpreter(os.environ)
        if sealed_cargo:
            # The compiler-environment sealing step of the evidence envelope:
            # a rejection here is a typed setup fault recorded in the terminal
            # envelope — the target is never spawned.
            assert suite_lock_path is not None and sealed_build_root is not None
            sealed = prepare_sealed_cargo(
                argv=argv,
                cwd=cwd,
                suite_lock_path=suite_lock_path,
                sealed_build_root=sealed_build_root,
                environ=os.environ,
            )
            argv = sealed["argv"]
            child_env = sealed["env"]
            sealed_compiler_facts = sealed["facts"]
        (
            proc,
            exec_status_read,
            gate_ready_read,
            gate_release_write,
        ) = spawn_stopped_exec(
            argv,
            cwd,
            supervisor_pid,
            target_signal_mask=initial_signal_mask,
            test_before_stop_delay_ms=test_before_stop_delay_ms,
            test_gate_mode=test_gate_mode,
            env=child_env,
        )
        os.set_blocking(exec_status_read, False)
        os.set_blocking(gate_ready_read, False)
        # The child retained the blocked mask across fork. The supervisor can
        # now observe cancellation without exposing target execution.
        signal.pthread_sigmask(
            signal.SIG_SETMASK, supervisor_runtime_signal_mask
        )
        out_thread = threading.Thread(
            target=drain,
            args=(proc.stdout, stdout_capture, errors, "stdout"),
            daemon=True,
        )
        err_thread = threading.Thread(
            target=drain,
            args=(proc.stderr, stderr_capture, errors, "stderr"),
            daemon=True,
        )
        if test_fault_point == "thread_start_stdout":
            raise EvidenceError("injected stdout drainer start failure")
        out_thread.start()
        out_thread_started = True
        if test_fault_point == "thread_start_stderr":
            raise EvidenceError("injected stderr drainer start failure")
        err_thread.start()
        err_thread_started = True
        admission_fd_hoard: list[int] = []
        admission_fd_limit: tuple[int, int] | None = None
        if test_fault_point == "admission_fd_exhaustion":
            # Real resource exhaustion behind a planted trigger: clamp the soft
            # descriptor limit onto the live table and hoard the remainder, so
            # the admission /proc and pidfd binds hit genuine kernel EMFILE.
            # The clamp and hoard are both released before terminal publication
            # needs descriptors again.
            admission_fd_limit = resource.getrlimit(resource.RLIMIT_NOFILE)
            probe_descriptor = os.open("/dev/null", os.O_RDONLY | os.O_CLOEXEC)
            admission_fd_hoard.append(probe_descriptor)
            resource.setrlimit(
                resource.RLIMIT_NOFILE,
                (probe_descriptor + 4, admission_fd_limit[1]),
            )
            try:
                while True:
                    admission_fd_hoard.append(
                        os.open("/dev/null", os.O_RDONLY | os.O_CLOEXEC)
                    )
            except OSError:
                pass
        try:
            child_handle = admit_stopped_session_leader_until(
                proc.pid,
                supervisor_pid,
                setup_deadline,
                gate_ready_descriptor=gate_ready_read,
                cancelled=lambda: cancel_signal is not None,
            )
        finally:
            if admission_fd_limit is not None:
                resource.setrlimit(resource.RLIMIT_NOFILE, admission_fd_limit)
            while admission_fd_hoard:
                os.close(admission_fd_hoard.pop())
        known_descendants[proc.pid] = child_handle
        os.close(gate_ready_read)
        gate_ready_read = None
        child_facts = proc_stat_facts(proc.pid)
        supervisor_facts = proc_stat_facts(supervisor_pid)
        wrapper_facts = proc_stat_facts(wrapper_pid)
        if (
            child_facts is None
            or child_facts[0] != "T"
            or child_facts[1] != proc.pid
            or child_facts[2] != child_handle[0]
            or os.getsid(proc.pid) != proc.pid
            or proc.pid not in proc_children(supervisor_pid)
            or supervisor_facts is None
            or supervisor_facts[2] != supervisor_start_ticks
            or wrapper_facts is None
            or wrapper_facts[0] == "Z"
            or wrapper_facts[2] != wrapper_start_ticks
            or (
                guardian_identity is not None
                and os.getppid() != wrapper_pid
            )
        ):
            raise EvidenceError("cannot capture process identity facts for readiness")
        candidate_readiness_ns = time.monotonic_ns()
        readiness_data = canonical_json(
            {
                "schema": "fln.supervisor-readiness/3",
                "stage_id": stage_id,
                "wrapper_pid": wrapper_pid,
                "wrapper_start_ticks": wrapper_start_ticks,
                "supervisor_pid": supervisor_pid,
                "supervisor_start_ticks": supervisor_start_ticks,
                "child_pid": proc.pid,
                "child_pgid": child_facts[1],
                "child_sid": os.getsid(proc.pid),
                "child_start_ticks": child_facts[2],
                "monotonic_ns": candidate_readiness_ns,
                "status": "ready",
            }
        )
        try:
            if test_fault_point == "readiness_publication":
                raise EvidenceError("injected readiness publication failure")
            write_atomic_new(readiness_path, readiness_data)
        except BaseException as publication_error:
            try:
                retained_readiness, _size, _digest = stable_file_facts(
                    readiness_path, max_bytes=MAX_RECORD_BYTES
                )
            except BaseException:
                raise publication_error
            if not hmac.compare_digest(retained_readiness, readiness_data):
                raise publication_error
            readiness_ns = candidate_readiness_ns
            readiness_published = True
            raise EvidenceError(
                "readiness durability confirmation failed after atomic publication"
            ) from publication_error
        readiness_ns = candidate_readiness_ns
        readiness_published = True
        if test_before_release_delay_ms:
            time.sleep(test_before_release_delay_ms / 1000)
        previous_release_mask = signal.pthread_sigmask(
            signal.SIG_BLOCK, watched_signals
        )
        try:
            pending_before_release = signal.sigpending()
            if cancel_signal is None:
                cancel_signal = next(
                    (
                        signum
                        for signum in watched_signals
                        if signum in pending_before_release
                    ),
                    None,
                )
            if cancel_signal is not None:
                raise SetupCancelledError("cancellation won before target release")
            facts = proc_stat_facts(proc.pid)
            wrapper_facts = proc_stat_facts(wrapper_pid)
            if (
                facts is None
                or facts[0] != "T"
                or facts[1] != proc.pid
                or facts[2] != child_handle[0]
                or os.getsid(proc.pid) != proc.pid
                or proc.pid not in proc_children(supervisor_pid)
                or wrapper_facts is None
                or wrapper_facts[0] == "Z"
                or wrapper_facts[2] != wrapper_start_ticks
                or (
                    guardian_identity is not None
                    and os.getppid() != wrapper_pid
                )
            ):
                raise EvidenceError(
                    "stopped-child identity changed before private release"
                )
            candidate_release_decision_ns = time.monotonic_ns()
            if candidate_release_decision_ns >= setup_deadline_ns:
                raise SetupTimeoutError(
                    "stopped-child admission expired before private release"
                )
            release_decision_ns = candidate_release_decision_ns
            release_view = memoryview(STOPPED_GATE_RELEASE_TOKEN)
            while release_view:
                written = os.write(gate_release_write, release_view)
                if written <= 0:
                    raise EvidenceError("private gate release made no progress")
                release_view = release_view[written:]
            os.close(gate_release_write)
            gate_release_write = None
            if not signal_process_handle(proc.pid, child_handle, signal.SIGCONT):
                raise EvidenceError("cannot release exact stopped child identity")
            execution_started_ns = time.monotonic_ns()
            setup_finished_ns = execution_started_ns
        finally:
            signal.pthread_sigmask(
                signal.SIG_SETMASK,
                (
                    supervisor_runtime_signal_mask
                    if execution_started_ns is not None
                    else previous_release_mask
                ),
            )
        deadline_ns = execution_started_ns + timeout_ms * 1_000_000
        synthetic_cancel_deadline_ns = (
            execution_started_ns + cancel_after_ms * 1_000_000
            if cancel_after_ms is not None
            else None
        )
        child_event_descriptor = os.dup(child_handle[1])
        try:
            child_events = select.poll()
            child_events.register(
                child_event_descriptor,
                select.POLLIN | select.POLLHUP | select.POLLERR,
            )
            while True:
                poll_exec_status()
                live_tree_members(proc.pid, known_descendants)
                now_ns = time.monotonic_ns()
                if cancel_signal is not None:
                    termination_reason = "signal"
                elif (
                    synthetic_cancel_deadline_ns is not None
                    and now_ns >= synthetic_cancel_deadline_ns
                ):
                    cancel_signal = signal.SIGTERM
                    termination_reason = "signal"
                elif stdout_capture.total + stderr_capture.total > output_budget_bytes:
                    termination_reason = "output_budget_exhausted"
                elif now_ns >= deadline_ns:
                    termination_reason = "timeout"
                if termination_reason is not None:
                    termination_decision_ns = termination_decision_ns or now_ns
                    first = (
                        cancel_signal
                        if cancel_signal is not None
                        else signal.SIGTERM
                    )
                    term_sent, kill_sent, survivors = terminate_tree(
                        proc,
                        first,
                        grace_ms / 1000,
                        known_descendants,
                        graceful_root_only=True,
                    )
                    break
                next_deadline_ns = min(
                    deadline_ns,
                    (
                        synthetic_cancel_deadline_ns
                        if synthetic_cancel_deadline_ns is not None
                        else deadline_ns
                    ),
                )
                wait_ns = min(20_000_000, max(0, next_deadline_ns - now_ns))
                wait_ms = (wait_ns + 999_999) // 1_000_000
                if child_events.poll(wait_ms):
                    observed_ns = time.monotonic_ns()
                    child_terminal_observed_ns = observed_ns
                    if cancel_signal is not None:
                        termination_reason = "signal"
                    elif (
                        synthetic_cancel_deadline_ns is not None
                        and observed_ns >= synthetic_cancel_deadline_ns
                    ):
                        cancel_signal = signal.SIGTERM
                        termination_reason = "signal"
                    elif (
                        stdout_capture.total + stderr_capture.total
                        > output_budget_bytes
                    ):
                        termination_reason = "output_budget_exhausted"
                    elif observed_ns >= deadline_ns:
                        termination_reason = "timeout"
                    if termination_reason is None:
                        break
                    termination_decision_ns = (
                        termination_decision_ns or observed_ns
                    )
                    first = (
                        cancel_signal
                        if cancel_signal is not None
                        else signal.SIGTERM
                    )
                    term_sent, kill_sent, survivors = terminate_tree(
                        proc,
                        first,
                        grace_ms / 1000,
                        known_descendants,
                        graceful_root_only=True,
                    )
                    break
        finally:
            os.close(child_event_descriptor)
        child_return = proc.wait(timeout=max(1.0, grace_ms / 1000 + 1.0))
        child_reaped_ns = time.monotonic_ns()
        child_terminal_observed_ns = (
            child_terminal_observed_ns or child_reaped_ns
        )
        poll_exec_status()
        if not exec_status_complete:
            raise EvidenceError("target exec status did not reach a terminal state")
        lingering = live_tree_members(proc.pid, known_descendants)
        if lingering:
            errors.append(f"descendants outlived group leader: {sorted(lingering)}")
            sent_term, sent_kill, survivors = terminate_tree(
                proc, signal.SIGTERM, grace_ms / 1000, known_descendants
            )
            term_sent = term_sent or sent_term
            kill_sent = kill_sent or sent_kill
        join_drainers()
        if any(
            thread is not None and started and thread.is_alive()
            for thread, started in (
                (out_thread, out_thread_started),
                (err_thread, err_thread_started),
            )
        ):
            sent_term, sent_kill, survivors = terminate_tree(
                proc, signal.SIGKILL, grace_ms / 1000, known_descendants
            )
            term_sent = term_sent or sent_term
            kill_sent = kill_sent or sent_kill
        if survivors:
            errors.append(f"process-tree termination left survivors: {survivors}")
        if (
            termination_reason is None
            and stdout_capture.total + stderr_capture.total > output_budget_bytes
        ):
            # A very fast producer can exit between monitor polls. Its completed result
            # still exceeded the declared resource budget and therefore remains typed
            # inconclusive rather than being promoted to pass/fail.
            termination_reason = "output_budget_exhausted"
            termination_decision_ns = termination_decision_ns or time.monotonic_ns()
        if child_return < 0:
            child_signal = signal.Signals(-child_return).name
        else:
            child_exit = child_return
    except SetupCancelledError:
        setup_finished_ns = setup_finished_ns or time.monotonic_ns()
        termination_decision_ns = (
            termination_decision_ns or setup_finished_ns
        )
        termination_reason = "signal"
        cleanup_failed_child(cancel_signal or signal.SIGTERM)
    except SetupTimeoutError:
        setup_finished_ns = setup_finished_ns or time.monotonic_ns()
        termination_decision_ns = (
            termination_decision_ns or setup_finished_ns
        )
        termination_reason = "setup_timeout"
        cleanup_failed_child(signal.SIGTERM)
    except SealedCompilerRejection as error:
        setup_finished_ns = setup_finished_ns or time.monotonic_ns()
        sealed_rejection = error.reason_token
        if error.facts is not None and sealed_compiler_facts is None:
            sealed_compiler_facts = error.facts
        errors.append(f"sealed compiler rejection: {error}")
        cleanup_failed_child(signal.SIGTERM)
    except SealedInterpreterRejection as error:
        setup_finished_ns = setup_finished_ns or time.monotonic_ns()
        sealed_interpreter_rejection = error.reason_token
        sealed_interpreter_facts = error.facts
        errors.append(f"sealed interpreter rejection: {error}")
        cleanup_failed_child(signal.SIGTERM)
    except BaseException as error:
        setup_finished_ns = setup_finished_ns or time.monotonic_ns()
        errors.append(f"supervisor failure: {type(error).__name__}: {error}")
        cleanup_failed_child(signal.SIGTERM)
    finally:
        if exec_status_write is not None:
            os.close(exec_status_write)
            exec_status_write = None
        if exec_status_read is not None:
            os.close(exec_status_read)
            exec_status_read = None
        if gate_ready_read is not None:
            os.close(gate_ready_read)
            gate_ready_read = None
        if gate_release_write is not None:
            os.close(gate_release_write)
            gate_release_write = None
        reap_adopted_children()

    if not readiness_published:
        try:
            readiness_status = {
                "setup_timeout": "setup_timeout",
                "signal": "setup_cancelled",
            }.get(termination_reason, "setup_failed")
            write_atomic_new(
                readiness_path,
                canonical_json(
                    {
                        "schema": "fln.supervisor-readiness/3",
                        "stage_id": stage_id,
                        "wrapper_pid": wrapper_pid,
                        "wrapper_start_ticks": wrapper_start_ticks,
                        "supervisor_pid": supervisor_pid,
                        "supervisor_start_ticks": supervisor_start_ticks,
                        "child_pid": None,
                        "child_pgid": None,
                        "child_sid": None,
                        "child_start_ticks": None,
                        "monotonic_ns": time.monotonic_ns(),
                        "status": readiness_status,
                    }
                ),
            )
            readiness_published = True
        except BaseException as error:
            errors.append(
                f"readiness publication failure: {type(error).__name__}: {error}"
            )

    # Block cancellation while terminal artifacts are selected and published. The
    # disposition change to SIG_IGN below is the single linearization point: signals
    # pending before it are reflected as cancellation; signals after it are post-commit.
    signal.pthread_sigmask(signal.SIG_BLOCK, watched_signals)
    previous_signal_mask = supervisor_runtime_signal_mask
    ended_ns = time.monotonic_ns()
    usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    if survivors and not any("termination left survivors" in error for error in errors):
        errors.append(f"process-tree termination left survivors: {survivors}")
    expected_out = stdout_capture.render()
    expected_err = stderr_capture.render()

    def publish_capture(
        label: str,
        capture_path: Path,
        expected: tuple[bytes, int, int],
    ) -> tuple[bytes, int, int, bool, bool]:
        expected_data, expected_head, expected_tail = expected
        try:
            if test_fault_point == f"capture_{label}":
                raise EvidenceError(f"injected {label} capture publication failure")
            write_atomic_new(capture_path, expected_data)
            return expected_data, expected_head, expected_tail, False, True
        except BaseException as error:
            errors.append(
                f"capture publication failure: {label}: "
                f"{type(error).__name__}: {error}"
            )
        try:
            retained, _size, _digest = stable_file_facts(
                capture_path, max_bytes=capture_bytes
            )
        except FileNotFoundError:
            try:
                write_atomic_new(capture_path, b"")
            except BaseException as fallback_error:
                errors.append(
                    f"capture fallback failure: {label}: "
                    f"{type(fallback_error).__name__}: {fallback_error}"
                )
                return b"", 0, 0, True, False
            return b"", 0, 0, True, True
        except BaseException as inspection_error:
            errors.append(
                f"capture inspection failure: {label}: "
                f"{type(inspection_error).__name__}: {inspection_error}"
            )
            return b"", 0, 0, True, False
        if not hmac.compare_digest(retained, expected_data):
            errors.append(f"capture publication retained unexpected bytes: {label}")
            return b"", 0, 0, True, False
        return retained, expected_head, expected_tail, True, True

    out_data, out_head, out_tail, out_failed, out_available = publish_capture(
        "stdout", stdout_path, expected_out
    )
    err_data, err_head, err_tail, err_failed, err_available = publish_capture(
        "stderr", stderr_path, expected_err
    )
    capture_publication_failed = out_failed or err_failed
    capture_artifacts_available = out_available and err_available

    pending = signal.sigpending()
    if cancel_signal is None:
        cancel_signal = next(
            (signum for signum in watched_signals if signum in pending), None
        )

    def classify_terminal(observed_cancel: int | None) -> tuple[str, str, int]:
        if capture_publication_failed:
            return "internal_fault", "artifact_publication_failure", SETUP_FAILURE
        if sealed_interpreter_rejection is not None:
            return "internal_fault", sealed_interpreter_rejection, SETUP_FAILURE
        if sealed_rejection is not None:
            return "internal_fault", sealed_rejection, SETUP_FAILURE
        if errors:
            return "internal_fault", "supervisor_or_capture_failure", SETUP_FAILURE
        if observed_cancel is not None:
            return (
                "cancelled",
                f"signal_{signal.Signals(observed_cancel).name}",
                CANCELLED,
            )
        if termination_reason in {
            "setup_timeout",
            "timeout",
            "output_budget_exhausted",
        }:
            return "inconclusive", termination_reason, INCONCLUSIVE
        if target_exec_failure is not None:
            return "internal_fault", "target_exec_failure", SETUP_FAILURE
        if child_signal is not None:
            return "inconclusive", f"child_signal_{child_signal}", INCONCLUSIVE
        if child_exit in semantic_exits:
            return "fail", "child_exit_semantic_failure", FAIL
        if child_exit != 0:
            return "internal_fault", "unexpected_child_exit", SETUP_FAILURE
        return "pass", "exit_zero", PASS

    classification, reason_code, wrapper_exit = classify_terminal(cancel_signal)
    if setup_finished_ns is None:
        setup_finished_ns = execution_started_ns or ended_ns
    execution_duration_ns = (
        child_terminal_observed_ns - execution_started_ns
        if execution_started_ns is not None
        and child_terminal_observed_ns is not None
        else None
    )
    exec_status = (
        "not_released"
        if execution_started_ns is None
        else "failed"
        if target_exec_failure is not None
        else "succeeded"
        if exec_status_complete
        and (exec_success_observed_live or child_exit is not None)
        else "unknown"
    )

    metadata: dict[str, Any] = {
        "schema": "fln.supervisor/5",
        "stage_id": stage_id,
        "argv": rendered_argv,
        "argv_redacted": had_redaction,
        "cwd": str(cwd),
        "classification": classification,
        "reason_code": reason_code,
        "sealed_compiler": sealed_compiler_facts,
        "sealed_interpreter": sealed_interpreter_facts,
        "wrapper_exit": wrapper_exit,
        "child_exit": child_exit,
        "child_signal": child_signal,
        "cancel_signal": signal.Signals(cancel_signal).name if cancel_signal else None,
        "planted": planted,
        "semantic_failure_exits": semantic_exits,
        "started_utc": started_utc,
        "ended_utc": utc_now(),
        "monotonic_start_ns": started_ns,
        "monotonic_end_ns": ended_ns,
        "duration_ns": ended_ns - started_ns,
        "phase_timing": {
            "admission_protocol": "same_pid_stopped_private_gate_pidfd/1",
            "setup_start_ns": started_ns,
            "setup_deadline_ns": setup_deadline_ns,
            "readiness_ns": readiness_ns,
            "release_decision_ns": release_decision_ns,
            "setup_end_ns": setup_finished_ns,
            "setup_duration_ns": setup_finished_ns - started_ns,
            "execution_start_ns": execution_started_ns,
            "synthetic_cancel_deadline_ns": synthetic_cancel_deadline_ns,
            "termination_decision_ns": termination_decision_ns,
            "child_terminal_observed_ns": child_terminal_observed_ns,
            "child_reaped_ns": child_reaped_ns,
            "execution_duration_ns": execution_duration_ns,
        },
        "target_exec": {
            "status": exec_status,
            "failure": (
                target_exec_failure if execution_started_ns is not None else None
            ),
        },
        "test_control": {
            "before_stop_delay_ms": test_before_stop_delay_ms,
            "before_release_delay_ms": test_before_release_delay_ms,
            "gate_mode": test_gate_mode,
            "terminal_delay_ms": test_terminal_delay_ms,
            "terminal_ready_enabled": test_terminal_ready_path is not None,
            "fault_point": test_fault_point,
        },
        "resource": {
            "capture_bytes_per_stream": capture_bytes,
            "output_budget_bytes": output_budget_bytes,
            "setup_timeout_ms": setup_timeout_ms,
            "execution_timeout_ms": timeout_ms,
            "cancel_after_ms": cancel_after_ms,
            "kill_grace_ms": grace_ms,
            "total_output_bytes": stdout_capture.total + stderr_capture.total,
            "user_cpu_seconds": max(0.0, usage_after.ru_utime - usage_before.ru_utime),
            "system_cpu_seconds": max(
                0.0, usage_after.ru_stime - usage_before.ru_stime
            ),
            "max_rss_kib_observed": usage_after.ru_maxrss,
            "term_sent": term_sent,
            "kill_sent": kill_sent,
            "process_tree_scope": (
                "linux_nested_subreapers_pidfd_procfs_best_effort"
                if guardian_identity is not None
                else "linux_subreaper_pidfd_procfs_best_effort"
            ),
            "surviving_pids": survivors,
        },
        "stdout": stdout_capture.facts(
            stdout_path.name, len(out_data), out_head, out_tail
        ),
        "stderr": stderr_capture.facts(
            stderr_path.name, len(err_data), err_head, err_tail
        ),
        "errors": errors,
        "readiness": readiness_path.name,
        "host": {
            "platform": platform.platform(),
            "machine": platform.machine(),
            "python": platform.python_version(),
        },
    }
    metadata["stdout"]["retained_sha256"] = hashlib.sha256(out_data).hexdigest()
    metadata["stderr"]["retained_sha256"] = hashlib.sha256(err_data).hexdigest()
    candidate_data: dict[int, bytes] = {}
    base_key = 0

    def candidate_for(observed_cancel: int | None) -> bytes:
        candidate = dict(metadata)
        candidate_class, candidate_reason, candidate_exit = classify_terminal(
            observed_cancel
        )
        candidate["classification"] = candidate_class
        candidate["reason_code"] = candidate_reason
        candidate["wrapper_exit"] = candidate_exit
        candidate["cancel_signal"] = (
            signal.Signals(observed_cancel).name
            if observed_cancel is not None
            else None
        )
        return canonical_json(candidate)

    candidate_data[base_key] = candidate_for(cancel_signal)
    for signum in watched_signals:
        candidate_data[signum] = candidate_for(cancel_signal or signum)

    metadata_parent_fd: int | None = None
    prepared: dict[int, int] = {}
    winner: list[int] = []
    commit_errors: list[BaseException] = []
    try:
        if not readiness_published:
            raise EvidenceError("readiness artifact could not be published")
        if not capture_artifacts_available:
            raise EvidenceError("capture artifacts could not be published")
        if test_fault_point == "metadata_parent_open":
            raise EvidenceError("injected metadata parent-open failure")
        _metadata_parent, metadata_parent_fd = open_directory_nofollow(
            metadata_path.parent, create=True
        )
        del _metadata_parent
        for key, data in candidate_data.items():
            prepared[key] = prepare_atomic_file(metadata_parent_fd, data)
        if test_terminal_ready_path is not None:
            write_atomic_new(test_terminal_ready_path, b"candidates_ready\n")
        if test_terminal_delay_ms:
            time.sleep(test_terminal_delay_ms / 1000)

        def commit_signal(signum: int, _frame: Any) -> None:
            if winner or commit_errors:
                return
            key = signum if signum in prepared else base_key
            try:
                if link_prepared_atomic_file(
                    metadata_parent_fd, prepared[key], metadata_path.name
                ):
                    winner.append(key)
            except BaseException as error:
                commit_errors.append(error)

        for signum in watched_signals:
            signal.signal(signum, commit_signal)
        signal.pthread_sigmask(signal.SIG_SETMASK, previous_signal_mask)
        if not winner and not commit_errors:
            initial_key = cancel_signal or base_key
            if link_prepared_atomic_file(
                metadata_parent_fd, prepared[initial_key], metadata_path.name
            ):
                winner.append(initial_key)
        signal.pthread_sigmask(signal.SIG_BLOCK, watched_signals)
        for signum in watched_signals:
            signal.signal(signum, signal.SIG_IGN)
        signal.pthread_sigmask(signal.SIG_SETMASK, previous_signal_mask)
        if commit_errors:
            raise commit_errors[0]
        if len(winner) != 1:
            raise EvidenceError("metadata atomic publication had no unique winner")
        selected = parse_json(candidate_data[winner[0]], subject="metadata candidate")
        if not isinstance(selected, dict):
            raise EvidenceError("metadata candidate is not an object")
        classification = str(selected["classification"])
        reason_code = str(selected["reason_code"])
        wrapper_exit = int(selected["wrapper_exit"])
    except BaseException as error:
        fallback = {
            "schema": "fln.supervisor/5",
            "classification": "internal_fault",
            "reason_code": "metadata_publication_failure",
            "metadata_path": str(metadata_path),
            "error": f"{type(error).__name__}: {error}",
        }
        try:
            sys.stderr.buffer.write(canonical_json(fallback))
        except BaseException:
            pass
        if restore_signal_state:
            for signum, handler in old_handlers.items():
                signal.signal(signum, handler)
            signal.signal(signal.SIGCHLD, old_sigchld_handler)
            signal.pthread_sigmask(signal.SIG_SETMASK, previous_signal_mask)
        return SETUP_FAILURE
    finally:
        for descriptor in prepared.values():
            try:
                os.close(descriptor)
            except OSError:
                pass
        if metadata_parent_fd is not None:
            try:
                os.close(metadata_parent_fd)
            except OSError:
                pass
        close_process_handles(known_descendants)
    if restore_signal_state:
        signal.pthread_sigmask(signal.SIG_BLOCK, watched_signals)
        for signum, handler in old_handlers.items():
            signal.signal(signum, handler)
        signal.signal(signal.SIGCHLD, old_sigchld_handler)
        signal.pthread_sigmask(signal.SIG_SETMASK, previous_signal_mask)
    return wrapper_exit


def parse_rust_lock(lock_path: Path) -> dict[str, str]:
    """Read the pinned Rust rows of SUITE.lock and enforce the lock's own law
    that `rust-nightly` equals rust-toolchain.toml's `[toolchain].channel`."""
    try:
        lock_text = lock_path.read_text(encoding="utf-8")
    except OSError as error:
        raise SealedCompilerRejection(
            "sealed_compiler_lock_unreadable", f"cannot read {lock_path}: {error}"
        ) from error
    rows: dict[str, str] = {}
    for line in lock_text.splitlines():
        line = line.strip()
        for key in ("rust-nightly", "rust-release", "rust-commit"):
            prefix = f"{key} "
            if line.startswith(prefix):
                rows[key] = line[len(prefix) :].strip()
    missing = sorted(
        key for key in ("rust-nightly", "rust-release", "rust-commit") if key not in rows
    )
    if missing:
        raise SealedCompilerRejection(
            "sealed_compiler_lock_incomplete",
            f"{lock_path} lacks pinned rust rows: {missing}",
        )
    toolchain_toml = lock_path.parent / "rust-toolchain.toml"
    try:
        toml_text = toolchain_toml.read_text(encoding="utf-8")
    except OSError as error:
        raise SealedCompilerRejection(
            "sealed_compiler_toolchain_toml_unreadable",
            f"cannot read {toolchain_toml}: {error}",
        ) from error
    channel_match = re.search(
        r'^\s*channel\s*=\s*"([^"]+)"', toml_text, flags=re.MULTILINE
    )
    if channel_match is None or channel_match.group(1) != rows["rust-nightly"]:
        raise SealedCompilerRejection(
            "sealed_compiler_channel_disagreement",
            f"rust-toolchain.toml channel {channel_match.group(1) if channel_match else None!r} "
            f"!= SUITE.lock rust-nightly {rows['rust-nightly']!r}",
        )
    return rows


def scan_hostile_compiler_env(environ: Mapping[str, str]) -> list[str]:
    offenders = [name for name in environ if name in HOSTILE_COMPILER_ENV_EXACT]
    offenders.extend(
        name
        for name in environ
        if name not in SEALED_ENV_OVERRIDDEN
        and name not in HOSTILE_COMPILER_ENV_EXACT
        and any(name.startswith(prefix) for prefix in HOSTILE_COMPILER_ENV_PREFIXES)
    )
    return sorted(set(offenders))


def scan_ancestor_cargo_config(cwd: Path) -> list[str]:
    """Cargo discovers `.cargo/config{,.toml}` in cwd and every ancestor; any
    such file would inject configuration beneath the sealed environment."""
    offenders: list[str] = []
    node = cwd
    while True:
        for name in ("config.toml", "config"):
            candidate = node / ".cargo" / name
            if candidate.is_file():
                offenders.append(str(candidate))
        if node.parent == node:
            break
        node = node.parent
    return sorted(offenders)


def resolve_sealed_toolchain(lock_rows: Mapping[str, str]) -> dict[str, str]:
    """Locate the pinned rustup toolchain and prove its identity: the resolved
    rustc must report exactly the locked release and commit hash."""
    machine = platform.machine()
    triple = SEALED_HOST_TRIPLES.get(machine)
    if triple is None:
        raise SealedCompilerRejection(
            "sealed_compiler_unsupported_host",
            f"no sealed host triple registered for machine {machine!r}",
        )
    rustup_home = Path(os.environ.get("RUSTUP_HOME", "") or Path.home() / ".rustup")
    toolchain_root = rustup_home / "toolchains" / f"{lock_rows['rust-nightly']}-{triple}"
    rustc_path = toolchain_root / "bin" / "rustc"
    cargo_path = toolchain_root / "bin" / "cargo"
    if not rustc_path.is_file() or not cargo_path.is_file():
        raise SealedCompilerRejection(
            "sealed_compiler_toolchain_unresolved",
            f"pinned toolchain binaries absent under {toolchain_root}",
        )
    probe_env = {"PATH": SEALED_PATH_TAIL, "HOME": str(Path.home())}
    try:
        probe = subprocess.run(  # ubs:ignore — argv is the SUITE.lock-resolved pinned rustc with a fixed flag, never user input.
            [str(rustc_path), "-vV"],
            capture_output=True,
            text=True,
            timeout=SEALED_RUSTC_PROBE_TIMEOUT_S,
            env=probe_env,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise SealedCompilerRejection(
            "sealed_compiler_probe_failure", f"rustc -vV probe failed: {error}"
        ) from error
    facts = {
        key.strip(): value.strip()
        for key, _, value in (
            line.partition(":") for line in probe.stdout.splitlines() if ":" in line
        )
    }
    release = facts.get("release", "")
    commit = facts.get("commit-hash", "")
    if (
        probe.returncode != 0
        or release != lock_rows["rust-release"]  # ubs:ignore — public compiler identity, not a secret.
        or commit != lock_rows["rust-commit"]  # ubs:ignore — public content-integrity digest, not authentication material.
    ):
        raise SealedCompilerRejection(
            "sealed_compiler_identity_mismatch",
            f"resolved rustc identity release={release!r} commit={commit!r} "
            f"does not match SUITE.lock release={lock_rows['rust-release']!r} "
            f"commit={lock_rows['rust-commit']!r} (probe exit {probe.returncode})",
        )
    return {
        "channel": lock_rows["rust-nightly"],
        "release": release,
        "commit": commit,
        "toolchain_root": str(toolchain_root),
        "rustc_path": str(rustc_path),
        "cargo_path": str(cargo_path),
    }


def prepare_sealed_cargo(
    *,
    argv: Sequence[str],
    cwd: Path,
    suite_lock_path: Path,
    sealed_build_root: Path,
    environ: Mapping[str, str],
) -> dict[str, Any]:
    """The compiler-environment sealing step of the evidence envelope: reject
    hostile channels, prove the pinned toolchain's identity, isolate Cargo
    home/target for this attempt, rebuild PATH, and rewrite `cargo` to the
    pinned absolute binary. Returns {argv, env, facts}."""
    hostile = scan_hostile_compiler_env(environ)
    if hostile:
        raise SealedCompilerRejection(
            "sealed_compiler_hostile_environment",
            f"hostile compiler channels present: {','.join(hostile)}",
            facts={"rejected_env": hostile},
        )
    ambient_configs = scan_ancestor_cargo_config(cwd)
    if ambient_configs:
        raise SealedCompilerRejection(
            "sealed_compiler_ambient_config",
            f"cargo config discovery would inject: {','.join(ambient_configs)}",
            facts={"rejected_configs": ambient_configs},
        )
    lock_rows = parse_rust_lock(suite_lock_path)
    toolchain = resolve_sealed_toolchain(lock_rows)
    cargo_home = sealed_build_root / "cargo-home"
    target_dir = sealed_build_root / "target"
    try:
        cargo_home.mkdir(parents=True, exist_ok=True)
        target_dir.mkdir(parents=True, exist_ok=True)
    except OSError as error:
        raise SealedCompilerRejection(
            "sealed_compiler_build_root_unavailable",
            f"cannot create sealed build state under {sealed_build_root}: {error}",
        ) from error
    for name in ("config.toml", "config"):
        if (cargo_home / name).exists():
            raise SealedCompilerRejection(
                "sealed_compiler_ambient_config",
                f"sealed cargo home unexpectedly carries {name}",
            )
    sealed_env: dict[str, str] = {
        name: environ[name]
        for name in environ
        if name in SEALED_ENV_ALLOWLIST or name.startswith("LC_")
    }
    sealed_env["PATH"] = f"{toolchain['toolchain_root']}/bin:{SEALED_PATH_TAIL}"
    sealed_env["CARGO_HOME"] = str(cargo_home)
    sealed_env["CARGO_TARGET_DIR"] = str(target_dir)
    sealed_env["RUSTC"] = toolchain["rustc_path"]
    argv = list(argv)
    original_argv0 = argv[0] if argv else ""
    if argv and argv[0] == "cargo":
        argv[0] = toolchain["cargo_path"]
    facts = {
        **toolchain,
        "cargo_home": str(cargo_home),
        "target_dir": str(target_dir),
        "admitted_env": sorted(sealed_env),
        "overridden_env": sorted(
            {
                name
                for name in environ
                if name in SEALED_ENV_OVERRIDDEN
            }
        ),
        "rejected_env": [],
        "original_argv0": original_argv0,
        "effective_argv0": argv[0] if argv else "",
    }
    return {"argv": argv, "env": sealed_env, "facts": facts}


def run_supervised(
    *,
    argv: Sequence[str],
    cwd: Path,
    metadata_path: Path,
    stdout_path: Path,
    stderr_path: Path,
    readiness_path: Path,
    artifact_root: Path,
    capture_bytes: int,
    output_budget_bytes: int,
    timeout_ms: int,
    grace_ms: int,
    stage_id: str,
    planted: bool,
    setup_timeout_ms: int = MAX_PROCESS_IDENTITY_WAIT_MS,
    semantic_failure_exits: Sequence[int] = (),
    cancel_after_ms: int | None = None,
    restore_signal_state: bool = True,
    test_terminal_delay_ms: int = 0,
    test_terminal_ready_path: Path | None = None,
    guardian_identity: tuple[int, int] | None = None,
    initial_signal_mask: set[signal.Signals] | None = None,
    test_before_stop_delay_ms: int = 0,
    test_before_release_delay_ms: int = 0,
    test_gate_mode: str = "normal",
    test_fault_point: str = "none",
    sealed_cargo: bool = False,
    suite_lock_path: Path | None = None,
    sealed_build_root: Path | None = None,
) -> int:
    """Run one isolated supervisor while restoring all caller process state."""
    watched = (signal.SIGHUP, signal.SIGINT, signal.SIGTERM)
    entry_handlers = {signum: signal.getsignal(signum) for signum in watched}
    entry_sigchld_handler = signal.getsignal(signal.SIGCHLD)
    entry_signal_mask = signal.pthread_sigmask(signal.SIG_BLOCK, watched)
    entry_subreaper: bool | None = None
    try:
        entry_subreaper = child_subreaper_enabled()
        try:
            task_ids = {
                int(entry.name)
                for entry in Path("/proc/self/task").iterdir()
                if entry.name.isdecimal()
            }
        except OSError as error:
            raise EvidenceError("cannot prove supervisor thread state") from error
        if threading.active_count() != 1 or task_ids != {os.getpid()}:
            raise EvidenceError("supervisor requires an exclusive single-thread process")
        existing_children = proc_children(os.getpid())
        if existing_children:
            raise EvidenceError(
                "supervisor process already owns unrelated child lifetimes: "
                f"{sorted(existing_children)}"
            )
        target_signal_mask = (
            set(initial_signal_mask)
            if initial_signal_mask is not None
            else set(entry_signal_mask)
        )
        return _run_supervised_impl(
            argv=argv,
            cwd=cwd,
            metadata_path=metadata_path,
            stdout_path=stdout_path,
            stderr_path=stderr_path,
            readiness_path=readiness_path,
            artifact_root=artifact_root,
            capture_bytes=capture_bytes,
            output_budget_bytes=output_budget_bytes,
            timeout_ms=timeout_ms,
            grace_ms=grace_ms,
            stage_id=stage_id,
            planted=planted,
            setup_timeout_ms=setup_timeout_ms,
            semantic_failure_exits=semantic_failure_exits,
            cancel_after_ms=cancel_after_ms,
            restore_signal_state=False,
            test_terminal_delay_ms=test_terminal_delay_ms,
            test_terminal_ready_path=test_terminal_ready_path,
            guardian_identity=guardian_identity,
            initial_signal_mask=target_signal_mask,
            test_before_stop_delay_ms=test_before_stop_delay_ms,
            test_before_release_delay_ms=test_before_release_delay_ms,
            test_gate_mode=test_gate_mode,
            test_fault_point=test_fault_point,
            sealed_cargo=sealed_cargo,
            suite_lock_path=suite_lock_path,
            sealed_build_root=sealed_build_root,
        )
    finally:
        signal.pthread_sigmask(signal.SIG_BLOCK, watched)
        for signum, handler in entry_handlers.items():
            signal.signal(signum, handler)
        signal.signal(signal.SIGCHLD, entry_sigchld_handler)
        if (
            entry_subreaper is not None
            and child_subreaper_enabled() != entry_subreaper
        ):
            set_child_subreaper(entry_subreaper)
        signal.pthread_sigmask(signal.SIG_SETMASK, entry_signal_mask)


def load_ndjson_snapshot(path: Path) -> tuple[list[dict[str, Any]], str]:
    data, _size, digest = stable_file_facts(path, max_bytes=MAX_LOG_BYTES)
    records: list[dict[str, Any]] = []
    for number, raw in enumerate(data.splitlines(keepends=True), 1):
        if len(raw) > MAX_RECORD_BYTES:
            raise EvidenceError(f"{path}:{number}: record too large")
        if not raw.endswith(b"\n"):
            raise EvidenceError(f"{path}:{number}: unterminated record")
        value = parse_json(raw, subject=f"{path}:{number}")
        if not isinstance(value, dict):
            raise EvidenceError(f"{path}:{number}: record is not an object")
        records.append(value)
    if not records:
        raise EvidenceError(f"NDJSON is empty: {path}")
    return records, digest


def load_ndjson(path: Path) -> list[dict[str, Any]]:
    records, _digest = load_ndjson_snapshot(path)
    return records


def render_check_human(records: Sequence[Mapping[str, Any]]) -> bytes:
    if not records:
        raise EvidenceError("cannot render an empty check run")
    if any(record.get("schema") != "fln.check/2" for record in records):
        raise EvidenceError("human renderer accepts only fln.check/2 records")
    lines = [f"{CHECK_HUMAN_SCHEMA} records={len(records)}\n"]
    for record in records:
        event = record.get("event")
        if event == "run_start":
            subject = record.get("scenario")
            outcome = "started"
            reason = "none"
        elif event == "stage":
            subject = record.get("stage")
            outcome = record.get("outcome")
            reason = record.get("reason_code")
        elif event == "self_test":
            subject = record.get("stage")
            outcome = "pass" if record.get("ok") is True else "fail"
            reason = "self_test_result"
        elif event == "run_end":
            subject = record.get("scenario")
            outcome = record.get("verdict")
            reason = record.get("reason_code")
        else:
            raise EvidenceError(f"human renderer rejects event {event!r}")
        values = {
            "event": event,
            "outcome": outcome,
            "reason": reason,
            "subject": subject,
        }
        if not all(isinstance(value, str) and value for value in values.values()):
            raise EvidenceError("human renderer received an incomplete event")
        record_digest = hashlib.sha256(canonical_json(record)).hexdigest()
        lines.append(
            " ".join(
                (
                    f"sequence={record.get('sequence')}",
                    *(
                        f"{key}={json.dumps(value, ensure_ascii=True)}"
                        for key, value in values.items()
                    ),
                    f"record_sha256={record_digest}",
                )
            )
            + "\n"
        )
    return "".join(lines).encode("utf-8")


def validate_check_human(run_path: Path, human_path: Path) -> dict[str, Any]:
    run_path = lexical_absolute(run_path)
    human_path = lexical_absolute(human_path)
    records, run_digest = load_ndjson_snapshot(run_path)
    expected = render_check_human(records)
    actual, size, digest = stable_file_facts(human_path, max_bytes=MAX_LOG_BYTES)
    if not hmac.compare_digest(actual, expected):
        raise EvidenceError(f"{human_path}: human/NDJSON event rendering differs")
    return {
        "schema": "fln.validation/1",
        "validator": CHECK_HUMAN_SCHEMA,
        "subject": human_path.name,
        "valid": True,
        "records": len(records),
        "bytes": size,
        "sha256": digest,
        "run_sha256": run_digest,
    }


def verification_adoption_hash(ids: Sequence[str]) -> str:
    digest = hashlib.sha256()
    digest.update(b"fln.verification-manifest.adoption.ids/1")
    digest.update(b"\0")
    for bead_id in ids:
        encoded = bead_id.encode("utf-8")
        digest.update(len(encoded).to_bytes(8, "little"))
        digest.update(encoded)
    return f"sha256:{digest.hexdigest()}"


def verification_adoption_authority_hash(
    ids: Sequence[str], open_ids: Sequence[str]
) -> str:
    digest = hashlib.sha256()
    digest.update(b"fln.verification-manifest.adoption-authority/1")
    digest.update(b"\0")
    for label, values in ((b"ids", ids), (b"open", open_ids)):
        digest.update(len(label).to_bytes(8, "little"))
        digest.update(label)
        digest.update(len(values).to_bytes(8, "little"))
        for bead_id in values:
            encoded = bead_id.encode("utf-8")
            digest.update(len(encoded).to_bytes(8, "little"))
            digest.update(encoded)
    return f"sha256:{digest.hexdigest()}"


def require_manifest_string_array(
    path: Path,
    record_number: int,
    record: Mapping[str, Any],
    field: str,
    *,
    nonempty: bool,
) -> list[str]:
    value = record.get(field)
    if not isinstance(value, list) or not all(
        isinstance(item, str) and item for item in value
    ):
        raise EvidenceError(
            f"{path}:{record_number}: {field} must be a string array"
        )
    if len(value) != len(set(value)) or value != sorted(value):
        raise EvidenceError(
            f"{path}:{record_number}: {field} must be sorted and duplicate-free"
        )
    if nonempty and not value:
        raise EvidenceError(f"{path}:{record_number}: {field} must not be empty")
    return value


def bead_status_projection(path: Path) -> dict[str, str]:
    records, _digest = load_ndjson_snapshot(path)
    states: dict[str, str] = {}
    for number, record in enumerate(records, 1):
        bead_id = record.get("id")
        status = record.get("status")
        if not isinstance(bead_id, str) or not bead_id:
            raise EvidenceError(f"{path}:{number}: bead id is missing")
        if status not in {"open", "in_progress", "closed", "tombstone"}:
            raise EvidenceError(
                f"{path}:{number}: bead {bead_id!r} has unsupported status {status!r}"
            )
        if bead_id in states:
            raise EvidenceError(f"{path}:{number}: duplicate bead id {bead_id!r}")
        states[bead_id] = status
    return states


def derived_verification_coverage_state(bead_status: str, skip: str) -> str:
    """Derive lifecycle state from the tracker; coverage rows never declare it."""
    if bead_status == "open":
        return "blocked" if skip == "blocked" else "planned"
    if bead_status == "in_progress":
        return "active"
    if bead_status in {"closed", "tombstone"}:
        return "complete"
    raise EvidenceError(
        f"cannot derive verification coverage from bead status {bead_status!r}"
    )


def validate_verification_manifest(
    manifest_path: Path,
    beads_path: Path,
    *,
    expected_adoption_authority_hash: str = VERIFICATION_ADOPTION_AUTHORITY_HASH,
) -> dict[str, Any]:
    manifest_path = lexical_absolute(manifest_path)
    beads_path = lexical_absolute(beads_path)
    records, manifest_digest = load_ndjson_snapshot(manifest_path)
    header = records[0]
    header_keys = {
        "schema",
        "kind",
        "source",
        "projection",
        "hash_algorithm",
        "hash_preimage",
        "record_count",
        "projection_hash",
        "adoption_ids",
        "adoption_open_ids",
    }
    if set(header) != header_keys:
        raise EvidenceError(
            f"{manifest_path}: adoption header shape differs: "
            f"missing={sorted(header_keys - set(header))!r} "
            f"extra={sorted(set(header) - header_keys)!r}"
        )
    if (
        header.get("schema") != VERIFICATION_MANIFEST_SCHEMA
        or header.get("kind") != "adoption"
        or header.get("source") != ".beads/issues.jsonl"
        or header.get("projection") != "sorted-canonical-bead-ids-v1"
        or header.get("hash_algorithm") != "sha256"
        or header.get("hash_preimage")
        != "fln.verification-manifest.adoption.ids/1+nul+u64le-length-prefixed-utf8"
    ):
        raise EvidenceError(f"{manifest_path}: invalid adoption authority header")
    adoption_ids = require_manifest_string_array(
        manifest_path, 1, header, "adoption_ids", nonempty=True
    )
    adoption_open_ids = require_manifest_string_array(
        manifest_path, 1, header, "adoption_open_ids", nonempty=False
    )
    if not set(adoption_open_ids).issubset(adoption_ids):
        raise EvidenceError(
            f"{manifest_path}: adoption_open_ids is not a subset of adoption_ids"
        )
    if (
        not isinstance(header.get("record_count"), int)
        or isinstance(header["record_count"], bool)
        or header["record_count"] != len(adoption_ids)
    ):
        raise EvidenceError(f"{manifest_path}: adoption record_count is stale")
    expected_projection_hash = verification_adoption_hash(adoption_ids)
    if not hmac.compare_digest(
        str(header.get("projection_hash")), expected_projection_hash
    ):
        raise EvidenceError(f"{manifest_path}: adoption projection hash is stale")
    actual_adoption_authority_hash = verification_adoption_authority_hash(
        adoption_ids, adoption_open_ids
    )
    if not hmac.compare_digest(
        actual_adoption_authority_hash, expected_adoption_authority_hash
    ):
        raise EvidenceError(
            f"{manifest_path}: adoption authority differs from the frozen migration"
        )

    coverage_keys = {
        "schema",
        "kind",
        "bead",
        "owner",
        "workstream",
        "claim_type",
        "evidence_kind",
        "mock_only",
        "skip",
        *VERIFICATION_COVERAGE_ARRAY_FIELDS,
    }
    scenario_keys = {
        "schema",
        "kind",
        "scenario",
        "owner",
        "activation",
        "claim_type",
        "evidence_kind",
        "gate_ids",
        "ci_required",
        "ci_root",
        "artifact_kind",
        "artifact_name",
    }
    bead_states = bead_status_projection(beads_path)
    coverage: dict[str, dict[str, Any]] = {}
    coverage_numbers: dict[str, int] = {}
    scenarios: dict[str, dict[str, Any]] = {}
    order: list[tuple[int, str]] = []
    for number, record in enumerate(records[1:], 2):
        if record.get("schema") != VERIFICATION_MANIFEST_SCHEMA:
            raise EvidenceError(f"{manifest_path}:{number}: wrong manifest schema")
        kind = record.get("kind")
        if kind == "coverage":
            if set(record) != coverage_keys:
                raise EvidenceError(
                    f"{manifest_path}:{number}: coverage shape differs: "
                    f"missing={sorted(coverage_keys - set(record))!r} "
                    f"extra={sorted(set(record) - coverage_keys)!r}"
                )
            bead_id = record.get("bead")
            if not isinstance(bead_id, str) or not bead_id:
                raise EvidenceError(
                    f"{manifest_path}:{number}: coverage bead is missing"
                )
            if bead_id in coverage:
                raise EvidenceError(
                    f"{manifest_path}:{number}: duplicate coverage row for {bead_id}"
                )
            order.append((0, bead_id))
            coverage[bead_id] = record
            coverage_numbers[bead_id] = number
            for field in ("owner", "workstream"):
                if not isinstance(record.get(field), str) or not record[field]:
                    raise EvidenceError(
                        f"{manifest_path}:{number}: coverage {field} is missing"
                    )
            if not re.fullmatch(r"W[0-9]+", record["workstream"]):
                raise EvidenceError(
                    f"{manifest_path}:{number}: invalid workstream identity"
                )
            claim_type = record.get("claim_type")
            evidence_kind = record.get("evidence_kind")
            if claim_type not in VERIFICATION_CLAIM_TYPES:
                raise EvidenceError(
                    f"{manifest_path}:{number}: invalid claim_type {claim_type!r}"
                )
            if evidence_kind not in VERIFICATION_EVIDENCE_KINDS:
                raise EvidenceError(
                    f"{manifest_path}:{number}: invalid evidence_kind {evidence_kind!r}"
                )
            if not isinstance(record.get("mock_only"), bool):
                raise EvidenceError(
                    f"{manifest_path}:{number}: mock_only must be boolean"
                )
            skip = record.get("skip")
            if skip not in {"none", "typed_limitation", "blocked"}:
                raise EvidenceError(
                    f"{manifest_path}:{number}: unclassified skip {skip!r}"
                )
            for field in VERIFICATION_COVERAGE_ARRAY_FIELDS:
                require_manifest_string_array(
                    manifest_path,
                    number,
                    record,
                    field,
                    nonempty=False,
                )
            if claim_type in {"invariant", "proof"}:
                if record["mock_only"] or evidence_kind not in {
                    "no_mock_e2e",
                    "proof",
                }:
                    raise EvidenceError(
                        f"{manifest_path}:{number}: {claim_type} claim has "
                        f"insufficient {evidence_kind} evidence"
                    )
                if not record["invariant_ids"]:
                    raise EvidenceError(
                        f"{manifest_path}:{number}: authoritative claim lacks invariant ids"
                    )
        elif kind == "scenario":
            if set(record) != scenario_keys:
                raise EvidenceError(
                    f"{manifest_path}:{number}: scenario shape differs: "
                    f"missing={sorted(scenario_keys - set(record))!r} "
                    f"extra={sorted(set(record) - scenario_keys)!r}"
                )
            scenario = record.get("scenario")
            if not isinstance(scenario, str) or not scenario:
                raise EvidenceError(
                    f"{manifest_path}:{number}: scenario identity is missing"
                )
            if scenario in scenarios:
                raise EvidenceError(
                    f"{manifest_path}:{number}: duplicate scenario {scenario!r}"
                )
            order.append((1, scenario))
            scenarios[scenario] = record
            if not isinstance(record.get("owner"), str) or not record["owner"]:
                raise EvidenceError(
                    f"{manifest_path}:{number}: scenario owner is missing"
                )
            activation = record.get("activation")
            if activation not in {"planned", "active", "blocked"}:
                raise EvidenceError(
                    f"{manifest_path}:{number}: invalid scenario activation"
                )
            if record.get("claim_type") not in VERIFICATION_CLAIM_TYPES:
                raise EvidenceError(
                    f"{manifest_path}:{number}: invalid scenario claim_type"
                )
            if record.get("evidence_kind") not in VERIFICATION_EVIDENCE_KINDS:
                raise EvidenceError(
                    f"{manifest_path}:{number}: invalid scenario evidence_kind"
                )
            if record["claim_type"] in {"invariant", "proof"} and record[
                "evidence_kind"
            ] not in {"no_mock_e2e", "proof"}:
                raise EvidenceError(
                    f"{manifest_path}:{number}: {record['claim_type']} scenario has "
                    f"insufficient {record['evidence_kind']} evidence"
                )
            require_manifest_string_array(
                manifest_path, number, record, "gate_ids", nonempty=True
            )
            if not isinstance(record.get("ci_required"), bool):
                raise EvidenceError(
                    f"{manifest_path}:{number}: ci_required must be boolean"
                )
            if activation != "active":
                if (
                    record["ci_required"]
                    or record.get("ci_root") != "-"
                    or record.get("artifact_kind") != "none"
                    or record.get("artifact_name") != "-"
                ):
                    raise EvidenceError(
                        f"{manifest_path}:{number}: planned/blocked scenario "
                        "cannot count as executed"
                    )
            elif record["ci_required"]:
                if (
                    not isinstance(record.get("ci_root"), str)
                    or not re.fullmatch(
                        r"(?:check|e2e)/[a-z0-9][a-z0-9-]*", record["ci_root"]
                    )
                    or record.get("artifact_kind")
                    not in {"direct", "single-bundle", "named-child"}
                ):
                    raise EvidenceError(
                        f"{manifest_path}:{number}: active CI scenario lacks "
                        "an exact artifact contract"
                    )
                if record["artifact_kind"] == "named-child":
                    if (
                        not isinstance(record.get("artifact_name"), str)
                        or record["artifact_name"] in {"", "-"}
                    ):
                        raise EvidenceError(
                            f"{manifest_path}:{number}: named child is missing"
                        )
                elif record.get("artifact_name") != "-":
                    raise EvidenceError(
                        f"{manifest_path}:{number}: non-named artifact has a child name"
                    )
            elif (
                record.get("ci_root") != "-"
                or record.get("artifact_kind") != "none"
                or record.get("artifact_name") != "-"
            ):
                raise EvidenceError(
                    f"{manifest_path}:{number}: non-CI scenario claims CI artifacts"
                )
        else:
            raise EvidenceError(
                f"{manifest_path}:{number}: unknown manifest row kind {kind!r}"
            )
    if order != sorted(order):
        raise EvidenceError(
            f"{manifest_path}: rows must be coverage-then-scenario canonical order"
        )

    current_ids = set(bead_states)
    adopted = set(adoption_ids)
    missing_adopted = sorted(adopted - current_ids)
    if missing_adopted:
        raise EvidenceError(
            f"{manifest_path}: adopted beads disappeared: {missing_adopted!r}"
        )
    derived_state_counts = {
        "planned": 0,
        "active": 0,
        "complete": 0,
        "blocked": 0,
    }
    for bead_id, record in coverage.items():
        if bead_id not in bead_states:
            raise EvidenceError(
                f"{manifest_path}: orphan coverage row for {bead_id!r}"
            )
        derived_state = derived_verification_coverage_state(
            bead_states[bead_id], record["skip"]
        )
        derived_state_counts[derived_state] += 1
        number = coverage_numbers[bead_id]
        if derived_state in {"active", "complete"} and record["skip"] != "none":
            raise EvidenceError(
                f"{manifest_path}:{number}: {derived_state} coverage cannot be skipped"
            )
        if derived_state == "blocked" and record["skip"] != "blocked":
            raise EvidenceError(
                f"{manifest_path}:{number}: blocked coverage lacks blocked classification"
            )
        if derived_state == "complete":
            for field in VERIFICATION_COVERAGE_ARRAY_FIELDS:
                if field not in VERIFICATION_COVERAGE_REQUIRED_FIELDS:
                    continue
                require_manifest_string_array(
                    manifest_path,
                    number,
                    record,
                    field,
                    nonempty=True,
                )
    required_coverage = current_ids - adopted
    required_coverage.update(
        bead_id
        for bead_id in adoption_open_ids
        if bead_states.get(bead_id) != "open"
    )
    missing_coverage = sorted(required_coverage - set(coverage))
    if missing_coverage:
        raise EvidenceError(
            f"{manifest_path}: beads crossed the adoption boundary without "
            f"coverage rows: {missing_coverage!r}"
        )
    for scenario, record in scenarios.items():
        owner = record["owner"]
        if owner not in bead_states:
            raise EvidenceError(
                f"{manifest_path}: scenario {scenario!r} has orphan owner {owner!r}"
            )
    for bead_id, record in coverage.items():
        for scenario in record["scenarios"]:
            registered = scenarios.get(scenario)
            if registered is None:
                raise EvidenceError(
                    f"{manifest_path}: coverage {bead_id!r} names unregistered "
                    f"scenario {scenario!r}"
                )
            # Scenario ownership names the bead responsible for maintaining the
            # lane and its artifact contract. It is not an exclusive-consumer
            # lock: several coverage rows may honestly rely on one active CI
            # scenario without duplicating the same execution artifact.
            if (
                registered["activation"] != "active"
                or registered["ci_required"] is not True
            ):
                raise EvidenceError(
                    f"{manifest_path}: coverage {bead_id!r} cannot claim "
                    f"unexecuted scenario {scenario!r}"
                )
    return {
        "schema": "fln.validation/1",
        "validator": VERIFICATION_MANIFEST_SCHEMA,
        "subject": manifest_path.name,
        "valid": True,
        "sha256": manifest_digest,
        "adoption_records": len(adoption_ids),
        "current_beads": len(bead_states),
        "coverage_rows": len(coverage),
        "coverage_state_source": ".beads/issues.jsonl",
        "derived_state_counts": derived_state_counts,
        "scenario_rows": len(scenarios),
        "ci_scenarios": sorted(
            scenario
            for scenario, record in scenarios.items()
            if record["activation"] == "active" and record["ci_required"]
        ),
    }


def require_guard_keys(
    path: Path, record: Mapping[str, Any], expected: set[str], *, label: str
) -> None:
    actual = set(record)
    if actual != expected:
        raise EvidenceError(
            f"{path}: {label} keys differ: "
            f"missing={sorted(expected - actual)!r} extra={sorted(actual - expected)!r}"
        )


def require_guard_nat(path: Path, value: Any, *, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise EvidenceError(f"{path}: {label} must be a nonnegative integer")
    return value


def require_guard_bool(path: Path, value: Any, *, label: str) -> bool:
    if not isinstance(value, bool):
        raise EvidenceError(f"{path}: {label} must be a boolean")
    return value


def require_guard_fnv(path: Path, value: Any, *, label: str) -> str:
    if not isinstance(value, str) or re.fullmatch(r"fnv1a64:[0-9a-f]{16}", value) is None:
        raise EvidenceError(f"{path}: {label} is not a canonical FNV-1a root")
    return value


def require_guard_name_list(path: Path, value: Any, *, label: str) -> list[str]:
    if (
        not isinstance(value, list)
        or any(
            not isinstance(name, str)
            or re.fullmatch(r"[A-Z_][A-Z0-9_]*", name) is None
            for name in value
        )
        or value != sorted(set(value))
    ):
        raise EvidenceError(f"{path}: {label} must be a sorted unique environment-name list")
    return value


def validate_guard(
    path: Path,
    expected_exit: int,
    expected_verdict: str,
    expected_findings: Sequence[str],
    expected_root: str,
    observed_exit: int,
) -> dict[str, Any]:
    path = lexical_absolute(path)
    records, digest = load_ndjson_snapshot(path)
    for index, record in enumerate(records):
        if record.get("schema") != "structure-guard/3":
            raise EvidenceError(f"{path}:{index + 1}: wrong schema")
    if records[0].get("event") != "run_start":
        raise EvidenceError(f"{path}: first record is not run_start")
    start = records[0]
    require_guard_keys(
        path,
        start,
        {
            "schema",
            "event",
            "root",
            "root_identity",
            "graph_digest",
            "crates",
            "edges",
            "authority_inventory",
            "effective_compiler_identity",
            "admitted_environment",
        },
        label="run_start",
    )
    if records[0].get("root") != expected_root:
        raise EvidenceError(f"{path}: guard root does not match the invoked fixture")
    if expected_verdict not in {"pass", "fail", "inconclusive", "setup_error"}:
        raise EvidenceError(f"{path}: unsupported expected guard verdict")
    if observed_exit != expected_exit:
        raise EvidenceError(
            f"{path}: observed exit {observed_exit}, expected {expected_exit}"
        )
    terminals = [record for record in records if record.get("event") == "run_end"]
    if len(terminals) != 1 or records[-1] is not terminals[0]:
        raise EvidenceError(f"{path}: expected exactly one final run_end")
    terminal = terminals[0]
    terminal_keys = {
        "schema",
        "event",
        "verdict",
        "exit_code",
        "findings",
        "authority",
        "contract_handoff_root",
        "traversal",
        "authority_count_rule",
        "authority_count_rule_holds",
        "governed_root_before",
        "governed_root_after",
        "governed_root_unchanged",
        "duration_ms",
    }
    if expected_verdict == "setup_error":
        terminal_keys.update({"reason_code", "detail"})
    require_guard_keys(path, terminal, terminal_keys, label="run_end")
    if terminal.get("verdict") != expected_verdict:
        raise EvidenceError(
            f"{path}: verdict {terminal.get('verdict')!r}, expected {expected_verdict!r}"
        )
    if terminal.get("exit_code") != expected_exit:
        raise EvidenceError(
            f"{path}: terminal exit {terminal.get('exit_code')!r}, expected {expected_exit}"
        )
    require_guard_nat(path, terminal.get("duration_ms"), label="duration_ms")
    if expected_verdict in {"pass", "fail", "inconclusive"}:
        require_guard_fnv(path, start.get("graph_digest"), label="graph_digest")
        crate_count = require_guard_nat(path, start.get("crates"), label="crates")
        require_guard_nat(path, start.get("edges"), label="edges")
        expected_identity = str(Path(expected_root).resolve(strict=True))
        if start.get("root_identity") != expected_identity:
            raise EvidenceError(
                f"{path}: canonical root identity {start.get('root_identity')!r} "
                f"does not match {expected_identity!r}"
            )

        inventory = start.get("authority_inventory")
        if not isinstance(inventory, dict):
            raise EvidenceError(f"{path}: authority inventory is missing")
        require_guard_keys(
            path,
            inventory,
            {
                "package_class",
                "packages",
                "target_class",
                "targets",
                "feature_class",
                "features",
                "target_triple_class",
                "target_triples",
            },
            label="authority_inventory",
        )
        expected_classes = {
            "package_class": "workspace-graph-exact",
            "target_class": "cargo-auto-discovery-closed",
            "feature_class": "manifest-enumerated",
            "target_triple_class": "suite-lock-declared",
        }
        for key, expected_class in expected_classes.items():
            if inventory.get(key) != expected_class:
                raise EvidenceError(f"{path}: {key} is not {expected_class!r}")
        if require_guard_nat(path, inventory.get("packages"), label="packages") != crate_count:
            raise EvidenceError(f"{path}: package inventory disagrees with crate count")
        target_count = require_guard_nat(path, inventory.get("targets"), label="targets")
        require_guard_nat(path, inventory.get("features"), label="features")
        target_triples = require_guard_nat(
            path, inventory.get("target_triples"), label="target_triples"
        )
        if expected_verdict == "pass" and (
            target_count < crate_count or target_triples == 0
        ):
            raise EvidenceError(f"{path}: passing authority inventory is not closed")

        contract_handoff_root = terminal.get("contract_handoff_root")
        if contract_handoff_root is None:
            if expected_verdict == "pass":
                raise EvidenceError(
                    f"{path}: passing guard lacks a contract handoff root"
                )
        else:
            require_guard_fnv(
                path,
                contract_handoff_root,
                label="contract_handoff_root",
            )

        compiler = start.get("effective_compiler_identity")
        if not isinstance(compiler, dict):
            raise EvidenceError(f"{path}: effective compiler identity is missing")
        require_guard_keys(
            path,
            compiler,
            {
                "source",
                "channel",
                "release",
                "commit",
                "host",
                "contract_declared",
                "configuration_match",
                "contract_match",
            },
            label="effective_compiler_identity",
        )
        if compiler.get("source") not in {"PATH", "RUSTC"}:
            raise EvidenceError(f"{path}: compiler identity source is unsupported")
        if (
            (
                compiler.get("channel") is not None
                and (
                    not isinstance(compiler.get("channel"), str)
                    or not compiler["channel"].startswith("nightly-")
                )
            )
            or not isinstance(compiler.get("release"), str)
            or re.fullmatch(r"[0-9a-f]{40}", str(compiler.get("commit"))) is None
            or not isinstance(compiler.get("host"), str)
        ):
            raise EvidenceError(f"{path}: effective compiler identity is malformed")
        compiler_contract_declared = require_guard_bool(
            path,
            compiler.get("contract_declared"),
            label="compiler contract_declared",
        )
        compiler_configuration_match = require_guard_bool(
            path,
            compiler.get("configuration_match"),
            label="compiler configuration_match",
        )
        compiler_contract_match = require_guard_bool(
            path, compiler.get("contract_match"), label="compiler contract_match"
        )
        if expected_verdict == "pass" and (
            compiler.get("channel") is None
            or not compiler_contract_declared
            or not compiler_configuration_match
            or not compiler_contract_match
        ):
            raise EvidenceError(f"{path}: passing compiler authority is not established")

        environment = start.get("admitted_environment")
        if not isinstance(environment, dict):
            raise EvidenceError(f"{path}: admitted environment is missing")
        require_guard_keys(
            path,
            environment,
            {"policy", "admitted_names", "compiler_override_names"},
            label="admitted_environment",
        )
        if environment.get("policy") != "names-only-no-values/1":
            raise EvidenceError(f"{path}: admitted environment policy is unsupported")
        require_guard_name_list(
            path, environment.get("admitted_names"), label="admitted_names"
        )
        require_guard_name_list(
            path,
            environment.get("compiler_override_names"),
            label="compiler_override_names",
        )

        traversal = terminal.get("traversal")
        if not isinstance(traversal, dict):
            raise EvidenceError(f"{path}: traversal facts are missing")
        require_guard_keys(
            path,
            traversal,
            {
                "directories_visited",
                "files_discovered",
                "files_scanned",
                "files_skipped_unreadable",
            },
            label="traversal",
        )
        require_guard_nat(
            path, traversal.get("directories_visited"), label="directories_visited"
        )
        discovered = require_guard_nat(
            path, traversal.get("files_discovered"), label="files_discovered"
        )
        scanned = require_guard_nat(path, traversal.get("files_scanned"), label="files_scanned")
        skipped = require_guard_nat(
            path,
            traversal.get("files_skipped_unreadable"),
            label="files_skipped_unreadable",
        )
        if scanned + skipped != discovered:
            raise EvidenceError(f"{path}: authority count conservation failed")
        authority_count_rule_holds = require_guard_bool(
            path,
            terminal.get("authority_count_rule_holds"),
            label="authority_count_rule_holds",
        )
        if (
            terminal.get("authority_count_rule")
            != "files_scanned+files_skipped_unreadable=files_discovered"
            or not authority_count_rule_holds
        ):
            raise EvidenceError(f"{path}: authority count rule is not established")
        root_before = require_guard_fnv(
            path, terminal.get("governed_root_before"), label="governed_root_before"
        )
        root_after = require_guard_fnv(
            path, terminal.get("governed_root_after"), label="governed_root_after"
        )
        governed_unchanged = require_guard_bool(
            path,
            terminal.get("governed_root_unchanged"),
            label="governed_root_unchanged",
        )
        if governed_unchanged != (root_before == root_after):
            raise EvidenceError(f"{path}: governed-root equality fact disagrees")
        expected_authority = (
            "incomplete" if expected_verdict == "inconclusive" else "complete"
        )
        if terminal.get("authority") != expected_authority:  # ubs:ignore — public verdict enum
            raise EvidenceError(
                f"{path}: authority {terminal.get('authority')!r}, "
                f"expected {expected_authority!r}"
            )
        if expected_authority == "complete" and (  # ubs:ignore — public verdict enum
            (
                compiler_contract_declared
                and (not compiler_configuration_match or not compiler_contract_match)
            )
            or not governed_unchanged
        ):
            raise EvidenceError(f"{path}: complete authority lacks identity closure")
    elif records[0].get("graph_digest") is not None:
        raise EvidenceError(f"{path}: setup failure claims a graph digest")
    else:
        if any(
            start.get(key) is not None
            for key in (
                "root_identity",
                "crates",
                "edges",
                "authority_inventory",
                "effective_compiler_identity",
                "admitted_environment",
            )
        ):
            raise EvidenceError(f"{path}: setup failure claims structural authority")
        if (
            terminal.get("authority") != "not_established"
            or terminal.get("contract_handoff_root") is not None
            or terminal.get("traversal") is not None
            or terminal.get("governed_root_before") is not None
            or terminal.get("governed_root_after") is not None
        ):
            raise EvidenceError(f"{path}: setup failure claims established authority")
        if require_guard_bool(
            path,
            terminal.get("authority_count_rule_holds"),
            label="setup authority_count_rule_holds",
        ) or require_guard_bool(
            path,
            terminal.get("governed_root_unchanged"),
            label="setup governed_root_unchanged",
        ):
            raise EvidenceError(f"{path}: setup failure claims established authority")
    actual_findings = []
    finding_records = records[1:-1]
    for index, record in enumerate(finding_records, 2):
        require_guard_keys(
            path,
            record,
            {"schema", "event", "code", "severity", "path", "detail"},
            label=f"finding line {index}",
        )
        if record.get("event") != "finding":
            raise EvidenceError(f"{path}:{index}: non-finding inside guard run")
        if record.get("severity") != "error":
            raise EvidenceError(f"{path}:{index}: guard finding severity is not error")
        if not isinstance(record.get("code"), str) or not isinstance(
            record.get("path"), str
        ):
            raise EvidenceError(f"{path}:{index}: malformed guard finding identity")
        if not isinstance(record.get("detail"), str) or not record["detail"]:
            raise EvidenceError(f"{path}:{index}: guard finding lacks detail")
        raw_path = str(record.get("path"))
        # Current structure-guard findings carry a source line in the path string.
        # Scenario contracts intentionally match code + canonical file path; span
        # accuracy is a separate claim and must not make fixtures line-number brittle.
        canonical_path = re.sub(r":\d+(?::\d+)?$", "", raw_path)
        actual_findings.append(f"{record.get('code')}@{canonical_path}")
    canonical_order = sorted(
        finding_records,
        key=lambda record: (
            str(record.get("code")),
            str(record.get("path")),
            str(record.get("detail")),
        ),
    )
    if finding_records != canonical_order:
        raise EvidenceError(f"{path}: guard findings are not deterministically sorted")
    if actual_findings != list(expected_findings):
        raise EvidenceError(
            f"{path}: exact findings {actual_findings!r}, expected {list(expected_findings)!r}"
        )
    if terminal.get("findings") != len(actual_findings):
        raise EvidenceError(f"{path}: terminal finding count disagrees with records")
    if terminal.get("exit_code") != observed_exit:
        raise EvidenceError(f"{path}: reported and observed exits disagree")
    return {
        "schema": "fln.validation/1",
        "subject": path.name,
        "valid": True,
        "exit_code": expected_exit,
        "verdict": expected_verdict,
        "findings": actual_findings,
        "sha256": digest,
    }


class VerdictWireReader:
    """Small independent reader for the frozen Verdict v1 evidence fixtures."""

    def __init__(self, data: bytes, *, subject: str) -> None:
        self.data = data
        self.subject = subject
        self.at = 0

    def take(self, amount: int) -> bytes:
        end = self.at + amount
        if amount < 0 or end > len(self.data):
            raise EvidenceError(
                f"{self.subject}: truncated Verdict wire value at byte {self.at}"
            )
        value = self.data[self.at : end]
        self.at = end
        return value

    def u8(self) -> int:
        return self.take(1)[0]

    def u16(self) -> int:
        return int.from_bytes(self.take(2), "little")

    def u32(self) -> int:
        return int.from_bytes(self.take(4), "little")

    def u64(self) -> int:
        return int.from_bytes(self.take(8), "little")

    def header(self, expected_kind: int) -> None:
        if self.take(len(VERDICT_WIRE_MAGIC)) != VERDICT_WIRE_MAGIC:
            raise EvidenceError(f"{self.subject}: invalid Verdict wire magic")
        kind = self.u8()
        version = self.u16()
        extensions = self.u16()
        if kind != expected_kind:
            raise EvidenceError(
                f"{self.subject}: Verdict kind {kind}, expected {expected_kind}"
            )
        if version != VERDICT_SCHEMA_VERSION or extensions != 0:
            raise EvidenceError(
                f"{self.subject}: Verdict version/extensions are not frozen v1/0"
            )

    def finish(self) -> None:
        if self.at != len(self.data):
            raise EvidenceError(
                f"{self.subject}: {len(self.data) - self.at} trailing Verdict bytes"
            )


def verdict_decode_hex(value: Any, *, label: str) -> bytes:
    if (
        not isinstance(value, str)
        or not value
        or len(value) % 2 != 0
        or re.fullmatch(r"[0-9a-f]+", value) is None
    ):
        raise EvidenceError(f"Verdict {label} is not canonical lowercase hex")
    if len(value) // 2 > VERDICT_MAX_ENCODED_BYTES:
        raise EvidenceError(f"Verdict {label} exceeds the encoded-byte bound")
    return bytes.fromhex(value)


def verdict_read_clause(reader: VerdictWireReader) -> list[int]:
    count = reader.u64()
    if count > 64:
        raise EvidenceError(f"{reader.subject}: fixture literal count is unbounded")
    literals: list[int] = []
    identities: set[int] = set()
    for _ in range(count):
        variable = reader.u32()
        polarity = reader.u8()
        if variable == 0 or polarity not in {0, 1}:
            raise EvidenceError(f"{reader.subject}: malformed Verdict literal")
        if variable in identities:
            raise EvidenceError(
                f"{reader.subject}: duplicate or tautological Verdict variable"
            )
        identities.add(variable)
        literals.append(variable if polarity == 1 else -variable)
    if literals != sorted(literals, key=lambda literal: (abs(literal), literal > 0)):
        raise EvidenceError(f"{reader.subject}: Verdict literals are not canonical")
    return literals


def verdict_parse_cnf(data: bytes, *, subject: str) -> dict[str, Any]:
    reader = VerdictWireReader(data, subject=subject)
    reader.header(1)
    variable_count = reader.u32()
    count = reader.u64()
    if variable_count > 64 or count > 64:
        raise EvidenceError(f"{subject}: Verdict CNF fixture exceeds validator bounds")
    clauses: list[dict[str, Any]] = []
    previous_id = 0
    for _ in range(count):
        clause_id = reader.u64()
        if clause_id <= previous_id:
            raise EvidenceError(f"{subject}: Verdict clause ids are not canonical")
        previous_id = clause_id
        literals = verdict_read_clause(reader)
        if any(abs(literal) > variable_count for literal in literals):
            raise EvidenceError(f"{subject}: Verdict literal exceeds variable count")
        clauses.append({"id": clause_id, "literals": literals})
    reader.finish()
    return {"variable_count": variable_count, "clauses": clauses}


def verdict_parse_model(data: bytes, *, subject: str) -> dict[str, Any]:
    reader = VerdictWireReader(data, subject=subject)
    reader.header(2)
    variable_count = reader.u32()
    count = reader.u64()
    if variable_count > 64 or count > 64:
        raise EvidenceError(f"{subject}: Verdict model fixture exceeds validator bounds")
    assignments: list[tuple[int, bool]] = []
    previous_variable = 0
    for _ in range(count):
        variable = reader.u32()
        raw_value = reader.u8()
        if variable <= previous_variable or raw_value not in {0, 1}:
            raise EvidenceError(f"{subject}: Verdict assignments are not canonical")
        previous_variable = variable
        assignments.append((variable, raw_value == 1))
    reader.finish()
    if [variable for variable, _value in assignments] != list(
        range(1, variable_count + 1)
    ):
        raise EvidenceError(f"{subject}: Verdict model is not complete")
    return {"variable_count": variable_count, "assignments": assignments}


def verdict_parse_proof(data: bytes, *, subject: str) -> dict[str, Any]:
    reader = VerdictWireReader(data, subject=subject)
    reader.header(3)
    count = reader.u64()
    if count > 64:
        raise EvidenceError(f"{subject}: Verdict proof fixture exceeds validator bounds")
    steps: list[dict[str, Any]] = []
    for _ in range(count):
        opcode_at = reader.at
        opcode = reader.u8()
        if opcode == 1:
            clause_id = reader.u64()
            clause = verdict_read_clause(reader)
            rule_opcode = reader.u8()
            if rule_opcode == 1:
                rule = {
                    "kind": "resolution",
                    "pivot": reader.u32(),
                    "positive_parent": reader.u64(),
                    "negative_parent": reader.u64(),
                }
            elif rule_opcode == 2:
                dependencies = reader.u64()
                if dependencies > 64:
                    raise EvidenceError(
                        f"{subject}: Verdict proof dependency count is unbounded"
                    )
                antecedents = [reader.u64() for _ in range(dependencies)]
                if antecedents != sorted(set(antecedents)):
                    raise EvidenceError(
                        f"{subject}: Verdict proof dependencies are not canonical"
                    )
                rule = {"kind": "rup", "antecedents": antecedents}
            else:
                raise EvidenceError(
                    f"{subject}: unknown Verdict proof rule opcode {rule_opcode}"
                )
            steps.append(
                {"kind": "derive", "id": clause_id, "clause": clause, "rule": rule}
            )
        elif opcode == 2:
            deletion_count = reader.u64()
            if deletion_count > 64:
                raise EvidenceError(
                    f"{subject}: Verdict deletion count is unbounded"
                )
            clauses = [reader.u64() for _ in range(deletion_count)]
            if not clauses or clauses != sorted(set(clauses)):
                raise EvidenceError(
                    f"{subject}: Verdict deletion targets are not canonical"
                )
            steps.append({"kind": "delete", "clauses": clauses})
        elif opcode == 3:
            steps.append({"kind": "conclude", "empty_clause": reader.u64()})
        else:
            raise EvidenceError(
                f"{subject}: unknown Verdict proof opcode {opcode} at byte {opcode_at}"
            )
    reader.finish()
    return {"steps": steps}


def verdict_read_canonical_record(
    path: Path, *, label: str, max_bytes: int
) -> tuple[dict[str, Any], str]:
    data, _size, digest = stable_file_facts(path, max_bytes=max_bytes)
    record = parse_json(data, subject=label)
    if not isinstance(record, dict):
        raise EvidenceError(f"{label}: expected one JSON object")
    if canonical_json(record) != data:
        raise EvidenceError(f"{label}: record is not canonical single-row NDJSON")
    return record, digest


def verdict_exact_integer(record: Mapping[str, Any], key: str) -> int:
    value = record.get(key)
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise EvidenceError(f"Verdict {key} is not a non-negative integer")
    return value


def validate_verdict_schema_evidence(
    semantic_path: Path,
    telemetry_path: Path,
    stdout_path: Path,
    stderr_path: Path,
    phase: str,
    observed_exit: int,
    *,
    positive_semantic_path: Path | None,
) -> dict[str, Any]:
    semantic, semantic_digest = verdict_read_canonical_record(
        semantic_path,
        label=f"Verdict {phase} semantic evidence",
        max_bytes=VERDICT_MAX_SEMANTIC_BYTES,
    )
    telemetry, telemetry_digest = verdict_read_canonical_record(
        telemetry_path,
        label=f"Verdict {phase} telemetry",
        max_bytes=VERDICT_MAX_TELEMETRY_BYTES,
    )
    stdout, _stdout_size, stdout_digest = stable_file_facts(
        stdout_path, max_bytes=MAX_LOG_BYTES
    )
    stderr, _stderr_size, stderr_digest = stable_file_facts(
        stderr_path, max_bytes=MAX_LOG_BYTES
    )
    stdout_text = stdout.decode("utf-8", errors="strict")
    stderr_text = stderr.decode("utf-8", errors="strict")

    common_semantic = {
        "data_grade": "verified",
        "schema": VERDICT_SEMANTIC_SCHEMA,
        "version": VERDICT_SCHEMA_VERSION,
    }
    for key, expected in common_semantic.items():
        if semantic.get(key) != expected:
            raise EvidenceError(
                f"Verdict {phase} semantic {key} {semantic.get(key)!r}, "
                f"expected {expected!r}"
            )
    forbidden_semantic_fragments = (
        "duration",
        "host",
        "monotonic",
        "path",
        "pid",
        "time",
        "worker",
    )
    if any(
        fragment in key
        for key in semantic
        for fragment in forbidden_semantic_fragments
    ):
        raise EvidenceError(
            f"Verdict {phase} semantic row contains telemetry or host identity"
        )

    expected_telemetry_fields = {
        "event",
        "max_encoded_bytes",
        "max_workers",
        "observed_encoded_bytes",
        "schema",
        "timing_used_as_gate",
        "version",
        "workers_spawned",
    }
    if set(telemetry) != expected_telemetry_fields:
        raise EvidenceError(
            f"Verdict {phase} telemetry fields differ from the frozen schema"
        )
    if (
        telemetry.get("schema") != VERDICT_TELEMETRY_SCHEMA
        or telemetry.get("version") != VERDICT_SCHEMA_VERSION
        or telemetry.get("event") != "phase_resources"
        or telemetry.get("timing_used_as_gate") is not False
    ):
        raise EvidenceError(f"Verdict {phase} telemetry identity is malformed")
    maximum_bytes = verdict_exact_integer(telemetry, "max_encoded_bytes")
    maximum_workers = verdict_exact_integer(telemetry, "max_workers")
    observed_bytes = verdict_exact_integer(telemetry, "observed_encoded_bytes")
    workers_spawned = verdict_exact_integer(telemetry, "workers_spawned")
    if (
        maximum_bytes != VERDICT_MAX_ENCODED_BYTES
        or observed_bytes > maximum_bytes
        or maximum_workers != VERDICT_MAX_WORKERS
        or workers_spawned > maximum_workers
    ):
        raise EvidenceError(f"Verdict {phase} telemetry exceeded or changed its bounds")

    expected_sat_cnf = {
        "variable_count": 3,
        "clauses": [
            {"id": 1, "literals": [1, -2]},
            {"id": 2, "literals": [2]},
            {"id": 3, "literals": [-1, 3]},
        ],
    }
    expected_unsat_cnf = {
        "variable_count": 1,
        "clauses": [
            {"id": 1, "literals": [1]},
            {"id": 2, "literals": [-1]},
        ],
    }
    expected_model = {
        "variable_count": 3,
        "assignments": [(1, True), (2, True), (3, True)],
    }
    expected_proof = {
        "steps": [
            {
                "kind": "derive",
                "id": 3,
                "clause": [],
                "rule": {
                    "kind": "resolution",
                    "pivot": 1,
                    "positive_parent": 1,
                    "negative_parent": 2,
                },
            },
            {"kind": "conclude", "empty_clause": 3},
        ]
    }

    if phase == "positive":
        expected_fields = {
            "cnf_hex",
            "data_grade",
            "event",
            "model_hex",
            "model_satisfies",
            "proof_hex",
            "schema",
            "status",
            "thread_cnf_hex",
            "threads",
            "unsat_cnf_hex",
            "version",
        }
        if set(semantic) != expected_fields:
            raise EvidenceError("Verdict positive semantic fields differ from v1")
        if semantic.get("event") != "positive" or semantic.get("status") != "pass":
            raise EvidenceError("Verdict positive semantic verdict is not pass")
        cnf_bytes = verdict_decode_hex(semantic.get("cnf_hex"), label="CNF")
        model_bytes = verdict_decode_hex(semantic.get("model_hex"), label="model")
        unsat_bytes = verdict_decode_hex(
            semantic.get("unsat_cnf_hex"), label="UNSAT CNF"
        )
        proof_bytes = verdict_decode_hex(semantic.get("proof_hex"), label="proof")
        if verdict_parse_cnf(cnf_bytes, subject="positive CNF") != expected_sat_cnf:
            raise EvidenceError("Verdict positive CNF semantic fixture differs")
        parsed_model = verdict_parse_model(model_bytes, subject="positive model")
        if parsed_model != expected_model:
            raise EvidenceError("Verdict positive model semantic fixture differs")
        if verdict_parse_cnf(
            unsat_bytes, subject="positive UNSAT CNF"
        ) != expected_unsat_cnf:
            raise EvidenceError("Verdict positive UNSAT CNF semantic fixture differs")
        if verdict_parse_proof(
            proof_bytes, subject="positive proof"
        ) != expected_proof:
            raise EvidenceError("Verdict positive proof semantic fixture differs")
        assignment = dict(parsed_model["assignments"])
        independently_satisfies = all(
            any(
                (assignment[abs(literal)] and literal > 0)
                or (not assignment[abs(literal)] and literal < 0)
                for literal in clause["literals"]
            )
            for clause in expected_sat_cnf["clauses"]
        )
        if (
            semantic.get("model_satisfies") is not True
            or not independently_satisfies
            or semantic.get("threads") != [1, 8, 32]
            or semantic.get("thread_cnf_hex")
            != [semantic["cnf_hex"], semantic["cnf_hex"], semantic["cnf_hex"]]
        ):
            raise EvidenceError("Verdict positive semantic equivalence claim differs")
        expected_observed_bytes = sum(
            map(len, (cnf_bytes, model_bytes, unsat_bytes, proof_bytes))
        )
        if workers_spawned != 41:
            raise EvidenceError("Verdict positive worker count is not 1+8+32")
    elif phase == "failure":
        expected_fields = {
            "corrupted_proof_hex",
            "data_grade",
            "error_at",
            "error_code",
            "event",
            "opcode",
            "partial_artifact_published",
            "schema",
            "status",
            "version",
        }
        if set(semantic) != expected_fields:
            raise EvidenceError("Verdict failure semantic fields differ from v1")
        corrupted = verdict_decode_hex(
            semantic.get("corrupted_proof_hex"), label="corrupted proof"
        )
        reader = VerdictWireReader(corrupted, subject="failure proof")
        reader.header(3)
        if reader.u64() != 2:
            raise EvidenceError("Verdict failure proof changed its step count")
        opcode_at = reader.at
        opcode = reader.u8()
        if (
            semantic.get("event") != "failure"
            or semantic.get("status") != "refused"
            or semantic.get("error_code") != "unknown_opcode"
            or semantic.get("error_at") != opcode_at
            or semantic.get("opcode") != opcode
            or opcode_at != VERDICT_WIRE_HEADER_BYTES + 8
            or opcode != 255
            or semantic.get("partial_artifact_published") is not False
        ):
            raise EvidenceError("Verdict failure refusal is not the intended opcode")
        if stdout_text.count(VERDICT_FAILURE_MARKER) != 1:
            raise EvidenceError("Verdict failure stdout lacks the exact mutant marker")
        if stderr_text.count(VERDICT_FAILURE_MARKER) != 1:
            raise EvidenceError("Verdict failure stderr lacks the exact mutant marker")
        expected_observed_bytes = len(corrupted)
        if workers_spawned != 0:
            raise EvidenceError("Verdict failure unexpectedly spawned encoder workers")
    elif phase == "recovery":
        expected_fields = {
            "cnf_hex",
            "data_grade",
            "event",
            "proof_hex",
            "recovered_after",
            "schema",
            "status",
            "version",
        }
        if set(semantic) != expected_fields:
            raise EvidenceError("Verdict recovery semantic fields differ from v1")
        if (
            semantic.get("event") != "recovery"
            or semantic.get("status") != "pass"
            or semantic.get("recovered_after") != "unknown_opcode"
        ):
            raise EvidenceError("Verdict recovery semantic verdict is malformed")
        cnf_bytes = verdict_decode_hex(semantic.get("cnf_hex"), label="recovery CNF")
        proof_bytes = verdict_decode_hex(
            semantic.get("proof_hex"), label="recovery proof"
        )
        if verdict_parse_cnf(cnf_bytes, subject="recovery CNF") != expected_sat_cnf:
            raise EvidenceError("Verdict recovery CNF differs")
        if verdict_parse_proof(
            proof_bytes, subject="recovery proof"
        ) != expected_proof:
            raise EvidenceError("Verdict recovery proof differs")
        if positive_semantic_path is None:
            raise EvidenceError("Verdict recovery lacks positive semantic baseline")
        positive, _positive_digest = verdict_read_canonical_record(
            positive_semantic_path,
            label="Verdict recovery positive baseline",
            max_bytes=VERDICT_MAX_SEMANTIC_BYTES,
        )
        if (
            positive.get("event") != "positive"
            or semantic.get("cnf_hex") != positive.get("cnf_hex")
            or semantic.get("proof_hex") != positive.get("proof_hex")
        ):
            raise EvidenceError("Verdict recovery bytes differ from positive baseline")
        expected_observed_bytes = len(cnf_bytes) + len(proof_bytes)
        if workers_spawned != 0:
            raise EvidenceError("Verdict recovery unexpectedly spawned encoder workers")
    else:
        raise EvidenceError(f"unknown Verdict evidence phase {phase!r}")

    expected_exit = 101 if phase == "failure" else 0
    if observed_exit != expected_exit:
        raise EvidenceError(
            f"Verdict {phase} child exit {observed_exit}, expected {expected_exit}"
        )
    if observed_bytes != expected_observed_bytes:
        raise EvidenceError(
            f"Verdict {phase} telemetry byte count disagrees with semantic bytes"
        )
    if phase == "failure":
        if "test result: FAILED. 0 passed; 1 failed;" not in stdout_text:
            raise EvidenceError("Verdict failure stdout lacks the one-test summary")
        if "test result: ok. 1 passed; 0 failed;" in stdout_text + stderr_text:
            raise EvidenceError("Verdict failure streams contain a passing summary")
    elif "test result: ok. 1 passed; 0 failed;" not in stdout_text:
        raise EvidenceError(f"Verdict {phase} stdout lacks the one-test pass summary")

    return {
        "phase": phase,
        "schema": "fln.validation/1",
        "semantic_sha256": semantic_digest,
        "stderr_sha256": stderr_digest,
        "stdout_sha256": stdout_digest,
        "telemetry_sha256": telemetry_digest,
        "valid": True,
        "validator": "verdict-schema/1",
    }


def environment_collision_insertion_order(
    cardinality: int, partitions: int, rotation: int
) -> list[int]:
    rows: list[list[int]] = []
    for partition in range(partitions):
        row = list(range(partition, cardinality, partitions))
        if partition % 2 == 0:
            row.reverse()
        rows.append(row)
    offset = rotation % partitions
    rows = rows[offset:] + rows[:offset]
    return [component for row in rows for component in row]


def read_environment_collision_stream(
    path: Path, artifact_root: Path, *, label: str
) -> tuple[Path, bytes, str, str, str]:
    root = lexical_absolute(artifact_root)
    absolute = require_within(path, root, label=f"environment-collision {label}")
    data, _size, digest = stable_file_facts(absolute, max_bytes=MAX_LOG_BYTES)
    if data and not data.endswith(b"\n"):
        raise EvidenceError(
            f"environment-collision {label} is unterminated: {absolute}"
        )
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        raise EvidenceError(
            f"environment-collision {label} is not UTF-8: {absolute}"
        ) from error
    for number, raw_line in enumerate(data.splitlines(), 1):
        if len(raw_line) > MAX_RECORD_BYTES:
            raise EvidenceError(
                f"{absolute}:{number}: environment-collision {label} line is too large"
            )
    relative = absolute.relative_to(root).as_posix()
    return absolute, data, text, digest, relative


def environment_collision_failure_material(text: str) -> bool:
    failed_forms = {
        f"{ENVIRONMENT_COLLISION_TEST} --- FAILED",
        f"test {ENVIRONMENT_COLLISION_TEST} ... FAILED",
    }
    for line in text.splitlines():
        stripped = line.strip()
        if (
            stripped in failed_forms
            or stripped.startswith("test result: FAILED.")
            or stripped.startswith("thread '")
            and " panicked at " in stripped
            or re.fullmatch(r"assertion .* failed(?:: .*)?", stripped) is not None
            or stripped.startswith("error: test failed")
        ):
            return True
    return False


def validate_environment_collision(
    stdout_path: Path,
    stderr_path: Path,
    phase: str,
    expected_run_id: str,
    observed_exit: int,
    *,
    artifact_root: Path,
    expected_stdout_artifact: str,
    expected_stderr_artifact: str,
    expected_cwd: str | None = None,
    expected_argv: str | None = None,
    expected_cache_state: str | None = None,
) -> dict[str, Any]:
    if phase not in {"positive", "mutant", "recovery"}:
        raise EvidenceError(f"unsupported environment-collision phase: {phase!r}")
    if not re.fullmatch(r"[A-Za-z0-9_-]+", expected_run_id):
        raise EvidenceError("environment-collision run id is malformed")
    if not isinstance(observed_exit, int) or isinstance(observed_exit, bool):
        raise EvidenceError("environment-collision observed exit is not an integer")
    expected_exit = 101 if phase == "mutant" else 0
    if observed_exit != expected_exit:
        raise EvidenceError(
            f"environment-collision {phase} exit {observed_exit}, expected {expected_exit}"
        )

    root = lexical_absolute(artifact_root)
    stdout_path, stdout_data, stdout_text, stdout_digest, stdout_relative = (
        read_environment_collision_stream(stdout_path, root, label="stdout")
    )
    stderr_path, stderr_data, stderr_text, stderr_digest, stderr_relative = (
        read_environment_collision_stream(stderr_path, root, label="stderr")
    )
    if stdout_path == stderr_path:
        raise EvidenceError("environment-collision stdout and stderr are not distinct")
    for label, expected, actual in (
        ("stdout", expected_stdout_artifact, stdout_relative),
        ("stderr", expected_stderr_artifact, stderr_relative),
    ):
        expected_path = Path(expected)
        if (
            not expected
            or expected_path.is_absolute()
            or ".." in expected_path.parts
            or expected in {"."}
            or expected_path.as_posix() != expected
        ):
            raise EvidenceError(
                f"environment-collision expected {label} artifact is not a canonical relative path"
            )
        if expected != actual:
            raise EvidenceError(
                f"environment-collision {label} path {actual!r}, expected {expected!r}"
            )

    records: list[dict[str, Any]] = []
    schema_marker = ENVIRONMENT_COLLISION_SCHEMA.encode("ascii")
    if schema_marker in stderr_data:
        raise EvidenceError("environment-collision detail rows leaked into stderr")
    for number, raw_line in enumerate(stdout_data.splitlines(), 1):
        if schema_marker not in raw_line:
            continue
        object_start = raw_line.find(b"{")
        if object_start < 0:
            raise EvidenceError(
                f"{stdout_path}:{number}: collision evidence is not a JSON object"
            )
        value = parse_json(
            raw_line[object_start:].strip(), subject=f"{stdout_path}:{number}"
        )
        if not isinstance(value, dict):
            raise EvidenceError(
                f"{stdout_path}:{number}: collision evidence is not an object"
            )
        records.append(value)

    if phase == "mutant":
        if records:
            raise EvidenceError("killed collision mutant emitted passing detail records")
        failed_forms = {
            f"{ENVIRONMENT_COLLISION_TEST} --- FAILED",
            f"test {ENVIRONMENT_COLLISION_TEST} ... FAILED",
        }
        failed_lines = [
            line.strip()
            for line in stdout_text.splitlines()
            if line.strip() in failed_forms
        ]
        if len(failed_lines) != 1:
            raise EvidenceError(
                "collision mutant stdout lacks exactly one named FAILED test result"
            )
        if any(line.strip() in failed_forms for line in stderr_text.splitlines()):
            raise EvidenceError("collision mutant FAILED test result leaked into stderr")
        if ENVIRONMENT_COLLISION_MUTANT_MARKER in stdout_text:
            raise EvidenceError("collision mutant assertion marker leaked into stdout")
        marker_lines = [
            line.strip()
            for line in stderr_text.splitlines()
            if ENVIRONMENT_COLLISION_MUTANT_MARKER in line
        ]
        expected_marker_line = re.compile(
            r"assertion .* failed: collision enumeration diverged: threads=1"
        )
        if (
            stderr_text.count(ENVIRONMENT_COLLISION_MUTANT_MARKER) != 1
            or len(marker_lines) != 1
            or expected_marker_line.fullmatch(marker_lines[0]) is None
        ):
            raise EvidenceError(
                "collision mutant stderr lacks exactly one intended enumeration assertion marker"
            )
        result_lines = [
            line.strip()
            for line in stdout_text.splitlines()
            if line.strip().startswith("test result: FAILED.")
        ]
        if len(result_lines) != 1 or not re.match(
            r"^test result: FAILED\. 0 passed; 1 failed;", result_lines[0]
        ):
            raise EvidenceError(
                "collision mutant stdout lacks the exact one-test failure summary"
            )
        if any(
            line.strip().startswith("test result: FAILED.")
            for line in stderr_text.splitlines()
        ):
            raise EvidenceError("collision mutant failure summary leaked into stderr")
        if any(
            line.strip().startswith("test result: ok.")
            for line in (*stdout_text.splitlines(), *stderr_text.splitlines())
        ):
            raise EvidenceError("collision mutant streams contain a passing summary")
        return {
            "schema": "fln.validation/1",
            "validator": "environment-collision/1",
            "subject": stdout_relative,
            "valid": True,
            "phase": phase,
            "run_id": expected_run_id,
            "observed_exit": observed_exit,
            "records": 0,
            "failed_test": ENVIRONMENT_COLLISION_TEST,
            "assertion_marker": ENVIRONMENT_COLLISION_MUTANT_MARKER,
            "stdout_artifact": stdout_relative,
            "stderr_artifact": stderr_relative,
            "stdout_sha256": stdout_digest,
            "stderr_sha256": stderr_digest,
        }

    expected_identity = {
        "schema": ENVIRONMENT_COLLISION_SCHEMA,
        "bead": "fln-amv.10",
        "claim_id": "fln-amv.10-collision-canonicality",
        "claim_type": "bounded_model",
        "invariant_id": "FL-INV-01",
        "invariant_relation": "supports-local-pmap-slice",
        "gate_id": "PG-5",
        "gate_relation": "partial-component-evidence",
        "parity_ledger_row": "not_applicable_internal_data_structure_determinism",
        "data_grade": "verified",
        "epoch": "lean-v4.32.0",
        "mode": "sound",
        "profile": "e2e",
        "seed": "partition-rotation-v1",
        "scenario": "full-hash-collision-schedule-matrix",
        "status": "pass",
        "bucket_policy": "PKey-Ord",
        "lookup_complexity": "O(bucket)",
        "insert_complexity": "O(log(bucket))-comparisons-plus-O(bucket)-clone-shift",
        "resource_followup": "fln-amv.13",
        "cleanup_status": "retained_by_policy",
        "final_state": "canonical-enumeration-and-root-verified",
    }
    required_cli_values = {
        "expected cwd": expected_cwd,
        "expected argv": expected_argv,
        "expected cache state": expected_cache_state,
    }
    missing_cli = sorted(
        label for label, value in required_cli_values.items() if not isinstance(value, str) or not value
    )
    if missing_cli:
        raise EvidenceError(
            f"environment-collision {phase} validation lacks {missing_cli!r}"
        )
    if not Path(expected_cwd).is_absolute():
        raise EvidenceError("environment-collision expected cwd is not absolute")
    if len(records) != len(ENVIRONMENT_COLLISION_THREADS):
        raise EvidenceError(
            f"environment-collision {phase} emitted {len(records)} detail records, "
            f"expected {len(ENVIRONMENT_COLLISION_THREADS)}"
        )
    if environment_collision_failure_material(stdout_text):
        raise EvidenceError(
            f"environment-collision {phase} stdout contains failure material"
        )
    if environment_collision_failure_material(stderr_text):
        raise EvidenceError(
            f"environment-collision {phase} stderr contains failure material"
        )
    pass_result_lines = [
        line.strip()
        for line in stdout_text.splitlines()
        if line.strip().startswith("test result: ok.")
    ]
    if len(pass_result_lines) != 1 or not re.match(
        r"^test result: ok\. 1 passed; 0 failed;", pass_result_lines[0]
    ):
        raise EvidenceError(
            f"environment-collision {phase} log lacks the exact one-test pass summary"
        )

    def exact_integer(record: dict[str, Any], key: str, expected: int) -> None:
        value = record.get(key)
        if not isinstance(value, int) or isinstance(value, bool) or value != expected:
            raise EvidenceError(
                f"environment-collision {key} {value!r}, expected integer {expected}"
            )

    def integer_vector(value: Any, label: str) -> list[int]:
        if not isinstance(value, list) or any(
            not isinstance(item, int) or isinstance(item, bool) for item in value
        ):
            raise EvidenceError(f"environment-collision {label} is not an integer array")
        return value

    def integer_matrix(value: Any, label: str) -> list[list[int]]:
        if not isinstance(value, list):
            raise EvidenceError(f"environment-collision {label} is not an array")
        return [integer_vector(row, f"{label}[{index}]") for index, row in enumerate(value)]

    canonical_order = list(range(ENVIRONMENT_COLLISION_CARDINALITY))
    shared_input_root: str | None = None
    shared_collision_hash: str | None = None
    shared_environment_root: str | None = None
    shared_platform: str | None = None
    previous_end = -1
    for record, threads in zip(records, ENVIRONMENT_COLLISION_THREADS, strict=True):
        if set(record) != ENVIRONMENT_COLLISION_FIELDS:
            missing = sorted(ENVIRONMENT_COLLISION_FIELDS - set(record))
            extra = sorted(set(record) - ENVIRONMENT_COLLISION_FIELDS)
            raise EvidenceError(
                f"environment-collision v2 field mismatch: missing={missing!r} extra={extra!r}"
            )
        for key, expected in expected_identity.items():
            if record.get(key) != expected:
                raise EvidenceError(
                    f"environment-collision {key} {record.get(key)!r}, expected {expected!r}"
                )
        exact_integer(record, "version", ENVIRONMENT_COLLISION_VERSION)
        exact_integer(record, "collision_cardinality", ENVIRONMENT_COLLISION_CARDINALITY)
        exact_integer(record, "threads", threads)
        exact_integer(record, "workers_built", threads)
        exact_integer(record, "distinct_insertion_orders", threads)
        exact_integer(record, "enumeration_insert_operations", ENVIRONMENT_COLLISION_CARDINALITY * threads)
        exact_integer(record, "environment_insert_operations", ENVIRONMENT_COLLISION_CARDINALITY * threads)
        exact_integer(record, "environment_duplicate_checks", ENVIRONMENT_COLLISION_CARDINALITY * threads)
        exact_integer(record, "theoretical_fresh_node_bound_per_insert", 28)
        exact_integer(record, "theoretical_replaced_node_bound_per_insert", 14)
        exact_integer(record, "process_exit", 0)
        if record.get("run_id") != expected_run_id:
            raise EvidenceError("environment-collision detail run id mismatch")
        if record.get("cwd") != expected_cwd:
            raise EvidenceError("environment-collision detail cwd mismatch")
        if record.get("argv") != [expected_argv]:
            raise EvidenceError("environment-collision detail argv mismatch")
        if record.get("stdout_artifact") != expected_stdout_artifact or record.get(
            "stderr_artifact"
        ) != expected_stderr_artifact:
            raise EvidenceError("environment-collision detail artifact identity mismatch")
        if record.get("cache_state") != expected_cache_state:
            raise EvidenceError("environment-collision detail cache-state mismatch")
        platform_value = record.get("platform")
        if not isinstance(platform_value, str) or not platform_value or "-" not in platform_value:
            raise EvidenceError("environment-collision platform identity is malformed")
        if shared_platform is None:
            shared_platform = platform_value
        elif platform_value != shared_platform:
            raise EvidenceError("environment-collision platform changed across schedules")

        input_root = record.get("canonical_input_root")
        if not isinstance(input_root, str) or not re.fullmatch(
            r"fln-fixture:[0-9a-f]{64}", input_root
        ):
            raise EvidenceError("environment-collision canonical input root is malformed")
        if shared_input_root is None:
            shared_input_root = input_root
        elif input_root != shared_input_root:
            raise EvidenceError("environment-collision input root changed across schedules")
        collision_hash = record.get("collision_hash")
        if not isinstance(collision_hash, str) or not re.fullmatch(
            r"[0-9a-f]{16}", collision_hash
        ):
            raise EvidenceError("environment-collision hash is malformed")
        if shared_collision_hash is None:
            shared_collision_hash = collision_hash
        elif collision_hash != shared_collision_hash:
            raise EvidenceError("environment-collision hash changed across schedules")

        expected_worker_orders = [
            environment_collision_insertion_order(
                ENVIRONMENT_COLLISION_CARDINALITY, threads, worker
            )
            for worker in range(threads)
        ]
        worker_orders = integer_matrix(
            record.get("worker_insertion_orders"), "worker_insertion_orders"
        )
        if worker_orders != expected_worker_orders:
            raise EvidenceError(
                f"environment-collision worker insertion schedules differ for threads={threads}"
            )
        representative = integer_vector(
            record.get("representative_insertion_order"),
            "representative_insertion_order",
        )
        if representative != expected_worker_orders[0]:
            raise EvidenceError(
                f"environment-collision representative schedule differs for threads={threads}"
            )
        if record.get("schedule_id") != f"partitioned-{threads}":
            raise EvidenceError("environment-collision schedule id mismatch")
        if integer_vector(record.get("expected_enumeration"), "expected_enumeration") != canonical_order:
            raise EvidenceError("environment-collision expected enumeration is not canonical")
        if integer_vector(record.get("actual_enumeration"), "actual_enumeration") != canonical_order:
            raise EvidenceError("environment-collision actual enumeration is not canonical")
        worker_enumerations = integer_matrix(
            record.get("worker_enumerations"), "worker_enumerations"
        )
        if worker_enumerations != [canonical_order] * threads:
            raise EvidenceError(
                f"environment-collision worker enumerations differ for threads={threads}"
            )

        expected_root = record.get("expected_root")
        actual_root = record.get("actual_root")
        worker_roots = record.get("worker_roots")
        if not isinstance(expected_root, str) or not re.fullmatch(
            r"[0-9a-f]{64}", expected_root
        ):
            raise EvidenceError("environment-collision expected root is malformed")
        if actual_root != expected_root:
            raise EvidenceError("environment-collision actual root differs")
        if not isinstance(worker_roots, list) or worker_roots != [expected_root] * threads:
            raise EvidenceError("environment-collision worker roots differ")
        if shared_environment_root is None:
            shared_environment_root = expected_root
        elif expected_root != shared_environment_root:
            raise EvidenceError("environment-collision root changed across thread counts")
        if integer_vector(
            record.get("observed_enumeration_nodes"), "observed_enumeration_nodes"
        ) != [1] * threads:
            raise EvidenceError("environment-collision enumeration-node facts differ")
        if integer_vector(
            record.get("observed_environment_entries"), "observed_environment_entries"
        ) != [ENVIRONMENT_COLLISION_CARDINALITY] * threads:
            raise EvidenceError("environment-collision environment-entry facts differ")
        budget = record.get("operation_budget")
        if not isinstance(budget, dict) or set(budget) != {
            "max_collision_cardinality",
            "thread_matrix",
        }:
            raise EvidenceError("environment-collision operation budget is malformed")
        budget_cardinality = budget.get("max_collision_cardinality")
        if (
            not isinstance(budget_cardinality, int)
            or isinstance(budget_cardinality, bool)
            or budget_cardinality != ENVIRONMENT_COLLISION_CARDINALITY
        ):
            raise EvidenceError("environment-collision cardinality budget differs")
        if integer_vector(budget.get("thread_matrix"), "operation_budget.thread_matrix") != list(
            ENVIRONMENT_COLLISION_THREADS
        ):
            raise EvidenceError("environment-collision thread budget differs")

        start_us = record.get("monotonic_start_us")
        end_us = record.get("monotonic_end_us")
        duration_us = record.get("duration_us")
        if any(
            not isinstance(value, int) or isinstance(value, bool) or value < 0
            for value in (start_us, end_us, duration_us)
        ):
            raise EvidenceError("environment-collision timing facts are malformed")
        if end_us - start_us != duration_us or start_us < previous_end:
            raise EvidenceError("environment-collision timing facts are inconsistent")
        previous_end = end_us
        if record.get("timing_used_as_gate") is not False:
            raise EvidenceError("environment-collision timing was promoted to a gate")
        if record.get("signal") is not None or record.get("first_divergence") is not None:
            raise EvidenceError("passing environment-collision detail claims a failure")

    if (
        shared_input_root is None
        or shared_collision_hash is None
        or shared_environment_root is None
    ):
        raise EvidenceError("environment-collision shared identity facts are incomplete")
    return {
        "schema": "fln.validation/1",
        "validator": "environment-collision/1",
        "subject": stdout_relative,
        "valid": True,
        "phase": phase,
        "run_id": expected_run_id,
        "observed_exit": observed_exit,
        "records": len(records),
        "thread_matrix": list(ENVIRONMENT_COLLISION_THREADS),
        "collision_cardinality": ENVIRONMENT_COLLISION_CARDINALITY,
        "canonical_input_root": shared_input_root,
        "collision_hash": shared_collision_hash,
        "environment_root": shared_environment_root,
        "stdout_artifact": stdout_relative,
        "stderr_artifact": stderr_relative,
        "stdout_sha256": stdout_digest,
        "stderr_sha256": stderr_digest,
    }


def read_environment_resource_collision_stream(
    path: Path, artifact_root: Path, *, label: str
) -> tuple[Path, bytes, str, str, str]:
    root = lexical_absolute(artifact_root)
    absolute = require_within(
        path, root, label=f"environment-resource-collision {label}"
    )
    data, _size, digest = stable_file_facts(absolute, max_bytes=MAX_LOG_BYTES)
    if data and not data.endswith(b"\n"):
        raise EvidenceError(
            f"environment-resource-collision {label} is unterminated: {absolute}"
        )
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        raise EvidenceError(
            f"environment-resource-collision {label} is not UTF-8: {absolute}"
        ) from error
    for number, raw_line in enumerate(data.splitlines(), 1):
        if len(raw_line) > MAX_RECORD_BYTES:
            raise EvidenceError(
                f"{absolute}:{number}: environment-resource-collision "
                f"{label} line is too large"
            )
    return absolute, data, text, digest, absolute.relative_to(root).as_posix()


def environment_resource_collision_failure_material(text: str) -> bool:
    failed_forms = {
        f"{ENVIRONMENT_RESOURCE_COLLISION_TEST} --- FAILED",
        f"test {ENVIRONMENT_RESOURCE_COLLISION_TEST} ... FAILED",
    }
    for line in text.splitlines():
        stripped = line.strip()
        if (
            stripped in failed_forms
            or stripped.startswith("test result: FAILED.")
            or stripped.startswith("thread '")
            and " panicked at " in stripped
            or re.fullmatch(r"assertion .* failed(?:: .*)?", stripped) is not None
            or stripped.startswith("error: test failed")
            or stripped.startswith("error: could not compile")
        ):
            return True
    return False


def validate_environment_resource_collision(
    stdout_path: Path,
    stderr_path: Path,
    phase: str,
    expected_run_id: str,
    observed_exit: int,
    *,
    artifact_root: Path,
    expected_stdout_artifact: str,
    expected_stderr_artifact: str,
    expected_cwd: str | None = None,
    expected_argv: str | None = None,
    expected_cache_state: str | None = None,
) -> dict[str, Any]:
    if phase not in {"positive", "mutant", "recovery"}:
        raise EvidenceError(
            f"unsupported environment-resource-collision phase: {phase!r}"
        )
    if not re.fullmatch(r"[A-Za-z0-9_-]+", expected_run_id):
        raise EvidenceError("environment-resource-collision run id is malformed")
    if not isinstance(observed_exit, int) or isinstance(observed_exit, bool):
        raise EvidenceError(
            "environment-resource-collision observed exit is not an integer"
        )
    expected_exit = 101 if phase == "mutant" else 0
    if observed_exit != expected_exit:
        raise EvidenceError(
            f"environment-resource-collision {phase} exit {observed_exit}, "
            f"expected {expected_exit}"
        )

    root = lexical_absolute(artifact_root)
    stdout_path, stdout_data, stdout_text, stdout_digest, stdout_relative = (
        read_environment_resource_collision_stream(
            stdout_path, root, label="stdout"
        )
    )
    stderr_path, stderr_data, stderr_text, stderr_digest, stderr_relative = (
        read_environment_resource_collision_stream(
            stderr_path, root, label="stderr"
        )
    )
    if stdout_path == stderr_path:
        raise EvidenceError(
            "environment-resource-collision stdout and stderr are not distinct"
        )
    for label, expected, actual in (
        ("stdout", expected_stdout_artifact, stdout_relative),
        ("stderr", expected_stderr_artifact, stderr_relative),
    ):
        expected_path = Path(expected)
        if (
            not expected
            or expected_path.is_absolute()
            or ".." in expected_path.parts
            or expected == "."
            or expected_path.as_posix() != expected
        ):
            raise EvidenceError(
                "environment-resource-collision expected "
                f"{label} artifact is not a canonical relative path"
            )
        if expected != actual:
            raise EvidenceError(
                f"environment-resource-collision {label} path {actual!r}, "
                f"expected {expected!r}"
            )

    schema_marker = ENVIRONMENT_RESOURCE_COLLISION_SCHEMA.encode("ascii")
    if schema_marker in stderr_data:
        raise EvidenceError(
            "environment-resource-collision detail rows leaked into stderr"
        )
    records: list[dict[str, Any]] = []
    for number, raw_line in enumerate(stdout_data.splitlines(), 1):
        if schema_marker not in raw_line:
            continue
        object_start = raw_line.find(b"{")
        if object_start < 0:
            raise EvidenceError(
                f"{stdout_path}:{number}: resource-collision evidence "
                "is not a JSON object"
            )
        value = parse_json(
            raw_line[object_start:].strip(), subject=f"{stdout_path}:{number}"
        )
        if not isinstance(value, dict):
            raise EvidenceError(
                f"{stdout_path}:{number}: resource-collision evidence "
                "is not an object"
            )
        records.append(value)

    failed_forms = {
        f"{ENVIRONMENT_RESOURCE_COLLISION_TEST} --- FAILED",
        f"test {ENVIRONMENT_RESOURCE_COLLISION_TEST} ... FAILED",
    }
    if phase == "mutant":
        if records:
            raise EvidenceError(
                "killed environment-resource-collision mutant emitted passing records"
            )
        failed_lines = [
            line.strip()
            for line in stdout_text.splitlines()
            if line.strip() in failed_forms
        ]
        if len(failed_lines) != 1:
            raise EvidenceError(
                "resource-collision mutant stdout lacks exactly one named "
                "FAILED test result"
            )
        if any(line.strip() in failed_forms for line in stderr_text.splitlines()):
            raise EvidenceError(
                "resource-collision mutant FAILED test result leaked into stderr"
            )
        if ENVIRONMENT_RESOURCE_COLLISION_MUTANT_MARKER in stdout_text:
            raise EvidenceError(
                "resource-collision mutant assertion marker leaked into stdout"
            )
        panic_identity = re.compile(
            rf"^thread '{re.escape(ENVIRONMENT_RESOURCE_COLLISION_TEST)}'"
            r"(?: \([1-9][0-9]*\))? panicked at ",
            re.MULTILINE,
        )
        if len(panic_identity.findall(stderr_text)) != 1:
            raise EvidenceError(
                "resource-collision mutant stderr lacks exactly one named panic"
            )
        if stderr_text.count(ENVIRONMENT_RESOURCE_COLLISION_MUTANT_MARKER) != 1:
            raise EvidenceError(
                "resource-collision mutant stderr lacks the exact inline-threshold "
                "assertion marker"
            )
        result_lines = [
            line.strip()
            for line in stdout_text.splitlines()
            if line.strip().startswith("test result: FAILED.")
        ]
        if len(result_lines) != 1 or not re.match(
            r"^test result: FAILED\. 0 passed; 1 failed;", result_lines[0]
        ):
            raise EvidenceError(
                "resource-collision mutant stdout lacks the exact one-test "
                "failure summary"
            )
        if any(
            line.strip().startswith("test result: FAILED.")
            for line in stderr_text.splitlines()
        ):
            raise EvidenceError(
                "resource-collision mutant failure summary leaked into stderr"
            )
        if any(
            line.strip().startswith("test result: ok.")
            for line in (*stdout_text.splitlines(), *stderr_text.splitlines())
        ):
            raise EvidenceError(
                "resource-collision mutant streams contain a passing summary"
            )
        if "error: could not compile" in stdout_text + stderr_text:
            raise EvidenceError(
                "resource-collision mutant was a compile failure, not a killed mutant"
            )
        return {
            "schema": "fln.validation/1",
            "validator": "environment-resource-collision/1",
            "subject": stdout_relative,
            "valid": True,
            "phase": phase,
            "run_id": expected_run_id,
            "observed_exit": observed_exit,
            "records": 0,
            "failed_test": ENVIRONMENT_RESOURCE_COLLISION_TEST,
            "assertion_marker": ENVIRONMENT_RESOURCE_COLLISION_MUTANT_MARKER,
            "stdout_artifact": stdout_relative,
            "stderr_artifact": stderr_relative,
            "stdout_sha256": stdout_digest,
            "stderr_sha256": stderr_digest,
        }

    required_cli_values = {
        "expected cwd": expected_cwd,
        "expected argv": expected_argv,
        "expected cache state": expected_cache_state,
    }
    missing_cli = sorted(
        label
        for label, value in required_cli_values.items()
        if not isinstance(value, str) or not value
    )
    if missing_cli:
        raise EvidenceError(
            f"environment-resource-collision {phase} validation "
            f"lacks {missing_cli!r}"
        )
    if not Path(expected_cwd).is_absolute():
        raise EvidenceError(
            "environment-resource-collision expected cwd is not absolute"
        )
    if len(records) != len(ENVIRONMENT_RESOURCE_COLLISION_THREADS):
        raise EvidenceError(
            f"environment-resource-collision {phase} emitted {len(records)} "
            f"detail records, expected "
            f"{len(ENVIRONMENT_RESOURCE_COLLISION_THREADS)}"
        )
    if environment_resource_collision_failure_material(stdout_text):
        raise EvidenceError(
            f"environment-resource-collision {phase} stdout contains failure material"
        )
    if environment_resource_collision_failure_material(stderr_text):
        raise EvidenceError(
            f"environment-resource-collision {phase} stderr contains failure material"
        )
    pass_result_lines = [
        line.strip()
        for line in stdout_text.splitlines()
        if line.strip().startswith("test result: ok.")
    ]
    if len(pass_result_lines) != 1 or not re.match(
        r"^test result: ok\. 1 passed; 0 failed;", pass_result_lines[0]
    ):
        raise EvidenceError(
            f"environment-resource-collision {phase} log lacks the exact "
            "one-test pass summary"
        )

    expected_identity = {
        "schema": ENVIRONMENT_RESOURCE_COLLISION_SCHEMA,
        "bead": "fln-amv.13",
        "claim_id": "fln-amv.13-resource-bounded-collisions",
        "claim_type": "bounded_model",
        "invariant_id": "FL-INV-01",
        "invariant_relation": "supports-local-pmap-slice",
        "gate_id": "PG-5",
        "gate_relation": "partial-component-evidence",
        "parity_ledger_row": (
            "not_applicable_internal_data_structure_resource_bound"
        ),
        "data_grade": "verified",
        "epoch": "lean-v4.32.0",
        "mode": "sound",
        "profile": "e2e",
        "seed": "partition-rotation-v1",
        "canonical_input_root": ENVIRONMENT_RESOURCE_COLLISION_INPUT_ROOT,
        "scenario": "collision-resource-schedule-matrix",
        "status": "pass",
        "collision_hash": ENVIRONMENT_RESOURCE_COLLISION_HASH,
        "expected_root": ENVIRONMENT_RESOURCE_COLLISION_ROOT,
        "actual_root": ENVIRONMENT_RESOURCE_COLLISION_ROOT,
        "expected_recovery_root": ENVIRONMENT_RESOURCE_COLLISION_RECOVERY_ROOT,
        "actual_recovery_root": ENVIRONMENT_RESOURCE_COLLISION_RECOVERY_ROOT,
        "representation_tier": "persistent-avl",
        "secondary_identity": "exact-PKey-Ord-with-Eq-consistency",
        "secondary_hashing": "none",
        "secondary_identity_collision_behavior": (
            "Ord-equal-overwrites;Ord-distinct-path-copies"
        ),
        "cleanup_status": "retained_by_policy",
        "final_state": "typed-refusal-followed-by-exact-bound-recovery",
    }
    expected_bounds = {
        "construction_comparisons": 18_000,
        "inline_cloned_entries": 36,
        "append_minimum_shared_nodes": 983,
        "lookup_comparisons": 14,
        "maximum_avl_height": 14,
        "tree_fresh_nodes_per_insert": 17,
        "legacy_vector_copies": 499_500,
    }
    canonical_order = list(range(ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY))
    shared_platform: str | None = None
    previous_end = -1

    def exact_integer(record: dict[str, Any], key: str, expected: int) -> None:
        value = record.get(key)
        if not isinstance(value, int) or isinstance(value, bool) or value != expected:
            raise EvidenceError(
                f"environment-resource-collision {key} {value!r}, "
                f"expected integer {expected}"
            )

    def integer_vector(value: Any, label: str, length: int) -> list[int]:
        if (
            not isinstance(value, list)
            or len(value) != length
            or any(
                not isinstance(item, int) or isinstance(item, bool) or item < 0
                for item in value
            )
        ):
            raise EvidenceError(
                f"environment-resource-collision {label} is not a "
                f"{length}-element nonnegative integer array"
            )
        return value

    for record, threads in zip(
        records, ENVIRONMENT_RESOURCE_COLLISION_THREADS, strict=True
    ):
        if set(record) != ENVIRONMENT_RESOURCE_COLLISION_FIELDS:
            missing = sorted(ENVIRONMENT_RESOURCE_COLLISION_FIELDS - set(record))
            extra = sorted(set(record) - ENVIRONMENT_RESOURCE_COLLISION_FIELDS)
            raise EvidenceError(
                "environment-resource-collision v1 field mismatch: "
                f"missing={missing!r} extra={extra!r}"
            )
        for key, expected in expected_identity.items():
            if record.get(key) != expected:
                raise EvidenceError(
                    f"environment-resource-collision {key} "
                    f"{record.get(key)!r}, expected {expected!r}"
                )
        exact_integer(
            record, "version", ENVIRONMENT_RESOURCE_COLLISION_VERSION
        )
        exact_integer(
            record,
            "collision_cardinality",
            ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY,
        )
        exact_integer(record, "threads", threads)
        exact_integer(record, "workers_built", threads)
        exact_integer(record, "distinct_insertion_orders", threads)
        exact_integer(record, "promotion_cardinality", 9)
        exact_integer(record, "demotion_cardinality", 8)
        exact_integer(record, "process_exit", 0)
        if record.get("run_id") != expected_run_id:
            raise EvidenceError(
                "environment-resource-collision detail run id mismatch"
            )
        if record.get("cwd") != expected_cwd:
            raise EvidenceError("environment-resource-collision detail cwd mismatch")
        if record.get("argv") != [expected_argv]:
            raise EvidenceError("environment-resource-collision detail argv mismatch")
        if (
            record.get("stdout_artifact") != expected_stdout_artifact
            or record.get("stderr_artifact") != expected_stderr_artifact
        ):
            raise EvidenceError(
                "environment-resource-collision detail artifact identity mismatch"
            )
        if record.get("cache_state") != expected_cache_state:
            raise EvidenceError(
                "environment-resource-collision detail cache-state mismatch"
            )
        platform_value = record.get("platform")
        if (
            not isinstance(platform_value, str)
            or not platform_value
            or "-" not in platform_value
        ):
            raise EvidenceError(
                "environment-resource-collision platform identity is malformed"
            )
        if shared_platform is None:
            shared_platform = platform_value
        elif platform_value != shared_platform:
            raise EvidenceError(
                "environment-resource-collision platform changed across schedules"
            )
        if record.get("schedule_id") != f"partitioned-{threads}":
            raise EvidenceError(
                "environment-resource-collision schedule id mismatch"
            )

        expected_representative = environment_collision_insertion_order(
            ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY, threads, 0
        )
        if record.get("representative_insertion_order") != expected_representative:
            raise EvidenceError(
                "environment-resource-collision representative insertion "
                f"order differs for threads={threads}"
            )
        expected_insertion_roots = list(
            ENVIRONMENT_RESOURCE_COLLISION_INSERTION_ROOTS[threads]
        )
        if record.get("worker_insertion_order_roots") != expected_insertion_roots:
            raise EvidenceError(
                "environment-resource-collision worker insertion roots "
                f"differ for threads={threads}"
            )
        if len(set(expected_insertion_roots)) != threads:
            raise EvidenceError(
                "environment-resource-collision pinned worker schedules "
                "are not distinct"
            )
        if record.get("expected_order") != canonical_order:
            raise EvidenceError(
                "environment-resource-collision expected order is not canonical"
            )
        if record.get("actual_order") != canonical_order:
            raise EvidenceError(
                "environment-resource-collision actual order is not canonical"
            )
        if record.get("worker_enumeration_roots") != [
            ENVIRONMENT_RESOURCE_COLLISION_INPUT_ROOT
        ] * threads:
            raise EvidenceError(
                "environment-resource-collision worker enumeration roots differ"
            )
        if record.get("worker_roots") != [
            ENVIRONMENT_RESOURCE_COLLISION_ROOT
        ] * threads:
            raise EvidenceError(
                "environment-resource-collision worker roots differ"
            )
        if record.get("worker_recovery_roots") != [
            ENVIRONMENT_RESOURCE_COLLISION_RECOVERY_ROOT
        ] * threads:
            raise EvidenceError(
                "environment-resource-collision worker recovery roots differ"
            )

        comparisons = integer_vector(record.get("comparisons"), "comparisons", threads)
        fresh_map_nodes = integer_vector(
            record.get("fresh_map_nodes"), "fresh_map_nodes", threads
        )
        fresh_collision_nodes = integer_vector(
            record.get("fresh_collision_nodes"), "fresh_collision_nodes", threads
        )
        cloned_inline_entries = integer_vector(
            record.get("cloned_inline_entries"), "cloned_inline_entries", threads
        )
        final_collision_nodes = integer_vector(
            record.get("final_collision_nodes"), "final_collision_nodes", threads
        )
        snapshot_root_arc_bumps = integer_vector(
            record.get("snapshot_root_arc_bumps"),
            "snapshot_root_arc_bumps",
            threads,
        )
        snapshot_shared_nodes = integer_vector(
            record.get("snapshot_shared_collision_nodes"),
            "snapshot_shared_collision_nodes",
            threads,
        )
        append_shared_nodes = integer_vector(
            record.get("append_shared_collision_nodes"),
            "append_shared_collision_nodes",
            threads,
        )
        append_fresh_nodes = integer_vector(
            record.get("append_fresh_nodes"), "append_fresh_nodes", threads
        )
        lookup_comparisons = integer_vector(
            record.get("max_lookup_comparisons"),
            "max_lookup_comparisons",
            threads,
        )
        if any(value <= 0 or value > 18_000 for value in comparisons):
            raise EvidenceError(
                "environment-resource-collision comparison bound exceeded"
            )
        if fresh_map_nodes != [ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY] * threads:
            raise EvidenceError(
                "environment-resource-collision fresh map-node count differs"
            )
        if any(value <= 0 or value > 18_000 for value in fresh_collision_nodes):
            raise EvidenceError(
                "environment-resource-collision construction allocation "
                "bound exceeded"
            )
        if cloned_inline_entries != [36] * threads:
            raise EvidenceError(
                "environment-resource-collision inline clone count differs"
            )
        if final_collision_nodes != [
            ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY
        ] * threads:
            raise EvidenceError(
                "environment-resource-collision final node count differs"
            )
        if snapshot_root_arc_bumps != [1] * threads:
            raise EvidenceError(
                "environment-resource-collision snapshot root identity differs"
            )
        if snapshot_shared_nodes != [
            ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY
        ] * threads:
            raise EvidenceError(
                "environment-resource-collision snapshot sharing differs"
            )
        if any(
            value < 983
            or value > ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY
            for value in append_shared_nodes
        ):
            raise EvidenceError(
                "environment-resource-collision append sharing bound violated"
            )
        if any(value <= 0 or value > 18 for value in append_fresh_nodes):
            raise EvidenceError(
                "environment-resource-collision append allocation bound exceeded"
            )
        if any(value <= 0 or value > 14 for value in lookup_comparisons):
            raise EvidenceError(
                "environment-resource-collision lookup comparison bound exceeded"
            )

        budget = record.get("budget")
        if not isinstance(budget, dict) or set(budget) != {
            "max_collision_entries",
            "max_expanded_weight",
            "admission_max_fresh_nodes",
            "refusal_max_fresh_nodes",
            "refusal_resource",
            "refusal_attempted",
            "failure_atomic",
            "exact_boundary_recovery",
        }:
            raise EvidenceError(
                "environment-resource-collision budget is malformed"
            )
        for key in ("max_collision_entries", "max_expanded_weight"):
            value = budget.get(key)
            if (
                not isinstance(value, int)
                or isinstance(value, bool)
                or value != ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY + 1
            ):
                raise EvidenceError(
                    f"environment-resource-collision budget {key} differs"
                )
        if integer_vector(
            budget.get("admission_max_fresh_nodes"),
            "budget.admission_max_fresh_nodes",
            threads,
        ) != [18] * threads:
            raise EvidenceError(
                "environment-resource-collision admission allocation differs"
            )
        if integer_vector(
            budget.get("refusal_max_fresh_nodes"),
            "budget.refusal_max_fresh_nodes",
            threads,
        ) != [17] * threads:
            raise EvidenceError(
                "environment-resource-collision refusal limit differs"
            )
        if integer_vector(
            budget.get("refusal_attempted"),
            "budget.refusal_attempted",
            threads,
        ) != [18] * threads:
            raise EvidenceError(
                "environment-resource-collision refusal attempt differs"
            )
        if budget.get("refusal_resource") != "FreshNodes":
            raise EvidenceError(
                "environment-resource-collision refusal resource differs"
            )
        if budget.get("failure_atomic") is not True:
            raise EvidenceError(
                "environment-resource-collision refusal was not failure-atomic"
            )
        if budget.get("exact_boundary_recovery") is not True:
            raise EvidenceError(
                "environment-resource-collision exact-bound recovery failed"
            )
        if record.get("bounds") != expected_bounds:
            raise EvidenceError(
                "environment-resource-collision bounds differ from the pin"
            )
        if record.get("resources") != {
            "expanded_weight": ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY,
            "environment_entries": ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY,
            "timing_used_as_gate": False,
        }:
            raise EvidenceError(
                "environment-resource-collision resource facts differ"
            )

        start_us = record.get("monotonic_start_us")
        end_us = record.get("monotonic_end_us")
        duration_us = record.get("duration_us")
        if any(
            not isinstance(value, int) or isinstance(value, bool) or value < 0
            for value in (start_us, end_us, duration_us)
        ):
            raise EvidenceError(
                "environment-resource-collision timing facts are malformed"
            )
        if end_us - start_us != duration_us or start_us < previous_end:
            raise EvidenceError(
                "environment-resource-collision timing facts are inconsistent"
            )
        previous_end = end_us
        if record.get("timing_used_as_gate") is not False:
            raise EvidenceError(
                "environment-resource-collision timing was promoted to a gate"
            )
        if record.get("signal") is not None or record.get("first_divergence") is not None:
            raise EvidenceError(
                "passing environment-resource-collision claims a failure"
            )

    return {
        "schema": "fln.validation/1",
        "validator": "environment-resource-collision/1",
        "subject": stdout_relative,
        "valid": True,
        "phase": phase,
        "run_id": expected_run_id,
        "observed_exit": observed_exit,
        "records": len(records),
        "thread_matrix": list(ENVIRONMENT_RESOURCE_COLLISION_THREADS),
        "collision_cardinality": ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY,
        "canonical_input_root": ENVIRONMENT_RESOURCE_COLLISION_INPUT_ROOT,
        "collision_hash": ENVIRONMENT_RESOURCE_COLLISION_HASH,
        "environment_root": ENVIRONMENT_RESOURCE_COLLISION_ROOT,
        "recovery_root": ENVIRONMENT_RESOURCE_COLLISION_RECOVERY_ROOT,
        "stdout_artifact": stdout_relative,
        "stderr_artifact": stderr_relative,
        "stdout_sha256": stdout_digest,
        "stderr_sha256": stderr_digest,
    }


def read_environment_identity_stream(
    path: Path, artifact_root: Path, *, label: str
) -> tuple[Path, bytes, str, str, str]:
    root = lexical_absolute(artifact_root)
    absolute = require_within(path, root, label=f"environment-identity {label}")
    data, _size, digest = stable_file_facts(absolute, max_bytes=MAX_LOG_BYTES)
    if data and not data.endswith(b"\n"):
        raise EvidenceError(f"environment-identity {label} is unterminated: {absolute}")
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        raise EvidenceError(
            f"environment-identity {label} is not UTF-8: {absolute}"
        ) from error
    for number, raw_line in enumerate(data.splitlines(), 1):
        if len(raw_line) > MAX_RECORD_BYTES:
            raise EvidenceError(
                f"{absolute}:{number}: environment-identity {label} line is too large"
            )
    return absolute, data, text, digest, absolute.relative_to(root).as_posix()


def environment_identity_failure_material(text: str, test_name: str) -> bool:
    failed_forms = {
        f"{test_name} --- FAILED",
        f"test {test_name} ... FAILED",
    }
    for line in text.splitlines():
        stripped = line.strip()
        if (
            stripped in failed_forms
            or stripped.startswith("test result: FAILED.")
            or stripped.startswith("thread '")
            and " panicked at " in stripped
            or re.fullmatch(r"assertion .* failed(?:: .*)?", stripped) is not None
            or stripped.startswith("error: test failed")
            or stripped.startswith("error: could not compile")
        ):
            return True
    return False


def prepare_environment_identity_validation(
    stdout_path: Path,
    stderr_path: Path,
    *,
    artifact_root: Path,
    schema: str,
    test_name: str,
    expected_run_id: str,
    observed_exit: int,
    expected_stdout_artifact: str,
    expected_stderr_artifact: str,
    expected_records: int,
    additional_schemas: Sequence[str] = (),
) -> tuple[list[dict[str, Any]], str, str, str, str]:
    if not re.fullmatch(r"[A-Za-z0-9_-]+", expected_run_id):
        raise EvidenceError("environment-identity run id is malformed")
    if (
        not isinstance(observed_exit, int)
        or isinstance(observed_exit, bool)
        or observed_exit != 0
    ):
        raise EvidenceError(
            f"environment-identity observed exit {observed_exit!r}, expected 0"
        )
    root = lexical_absolute(artifact_root)
    stdout_path, stdout_data, stdout_text, stdout_digest, stdout_relative = (
        read_environment_identity_stream(stdout_path, root, label="stdout")
    )
    stderr_path, stderr_data, stderr_text, stderr_digest, stderr_relative = (
        read_environment_identity_stream(stderr_path, root, label="stderr")
    )
    if stdout_path == stderr_path:
        raise EvidenceError("environment-identity stdout and stderr are not distinct")
    for label, expected, actual in (
        ("stdout", expected_stdout_artifact, stdout_relative),
        ("stderr", expected_stderr_artifact, stderr_relative),
    ):
        if not isinstance(expected, str) or not expected:
            raise EvidenceError(f"environment-identity expected {label} is missing")
        if expected != actual:
            raise EvidenceError(
                f"environment-identity {label} path {actual!r}, expected {expected!r}"
            )
    if environment_identity_failure_material(stdout_text, test_name):
        raise EvidenceError("environment-identity stdout contains failure material")
    if environment_identity_failure_material(stderr_text, test_name):
        raise EvidenceError("environment-identity stderr contains failure material")

    schemas = (schema, *additional_schemas)
    if len(set(schemas)) != len(schemas) or any(not item for item in schemas):
        raise EvidenceError("environment-identity schema inventory is malformed")
    schema_markers = {
        item: f'"schema":"{item}"'.encode() for item in schemas
    }
    schema_prefixes = {
        item: b'{"schema":"' + item.encode() + b'"' for item in schemas
    }
    records: list[dict[str, Any]] = []
    for stream_label, data in (("stdout", stdout_data), ("stderr", stderr_data)):
        for number, raw_line in enumerate(data.splitlines(), 1):
            matched = [
                item for item in schemas if schema_markers[item] in raw_line
            ]
            if not matched:
                continue
            if len(matched) != 1:
                raise EvidenceError(
                    f"environment-identity {stream_label}:{number} "
                    "record matches multiple schemas"
                )
            matched_schema = matched[0]
            if not raw_line.startswith(schema_prefixes[matched_schema]):
                raise EvidenceError(
                    f"environment-identity {stream_label}:{number} "
                    "record is not canonically positioned"
                )
            try:
                record = json.loads(raw_line)
            except (UnicodeDecodeError, json.JSONDecodeError) as error:
                raise EvidenceError(
                    f"environment-identity {stream_label}:{number} "
                    "record is malformed"
                ) from error
            if not isinstance(record, dict):
                raise EvidenceError(
                    f"environment-identity {stream_label}:{number} "
                    "record is not an object"
                )
            if stream_label != "stdout":
                raise EvidenceError(
                    "environment-identity detail rows leaked into stderr"
                )
            records.append(record)
    if len(records) != expected_records:
        raise EvidenceError(
            f"environment-identity emitted {len(records)} records, "
            f"expected {expected_records}"
        )
    return (
        records,
        stdout_relative,
        stderr_relative,
        stdout_digest,
        stderr_digest,
    )


def require_environment_identity_fields(
    record: dict[str, Any],
    expected_fields: set[str],
    *,
    schema: str,
    expected_run_id: str,
    expected_beads: list[str],
    label: str,
    expected_final_state: str = "verified",
) -> None:
    if set(record) != expected_fields:
        missing = sorted(expected_fields - set(record))
        extra = sorted(set(record) - expected_fields)
        raise EvidenceError(
            f"{label} field mismatch: missing={missing!r} extra={extra!r}"
        )
    if (
        record.get("schema") != schema
        or record.get("version") != ENVIRONMENT_IDENTITY_VERSION
        or record.get("run_id") != expected_run_id
        or record.get("beads") != expected_beads
        or record.get("status") != "pass"
        or record.get("final_state") != expected_final_state
    ):
        raise EvidenceError(f"{label} shared identity fields differ")


def require_environment_identity_hex(value: Any, *, label: str) -> str:
    if not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{64}", value) is None:
        raise EvidenceError(f"{label} is not canonical lowercase hex")
    return value


def require_environment_identity_count(value: Any, *, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise EvidenceError(f"{label} is not a nonnegative integer")
    return value


def validate_declaration_tag_matrix(
    stdout_path: Path,
    stderr_path: Path,
    expected_run_id: str,
    observed_exit: int,
    *,
    artifact_root: Path,
    expected_stdout_artifact: str,
    expected_stderr_artifact: str,
) -> dict[str, Any]:
    (
        records,
        stdout_relative,
        stderr_relative,
        stdout_digest,
        stderr_digest,
    ) = prepare_environment_identity_validation(
        stdout_path,
        stderr_path,
        artifact_root=artifact_root,
        schema=DECLARATION_TAG_MATRIX_SCHEMA,
        test_name=DECLARATION_TAG_MATRIX_TEST,
        expected_run_id=expected_run_id,
        observed_exit=observed_exit,
        expected_stdout_artifact=expected_stdout_artifact,
        expected_stderr_artifact=expected_stderr_artifact,
        expected_records=11,
    )
    common = {
        "schema",
        "version",
        "run_id",
        "beads",
        "scenario",
        "status",
        "final_state",
    }
    case_fields = common | {
        "case",
        "family",
        "variant",
        "kind",
        "canonical_tag",
        "production_tag",
        "tag_source",
        "stream_bytes",
        "golden_stream_bytes",
        "stream_hash",
        "golden_stream_hash",
        "expected_digest",
        "actual_digest",
        "golden_digest",
        "repeated_digest",
        "digest_relation",
        "repeat_relation",
        "expected_root",
        "actual_root",
        "root_relation",
        "model",
        "elapsed_us",
    }
    thread_fields = common | {
        "worker_count",
        "distinct_root_count",
        "expected_root",
        "actual_root",
        "root_relation",
        "order_independence",
        "elapsed_us",
    }
    summary_fields = common | {
        "case_count",
        "unique_digest_count",
        "pairwise_comparisons",
        "expected_pairwise_comparisons",
        "thread_matrix",
        "thread_matrix_roots_distinct",
        "canonical_root",
        "source_order_defect_root",
        "source_order_defect_relation",
        "omitted_declaration_root",
        "omitted_declaration_relation",
        "named_defects_discriminated",
        "claim_type",
        "elapsed_us",
    }
    case_rows: dict[tuple[str, str], dict[str, Any]] = {}
    thread_rows: dict[int, dict[str, Any]] = {}
    summaries: list[dict[str, Any]] = []
    for number, record in enumerate(records, 1):
        scenario = record.get("scenario")
        label = f"declaration-tag record {number}"
        if scenario == "declaration-tag-matrix":
            require_environment_identity_fields(
                record,
                case_fields,
                schema=DECLARATION_TAG_MATRIX_SCHEMA,
                expected_run_id=expected_run_id,
                expected_beads=["fln-amv.12", "fln-amv.14"],
                label=label,
            )
            key = (record.get("family"), record.get("variant"))
            if key not in DECLARATION_TAG_GOLDENS or key in case_rows:
                raise EvidenceError(f"{label} has an unknown or duplicate case")
            kind, tag, stream_bytes, stream_hash, digest = (
                DECLARATION_TAG_GOLDENS[key]
            )
            if (
                record.get("case") != f"{key[0]}/{key[1]}"
                or record.get("kind") != kind
                or record.get("canonical_tag") != tag
                or record.get("production_tag") != tag
                or record.get("tag_source") != "explicit_exhaustive_match"
                or record.get("stream_bytes") != stream_bytes
                or record.get("golden_stream_bytes") != stream_bytes
                or record.get("stream_hash") != stream_hash
                or record.get("golden_stream_hash") != stream_hash
                or record.get("expected_digest") != digest
                or record.get("actual_digest") != digest
                or record.get("golden_digest") != digest
                or record.get("repeated_digest") != digest
                or record.get("digest_relation") != "equal"
                or record.get("repeat_relation") != "equal"
                or record.get("root_relation") != "equal"
                or record.get("model") != "independent-complete-stream-v1"
            ):
                raise EvidenceError(f"{label} differs from the frozen case contract")
            expected_root = require_environment_identity_hex(
                record.get("expected_root"), label=f"{label} expected root"
            )
            actual_root = require_environment_identity_hex(
                record.get("actual_root"), label=f"{label} actual root"
            )
            if expected_root != actual_root:
                raise EvidenceError(f"{label} root relation is false")
            require_environment_identity_count(
                record.get("elapsed_us"), label=f"{label} elapsed_us"
            )
            case_rows[key] = record
        elif scenario == "declaration-tag-thread-matrix":
            require_environment_identity_fields(
                record,
                thread_fields,
                schema=DECLARATION_TAG_MATRIX_SCHEMA,
                expected_run_id=expected_run_id,
                expected_beads=["fln-amv.12", "fln-amv.14"],
                label=label,
            )
            workers = record.get("worker_count")
            if workers not in {1, 8, 32} or workers in thread_rows:
                raise EvidenceError(f"{label} has an unknown or duplicate worker count")
            expected_root = require_environment_identity_hex(
                record.get("expected_root"), label=f"{label} expected root"
            )
            actual_root = require_environment_identity_hex(
                record.get("actual_root"), label=f"{label} actual root"
            )
            if (
                record.get("distinct_root_count") != 1
                or expected_root != actual_root
                or record.get("root_relation") != "equal"
                or record.get("order_independence") != "proven"
            ):
                raise EvidenceError(f"{label} thread relation differs")
            require_environment_identity_count(
                record.get("elapsed_us"), label=f"{label} elapsed_us"
            )
            thread_rows[workers] = record
        elif scenario == "declaration-tag-summary":
            require_environment_identity_fields(
                record,
                summary_fields,
                schema=DECLARATION_TAG_MATRIX_SCHEMA,
                expected_run_id=expected_run_id,
                expected_beads=["fln-amv.12", "fln-amv.14"],
                label=label,
            )
            summaries.append(record)
        else:
            raise EvidenceError(f"{label} has an unknown scenario")
    if set(case_rows) != set(DECLARATION_TAG_GOLDENS):
        raise EvidenceError("declaration-tag case matrix is incomplete")
    if set(thread_rows) != {1, 8, 32}:
        raise EvidenceError("declaration-tag thread matrix is incomplete")
    if len(summaries) != 1:
        raise EvidenceError("declaration-tag summary is missing or duplicated")
    if len({row["actual_digest"] for row in case_rows.values()}) != 7:
        raise EvidenceError("declaration-tag case digests are not pairwise distinct")
    thread_roots = {row["actual_root"] for row in thread_rows.values()}
    if len(thread_roots) != 1:
        raise EvidenceError("declaration-tag thread roots differ")
    summary = summaries[0]
    canonical_root = require_environment_identity_hex(
        summary.get("canonical_root"), label="declaration-tag canonical root"
    )
    source_order_root = require_environment_identity_hex(
        summary.get("source_order_defect_root"),
        label="declaration-tag source-order defect root",
    )
    omitted_root = require_environment_identity_hex(
        summary.get("omitted_declaration_root"),
        label="declaration-tag omitted-declaration root",
    )
    if (
        summary.get("case_count") != 7
        or summary.get("unique_digest_count") != 7
        or summary.get("pairwise_comparisons") != 21
        or summary.get("expected_pairwise_comparisons") != 21
        or summary.get("thread_matrix") != [1, 8, 32]
        or summary.get("thread_matrix_roots_distinct") != 1
        or thread_roots != {canonical_root}
        or source_order_root == canonical_root
        or omitted_root == canonical_root
        or summary.get("source_order_defect_relation") != "differs"
        or summary.get("omitted_declaration_relation") != "differs"
        or summary.get("named_defects_discriminated")
        != ["cast_after_source_reorder", "omitted_declaration"]
        or summary.get("claim_type") != "bounded_model"
    ):
        raise EvidenceError("declaration-tag summary differs from the strict contract")
    require_environment_identity_count(
        summary.get("elapsed_us"), label="declaration-tag summary elapsed_us"
    )
    return {
        "schema": "fln.validation/1",
        "validator": "declaration-tag-matrix/1",
        "subject": stdout_relative,
        "valid": True,
        "run_id": expected_run_id,
        "observed_exit": observed_exit,
        "records": len(records),
        "case_count": len(case_rows),
        "thread_matrix": [1, 8, 32],
        "stdout_artifact": stdout_relative,
        "stderr_artifact": stderr_relative,
        "stdout_sha256": stdout_digest,
        "stderr_sha256": stderr_digest,
    }


def validate_declaration_membership(
    stdout_path: Path,
    stderr_path: Path,
    expected_run_id: str,
    observed_exit: int,
    *,
    artifact_root: Path,
    expected_stdout_artifact: str,
    expected_stderr_artifact: str,
) -> dict[str, Any]:
    (
        records,
        stdout_relative,
        stderr_relative,
        stdout_digest,
        stderr_digest,
    ) = prepare_environment_identity_validation(
        stdout_path,
        stderr_path,
        artifact_root=artifact_root,
        schema=DECLARATION_MEMBERSHIP_SCHEMA,
        test_name=DECLARATION_MEMBERSHIP_TEST,
        expected_run_id=expected_run_id,
        observed_exit=observed_exit,
        expected_stdout_artifact=expected_stdout_artifact,
        expected_stderr_artifact=expected_stderr_artifact,
        expected_records=41,
    )
    common = {
        "schema",
        "version",
        "run_id",
        "beads",
        "scenario",
        "status",
        "final_state",
    }
    matrix_fields = common | {
        "kind",
        "membership_case",
        "member_count",
        "expected_digest",
        "actual_digest",
        "repeated_digest",
        "digest_relation",
        "repeat_relation",
        "expected_root",
        "actual_root",
        "root_relation",
        "root_propagation",
        "model",
        "elapsed_us",
    }
    defect_fields = common | {
        "kind",
        "canonical_digest",
        "dropped_list_digest",
        "dropped_list_relation",
        "omitted_count_digest",
        "omitted_count_relation",
        "sorted_members_digest",
        "sorted_members_relation",
        "sorted_members_order_collapse",
        "wrong_domain_digest",
        "wrong_domain_relation",
        "real_root",
        "stale_digest_root",
        "root_propagation_relation",
        "named_defects_discriminated",
        "boundary_distinctions",
    }
    summary_fields = common | {
        "kind_count",
        "membership_case_count",
        "matrix_rows",
        "large_member_count",
        "opaque_solo_digest",
        "opaque_grouped_digest",
        "opaque_regression_relation",
        "root_propagation",
        "claim_type",
        "elapsed_us",
    }
    kinds = {"definition", "theorem", "opaque", "inductive", "recursor"}
    member_counts = {
        "empty": 0,
        "singleton": 1,
        "repeated": 2,
        "ordered": 2,
        "reordered": 2,
        "renamed": 2,
        "declared_large": 4096,
    }
    matrix: dict[tuple[str, str], dict[str, Any]] = {}
    defects: dict[str, dict[str, Any]] = {}
    summaries: list[dict[str, Any]] = []
    for number, record in enumerate(records, 1):
        scenario = record.get("scenario")
        label = f"declaration-membership record {number}"
        if scenario == "declaration-membership-matrix":
            require_environment_identity_fields(
                record,
                matrix_fields,
                schema=DECLARATION_MEMBERSHIP_SCHEMA,
                expected_run_id=expected_run_id,
                expected_beads=["fln-amv.1", "fln-amv.14"],
                label=label,
            )
            key = (record.get("kind"), record.get("membership_case"))
            if (
                key[0] not in kinds
                or key[1] not in member_counts
                or key in matrix
            ):
                raise EvidenceError(f"{label} has an unknown or duplicate case")
            expected_digest = require_environment_identity_hex(
                record.get("expected_digest"), label=f"{label} expected digest"
            )
            actual_digest = require_environment_identity_hex(
                record.get("actual_digest"), label=f"{label} actual digest"
            )
            repeated_digest = require_environment_identity_hex(
                record.get("repeated_digest"), label=f"{label} repeated digest"
            )
            expected_root = require_environment_identity_hex(
                record.get("expected_root"), label=f"{label} expected root"
            )
            actual_root = require_environment_identity_hex(
                record.get("actual_root"), label=f"{label} actual root"
            )
            if (
                record.get("member_count") != member_counts[key[1]]
                or expected_digest != actual_digest
                or repeated_digest != actual_digest
                or record.get("digest_relation") != "equal"
                or record.get("repeat_relation") != "equal"
                or expected_root != actual_root
                or record.get("root_relation") != "equal"
                or record.get("root_propagation") != "exact"
                or record.get("model") != "independent-canonical-membership-v1"
            ):
                raise EvidenceError(f"{label} relation differs")
            require_environment_identity_count(
                record.get("elapsed_us"), label=f"{label} elapsed_us"
            )
            matrix[key] = record
        elif scenario == "declaration-membership-defects":
            require_environment_identity_fields(
                record,
                defect_fields,
                schema=DECLARATION_MEMBERSHIP_SCHEMA,
                expected_run_id=expected_run_id,
                expected_beads=["fln-amv.1", "fln-amv.14"],
                label=label,
            )
            kind = record.get("kind")
            if kind not in kinds or kind in defects:
                raise EvidenceError(f"{label} has an unknown or duplicate kind")
            defects[kind] = record
        elif scenario == "declaration-membership-summary":
            require_environment_identity_fields(
                record,
                summary_fields,
                schema=DECLARATION_MEMBERSHIP_SCHEMA,
                expected_run_id=expected_run_id,
                expected_beads=["fln-amv.1", "fln-amv.14"],
                label=label,
            )
            summaries.append(record)
        else:
            raise EvidenceError(f"{label} has an unknown scenario")
    expected_matrix = {
        (kind, membership_case)
        for kind in kinds
        for membership_case in member_counts
    }
    if set(matrix) != expected_matrix:
        raise EvidenceError("declaration-membership matrix is incomplete")
    if set(defects) != kinds or len(summaries) != 1:
        raise EvidenceError("declaration-membership defect or summary rows are incomplete")
    for kind in kinds:
        rows = {
            membership_case: matrix[(kind, membership_case)]
            for membership_case in member_counts
        }
        if len({row["actual_digest"] for row in rows.values()}) != 7:
            raise EvidenceError(
                f"declaration-membership {kind} boundary digests alias"
            )
        defect = defects[kind]
        digests = {
            field: require_environment_identity_hex(
                defect.get(field), label=f"declaration-membership {kind} {field}"
            )
            for field in (
                "canonical_digest",
                "dropped_list_digest",
                "omitted_count_digest",
                "sorted_members_digest",
                "wrong_domain_digest",
            )
        }
        real_root = require_environment_identity_hex(
            defect.get("real_root"), label=f"declaration-membership {kind} real root"
        )
        stale_root = require_environment_identity_hex(
            defect.get("stale_digest_root"),
            label=f"declaration-membership {kind} stale root",
        )
        canonical = rows["ordered"]["actual_digest"]
        reordered = rows["reordered"]["actual_digest"]
        if (
            digests["canonical_digest"] != canonical
            or digests["dropped_list_digest"] == canonical
            or digests["omitted_count_digest"] == canonical
            or digests["wrong_domain_digest"] == canonical
            or digests["sorted_members_digest"] != canonical
            or digests["sorted_members_digest"] == reordered
            or real_root != rows["ordered"]["actual_root"]
            or stale_root == real_root
            or defect.get("dropped_list_relation") != "differs"
            or defect.get("omitted_count_relation") != "differs"
            or defect.get("sorted_members_relation") != "differs"
            or defect.get("sorted_members_order_collapse") is not True
            or defect.get("wrong_domain_relation") != "differs"
            or defect.get("root_propagation_relation") != "differs"
            or defect.get("named_defects_discriminated")
            != [
                "dropped_list",
                "omitted_count",
                "reordered_membership",
                "wrong_domain",
                "failed_root_propagation",
            ]
            or defect.get("boundary_distinctions") != 7
        ):
            raise EvidenceError(
                f"declaration-membership {kind} defect contract differs"
            )
    summary = summaries[0]
    opaque_solo = require_environment_identity_hex(
        summary.get("opaque_solo_digest"),
        label="declaration-membership opaque solo digest",
    )
    opaque_grouped = require_environment_identity_hex(
        summary.get("opaque_grouped_digest"),
        label="declaration-membership opaque grouped digest",
    )
    if (
        summary.get("kind_count") != 5
        or summary.get("membership_case_count") != 7
        or summary.get("matrix_rows") != 40
        or summary.get("large_member_count") != 4096
        or opaque_solo != matrix[("opaque", "singleton")]["actual_digest"]
        or opaque_grouped != matrix[("opaque", "ordered")]["actual_digest"]
        or opaque_solo == opaque_grouped
        or summary.get("opaque_regression_relation") != "differs"
        or summary.get("root_propagation") != "exact"
        or summary.get("claim_type") != "bounded_model"
    ):
        raise EvidenceError(
            "declaration-membership summary differs from the strict contract"
        )
    require_environment_identity_count(
        summary.get("elapsed_us"),
        label="declaration-membership summary elapsed_us",
    )
    return {
        "schema": "fln.validation/1",
        "validator": "declaration-membership/1",
        "subject": stdout_relative,
        "valid": True,
        "run_id": expected_run_id,
        "observed_exit": observed_exit,
        "records": len(records),
        "matrix_rows": len(matrix),
        "defect_rows": len(defects),
        "stdout_artifact": stdout_relative,
        "stderr_artifact": stderr_relative,
        "stdout_sha256": stdout_digest,
        "stderr_sha256": stderr_digest,
    }


def validate_extension_descriptor_matrix(
    stdout_path: Path,
    stderr_path: Path,
    expected_run_id: str,
    observed_exit: int,
    *,
    artifact_root: Path,
    expected_stdout_artifact: str,
    expected_stderr_artifact: str,
) -> dict[str, Any]:
    (
        records,
        stdout_relative,
        stderr_relative,
        stdout_digest,
        stderr_digest,
    ) = prepare_environment_identity_validation(
        stdout_path,
        stderr_path,
        artifact_root=artifact_root,
        schema=EXTENSION_DESCRIPTOR_MATRIX_SCHEMA,
        test_name=EXTENSION_DESCRIPTOR_MATRIX_TEST,
        expected_run_id=expected_run_id,
        observed_exit=observed_exit,
        expected_stdout_artifact=expected_stdout_artifact,
        expected_stderr_artifact=expected_stderr_artifact,
        expected_records=25,
    )
    common = {
        "schema",
        "version",
        "run_id",
        "beads",
        "scenario",
        "status",
        "final_state",
    }
    matrix_fields = common | {
        "merge",
        "merge_tag",
        "checkpoint",
        "checkpoint_tag",
        "provenance",
        "provenance_tag",
        "descriptor_position",
        "journal_entries",
        "expected_digest",
        "actual_digest",
        "repeated_digest",
        "digest_relation",
        "repeat_relation",
        "expected_root",
        "actual_root",
        "root_relation",
        "root_propagation",
        "model",
        "elapsed_us",
    }
    defect_fields = common | {
        "merge",
        "checkpoint",
        "provenance",
        "canonical_digest",
        "omit_merge_digest",
        "omit_merge_relation",
        "omit_checkpoint_digest",
        "omit_checkpoint_relation",
        "omit_provenance_digest",
        "omit_provenance_relation",
        "swapped_tag_digest",
        "swapped_tag_relation",
        "swapped_tag_discriminating",
        "swapped_field_digest",
        "swapped_field_relation",
        "swapped_field_discriminating",
        "debug_text_digest",
        "debug_text_relation",
        "after_journal_digest",
        "after_journal_relation",
        "named_defects_discriminated",
    }
    summary_fields = common | {
        "combination_count",
        "merge_variants",
        "checkpoint_variants",
        "provenance_variants",
        "distinct_delta_digests",
        "distinct_logical_roots",
        "descriptor_position",
        "matrix_rows",
        "root_propagation",
        "claim_type",
        "elapsed_us",
    }
    merge_tags = {
        "append_ordered": 0,
        "set_union": 1,
        "conflicts_require_review": 2,
    }
    checkpoint_tags = {"journal_suffix": 0, "full_journal": 1}
    provenance_tags = {"understood": 0, "opaque": 1}
    matrix: dict[tuple[str, str, str], dict[str, Any]] = {}
    defects: dict[tuple[str, str, str], dict[str, Any]] = {}
    summaries: list[dict[str, Any]] = []
    for number, record in enumerate(records, 1):
        scenario = record.get("scenario")
        label = f"extension-descriptor record {number}"
        if scenario == "extension-descriptor-matrix":
            require_environment_identity_fields(
                record,
                matrix_fields,
                schema=EXTENSION_DESCRIPTOR_MATRIX_SCHEMA,
                expected_run_id=expected_run_id,
                expected_beads=["fln-amv.2", "fln-amv.14"],
                label=label,
            )
            key = (
                record.get("merge"),
                record.get("checkpoint"),
                record.get("provenance"),
            )
            if (
                key[0] not in merge_tags
                or key[1] not in checkpoint_tags
                or key[2] not in provenance_tags
                or key in matrix
            ):
                raise EvidenceError(f"{label} has an unknown or duplicate case")
            expected_digest = require_environment_identity_hex(
                record.get("expected_digest"), label=f"{label} expected digest"
            )
            actual_digest = require_environment_identity_hex(
                record.get("actual_digest"), label=f"{label} actual digest"
            )
            repeated_digest = require_environment_identity_hex(
                record.get("repeated_digest"), label=f"{label} repeated digest"
            )
            expected_root = require_environment_identity_hex(
                record.get("expected_root"), label=f"{label} expected root"
            )
            actual_root = require_environment_identity_hex(
                record.get("actual_root"), label=f"{label} actual root"
            )
            if (
                record.get("merge_tag") != merge_tags[key[0]]
                or record.get("checkpoint_tag") != checkpoint_tags[key[1]]
                or record.get("provenance_tag") != provenance_tags[key[2]]
                or record.get("descriptor_position") != "before_journal"
                or record.get("journal_entries") != 2
                or expected_digest != actual_digest
                or repeated_digest != actual_digest
                or record.get("digest_relation") != "equal"
                or record.get("repeat_relation") != "equal"
                or expected_root != actual_root
                or record.get("root_relation") != "equal"
                or record.get("root_propagation") != "exact"
                or record.get("model") != "independent-descriptor-layout-v1"
            ):
                raise EvidenceError(f"{label} relation differs")
            require_environment_identity_count(
                record.get("elapsed_us"), label=f"{label} elapsed_us"
            )
            matrix[key] = record
        elif scenario == "extension-descriptor-defects":
            require_environment_identity_fields(
                record,
                defect_fields,
                schema=EXTENSION_DESCRIPTOR_MATRIX_SCHEMA,
                expected_run_id=expected_run_id,
                expected_beads=["fln-amv.2", "fln-amv.14"],
                label=label,
            )
            key = (
                record.get("merge"),
                record.get("checkpoint"),
                record.get("provenance"),
            )
            if (
                key[0] not in merge_tags
                or key[1] not in checkpoint_tags
                or key[2] not in provenance_tags
                or key in defects
            ):
                raise EvidenceError(f"{label} has an unknown or duplicate case")
            defects[key] = record
        elif scenario == "extension-descriptor-summary":
            require_environment_identity_fields(
                record,
                summary_fields,
                schema=EXTENSION_DESCRIPTOR_MATRIX_SCHEMA,
                expected_run_id=expected_run_id,
                expected_beads=["fln-amv.2", "fln-amv.14"],
                label=label,
            )
            summaries.append(record)
        else:
            raise EvidenceError(f"{label} has an unknown scenario")
    expected_matrix = {
        (merge, checkpoint, provenance)
        for merge in merge_tags
        for checkpoint in checkpoint_tags
        for provenance in provenance_tags
    }
    if set(matrix) != expected_matrix or set(defects) != expected_matrix:
        raise EvidenceError("extension-descriptor matrix is incomplete")
    if len(summaries) != 1:
        raise EvidenceError("extension-descriptor summary is missing or duplicated")
    if len({row["actual_digest"] for row in matrix.values()}) != 12:
        raise EvidenceError("extension-descriptor delta digests alias")
    if len({row["actual_root"] for row in matrix.values()}) != 12:
        raise EvidenceError("extension-descriptor logical roots alias")
    for key, row in matrix.items():
        defect = defects[key]
        canonical = row["actual_digest"]
        digest_fields = (
            "canonical_digest",
            "omit_merge_digest",
            "omit_checkpoint_digest",
            "omit_provenance_digest",
            "swapped_tag_digest",
            "swapped_field_digest",
            "debug_text_digest",
            "after_journal_digest",
        )
        digests = {
            field: require_environment_identity_hex(
                defect.get(field),
                label=f"extension-descriptor {'/'.join(key)} {field}",
            )
            for field in digest_fields
        }
        tag_discriminating = key[0] != "conflicts_require_review"
        field_discriminating = merge_tags[key[0]] != checkpoint_tags[key[1]]
        expected_tag_relation = (
            "differs" if tag_discriminating else "equal_by_construction"
        )
        expected_field_relation = (
            "differs" if field_discriminating else "equal_by_construction"
        )
        if (
            digests["canonical_digest"] != canonical
            or any(
                digests[field] == canonical
                for field in (
                    "omit_merge_digest",
                    "omit_checkpoint_digest",
                    "omit_provenance_digest",
                    "debug_text_digest",
                    "after_journal_digest",
                )
            )
            or (digests["swapped_tag_digest"] != canonical) != tag_discriminating
            or (digests["swapped_field_digest"] != canonical)
            != field_discriminating
            or defect.get("omit_merge_relation") != "differs"
            or defect.get("omit_checkpoint_relation") != "differs"
            or defect.get("omit_provenance_relation") != "differs"
            or defect.get("swapped_tag_relation") != expected_tag_relation
            or defect.get("swapped_tag_discriminating") is not tag_discriminating
            or defect.get("swapped_field_relation") != expected_field_relation
            or defect.get("swapped_field_discriminating")
            is not field_discriminating
            or defect.get("debug_text_relation") != "differs"
            or defect.get("after_journal_relation") != "differs"
            or defect.get("named_defects_discriminated")
            != ["omitted_dimension", "swapped_tag", "debug_text", "after_journal"]
        ):
            raise EvidenceError(
                f"extension-descriptor {'/'.join(key)} defect contract differs"
            )
    summary = summaries[0]
    if (
        summary.get("combination_count") != 12
        or summary.get("merge_variants") != 3
        or summary.get("checkpoint_variants") != 2
        or summary.get("provenance_variants") != 2
        or summary.get("distinct_delta_digests") != 12
        or summary.get("distinct_logical_roots") != 12
        or summary.get("descriptor_position") != "before_journal"
        or summary.get("matrix_rows") != 24
        or summary.get("root_propagation") != "exact"
        or summary.get("claim_type") != "bounded_model"
    ):
        raise EvidenceError(
            "extension-descriptor summary differs from the strict contract"
        )
    require_environment_identity_count(
        summary.get("elapsed_us"), label="extension-descriptor summary elapsed_us"
    )
    return {
        "schema": "fln.validation/1",
        "validator": "extension-descriptor-matrix/1",
        "subject": stdout_relative,
        "valid": True,
        "run_id": expected_run_id,
        "observed_exit": observed_exit,
        "records": len(records),
        "combination_count": len(matrix),
        "defect_rows": len(defects),
        "stdout_artifact": stdout_relative,
        "stderr_artifact": stderr_relative,
        "stdout_sha256": stdout_digest,
        "stderr_sha256": stderr_digest,
    }


def validate_environment_state(
    stdout_path: Path,
    stderr_path: Path,
    expected_run_id: str,
    observed_exit: int,
    *,
    artifact_root: Path,
    expected_stdout_artifact: str,
    expected_stderr_artifact: str,
) -> dict[str, Any]:
    """Validate the exact checkpoint/history evidence contract (bead 41s).

    A schema prefix and record count cannot distinguish a duplicated scenario,
    two interleaved runs, a transposed record, or a checkpoint rebound to the
    wrong base. This validator binds the four real producer rows, their order,
    their typed final states, and the identities shared across those rows.
    """
    (
        records,
        stdout_relative,
        stderr_relative,
        stdout_digest,
        stderr_digest,
    ) = prepare_environment_identity_validation(
        stdout_path,
        stderr_path,
        artifact_root=artifact_root,
        schema=ENVIRONMENT_STATE_SCHEMA,
        test_name=ENVIRONMENT_STATE_TEST,
        expected_run_id=expected_run_id,
        observed_exit=observed_exit,
        expected_stdout_artifact=expected_stdout_artifact,
        expected_stderr_artifact=expected_stderr_artifact,
        expected_records=4,
    )
    common = {
        "schema",
        "version",
        "run_id",
        "beads",
        "scenario",
        "status",
        "elapsed_us",
        "final_state",
    }
    persistent_fields = common | {
        "entry_count",
        "chunk_capacity",
        "chunk_count",
        "node_count",
        "shared_node_count",
        "fresh_node_count",
        "append_operations",
        "replay_operations",
        "node_allocations",
        "copied_child_slots",
        "copied_entry_slots",
        "payload_bytes",
        "expected_order_hash",
        "actual_order_hash",
        "expected_root",
        "actual_root",
        "snapshot_root",
    }
    checkpoint_fields = common | {
        "mode",
        "base_id",
        "checkpoint_id",
        "restored_id",
        "base_root",
        "checkpoint_base_root",
        "expected_root",
        "actual_root",
        "base_entries",
        "checkpoint_entries",
        "restored_entries",
        "payload_bytes",
        "prefix_lookup_steps",
        "capture_operations",
        "restore_operations",
        "entry_limit",
        "payload_byte_limit",
        "expected_outcome",
        "actual_outcome",
    }
    recovery_fields = common | {
        "mode",
        "base_id",
        "checkpoint_id",
        "restored_id",
        "base_root_before",
        "base_root_after",
        "expected_root",
        "actual_root",
        "base_entries",
        "checkpoint_entries",
        "restored_entries",
        "entry_limit",
        "payload_byte_limit",
        "expected_outcome",
        "actual_outcome",
        "recovery_outcome",
    }
    expected_keys = [
        ("persistent-journal", None),
        ("checkpoint-roundtrip", "journal_suffix"),
        ("checkpoint-roundtrip", "full_journal"),
        ("checkpoint-negative-recovery", "journal_suffix"),
    ]
    actual_keys = [
        (record.get("scenario"), record.get("mode")) for record in records
    ]
    if actual_keys != expected_keys:
        raise EvidenceError(
            "environment-state scenario order or identity differs: "
            f"{actual_keys!r}"
        )

    persistent, suffix, full, recovery = records
    require_environment_identity_fields(
        persistent,
        persistent_fields,
        schema=ENVIRONMENT_STATE_SCHEMA,
        expected_run_id=expected_run_id,
        expected_beads=["fln-amv.5", "fln-amv.7"],
        label="environment-state persistent-journal",
    )
    for label, record in (
        ("journal-suffix", suffix),
        ("full-journal", full),
    ):
        require_environment_identity_fields(
            record,
            checkpoint_fields,
            schema=ENVIRONMENT_STATE_SCHEMA,
            expected_run_id=expected_run_id,
            expected_beads=["fln-amv.7"],
            label=f"environment-state {label}",
        )
    require_environment_identity_fields(
        recovery,
        recovery_fields,
        schema=ENVIRONMENT_STATE_SCHEMA,
        expected_run_id=expected_run_id,
        expected_beads=["fln-amv.7"],
        label="environment-state negative-recovery",
        expected_final_state="clean_recovery",
    )

    stable_contracts: list[tuple[str, dict[str, Any], dict[str, Any]]] = [
        (
            "persistent-journal",
            persistent,
            {
                "entry_count": 69,
                "chunk_capacity": 32,
                "chunk_count": 3,
                "node_count": 4,
                "shared_node_count": 2,
                "fresh_node_count": 2,
                "append_operations": 69,
                "replay_operations": 69,
                "node_allocations": 106,
                "copied_child_slots": 77,
                "copied_entry_slots": 1002,
                "payload_bytes": 552,
                "expected_order_hash": "8ac9a67f1111de29",
                "actual_order_hash": "8ac9a67f1111de29",
                "expected_root": (
                    "cffbec6eac072caa55a121f4e21f4bc6"
                    "ac9c13bb324470a8f8ff8ba04ab797f9"
                ),
                "actual_root": (
                    "cffbec6eac072caa55a121f4e21f4bc6"
                    "ac9c13bb324470a8f8ff8ba04ab797f9"
                ),
                "snapshot_root": (
                    "8f1976245ae9dce33f3eb0d3febd2bc"
                    "32e2b5f1f88710c7aa579b80b0c1705ab"
                ),
            },
        ),
        (
            "journal-suffix",
            suffix,
            {
                "mode": "journal_suffix",
                "base_id": (
                    "a9c5fd7d6f4e70ce4c0a6cd3f90c9355"
                    "46bcc9c5ff573f4f9d93997677d632ee"
                ),
                "checkpoint_id": "v1-suffix-5-7567db5a9df19e29",
                "restored_id": (
                    "8d00a22b42354950b09dc8f2e927c523"
                    "7dc7357cbd2bec7985fff5770b753972"
                ),
                "base_root": (
                    "8f1976245ae9dce33f3eb0d3febd2bc"
                    "32e2b5f1f88710c7aa579b80b0c1705ab"
                ),
                "checkpoint_base_root": (
                    "a9c5fd7d6f4e70ce4c0a6cd3f90c9355"
                    "46bcc9c5ff573f4f9d93997677d632ee"
                ),
                "expected_root": (
                    "cffbec6eac072caa55a121f4e21f4bc6"
                    "ac9c13bb324470a8f8ff8ba04ab797f9"
                ),
                "actual_root": (
                    "cffbec6eac072caa55a121f4e21f4bc6"
                    "ac9c13bb324470a8f8ff8ba04ab797f9"
                ),
                "base_entries": 64,
                "checkpoint_entries": 5,
                "restored_entries": 69,
                "payload_bytes": 40,
                "prefix_lookup_steps": 2,
                "capture_operations": 5,
                "restore_operations": 5,
                "entry_limit": 1000,
                "payload_byte_limit": 64000,
                "expected_outcome": "restored",
                "actual_outcome": "restored",
            },
        ),
        (
            "full-journal",
            full,
            {
                "mode": "full_journal",
                "base_id": None,
                "checkpoint_id": "v1-full-37-38b8cd0e43c2cb09",
                "restored_id": (
                    "56b471fc08e0aaf91410cb01467c5a865"
                    "23f6cfb0efd037c782c61818c6c988b"
                ),
                "base_root": None,
                "checkpoint_base_root": None,
                "expected_root": (
                    "0af8c87b8a15bb34bc78108eadf4f6b0"
                    "640051ba9678536bd17645d11263c131"
                ),
                "actual_root": (
                    "0af8c87b8a15bb34bc78108eadf4f6b0"
                    "640051ba9678536bd17645d11263c131"
                ),
                "base_entries": 0,
                "checkpoint_entries": 37,
                "restored_entries": 37,
                "payload_bytes": 296,
                "prefix_lookup_steps": 0,
                "capture_operations": 37,
                "restore_operations": 37,
                "entry_limit": 1000,
                "payload_byte_limit": 64000,
                "expected_outcome": "restored",
                "actual_outcome": "restored",
            },
        ),
        (
            "negative-recovery",
            recovery,
            {
                "mode": "journal_suffix",
                "base_id": (
                    "c0f8dd130cf1f9eccd9dd575a0ee9ddd"
                    "75654c7afd999ffcfbb1bb557ca2f203"
                ),
                "checkpoint_id": "v1-suffix-5-7567db5a9df19e29",
                "restored_id": (
                    "8d00a22b42354950b09dc8f2e927c523"
                    "7dc7357cbd2bec7985fff5770b753972"
                ),
                "base_root_before": (
                    "525e3fa4730a11ab0cbc6c56d10282c3"
                    "80cd0b043751888bb15174fd17df5bbc"
                ),
                "base_root_after": (
                    "525e3fa4730a11ab0cbc6c56d10282c3"
                    "80cd0b043751888bb15174fd17df5bbc"
                ),
                "expected_root": (
                    "cffbec6eac072caa55a121f4e21f4bc6"
                    "ac9c13bb324470a8f8ff8ba04ab797f9"
                ),
                "actual_root": (
                    "cffbec6eac072caa55a121f4e21f4bc6"
                    "ac9c13bb324470a8f8ff8ba04ab797f9"
                ),
                "base_entries": 64,
                "checkpoint_entries": 5,
                "restored_entries": 69,
                "entry_limit": 1000,
                "payload_byte_limit": 64000,
                "expected_outcome": "base_history_mismatch",
                "actual_outcome": "base_history_mismatch",
                "recovery_outcome": "restored",
            },
        ),
    ]
    for label, record, expected in stable_contracts:
        for field, expected_value in expected.items():
            if record.get(field) != expected_value:
                raise EvidenceError(
                    f"environment-state {label} {field} differs: "
                    f"{record.get(field)!r}"
                )
        require_environment_identity_count(
            record.get("elapsed_us"),
            label=f"environment-state {label} elapsed_us",
        )

    if (
        suffix["base_id"] != suffix["checkpoint_base_root"]
        or suffix["base_root"] != persistent["snapshot_root"]
        or suffix["expected_root"] != persistent["actual_root"]
        or suffix["actual_root"] != persistent["actual_root"]
    ):
        raise EvidenceError(
            "environment-state suffix checkpoint is rebound to another base or root"
        )
    if (
        recovery["checkpoint_id"] != suffix["checkpoint_id"]
        or recovery["restored_id"] != suffix["restored_id"]
        or recovery["expected_root"] != suffix["expected_root"]
        or recovery["actual_root"] != suffix["actual_root"]
        or recovery["base_root_before"] != recovery["base_root_after"]
    ):
        raise EvidenceError(
            "environment-state refusal/recovery is stale or uses another checkpoint"
        )

    return {
        "schema": "fln.validation/1",
        "validator": "environment-state/1",
        "subject": stdout_relative,
        "valid": True,
        "run_id": expected_run_id,
        "observed_exit": observed_exit,
        "records": len(records),
        "record_keys": [
            scenario if mode is None else f"{scenario}/{mode}"
            for scenario, mode in expected_keys
        ],
        "checkpoint_id": suffix["checkpoint_id"],
        "logical_root": persistent["actual_root"],
        "stdout_artifact": stdout_relative,
        "stderr_artifact": stderr_relative,
        "stdout_sha256": stdout_digest,
        "stderr_sha256": stderr_digest,
    }


def validate_declaration_admission(
    stdout_path: Path,
    stderr_path: Path,
    expected_run_id: str,
    observed_exit: int,
    *,
    artifact_root: Path,
    expected_stdout_artifact: str,
    expected_stderr_artifact: str,
) -> dict[str, Any]:
    """Validate j8h's exact real declaration-admission evidence contract.

    The producer deliberately reports seven budgeted limits while distinguishing
    the five locally measured DeclarationDimensions from the two limits delegated
    to term-weight preflight. This validator binds both sets, their order, typed
    outcomes, publication authority, exact roots, and recovery identities.
    """
    (
        records,
        stdout_relative,
        stderr_relative,
        stdout_digest,
        stderr_digest,
    ) = prepare_environment_identity_validation(
        stdout_path,
        stderr_path,
        artifact_root=artifact_root,
        schema=DECLARATION_ADMISSION_SCHEMA,
        additional_schemas=(DECLARATION_ADMISSION_SUMMARY_SCHEMA,),
        test_name=DECLARATION_ADMISSION_TEST,
        expected_run_id=expected_run_id,
        observed_exit=observed_exit,
        expected_stdout_artifact=expected_stdout_artifact,
        expected_stderr_artifact=expected_stderr_artifact,
        expected_records=19,
    )
    envelope = {
        "schema",
        "version",
        "run_id",
        "bead",
        "claim_id",
        "claim_type",
        "invariant_id",
        "invariant_relation",
        "gate_id",
        "gate_relation",
        "parity_ledger_row",
        "data_grade",
        "epoch",
        "mode",
        "profile",
        "platform",
        "cache_state",
        "canonical_input_root",
        "cwd",
        "argv",
        "stdout_artifact",
        "stderr_artifact",
        "timing_used_as_gate",
    }
    detail = envelope | {
        "scenario",
        "step",
        "step_index",
        "declaration",
        "status",
        "cleanup_status",
        "final_state",
    }
    publication = {
        "base_root",
        "published_root",
        "authoritative",
        "published",
        "cacheable",
        "expected_outcome",
        "actual_outcome",
        "first_divergence",
    }
    admitted_fields = detail | publication | {
        "budget",
        "usage",
        "canonical_digest",
        "limit_name",
        "allowed",
        "observed",
        "structural_unit",
    }
    refusal_fields = admitted_fields | {
        "is_declaration_dimension",
        "measured_by",
        "progress",
    }
    cancellation_fields = detail | publication | {"checkpoint"}
    superseded_fields = detail | publication | {
        "plan_base_root",
        "commit_target_root",
    }
    recovery_fields = detail | publication | {
        "budget",
        "usage",
        "canonical_digest",
        "limit_name",
    }
    summary_fields = envelope | {
        "scenario",
        "steps",
        "admitted_rows",
        "refusal_rows",
        "cancellation_rows",
        "superseded_rows",
        "recovery_rows",
        "declaration_dimension_rows",
        "delegated_limit_rows",
        "status",
        "cleanup_status",
        "final_state",
    }

    def require_row(
        record: dict[str, Any],
        expected_fields: set[str],
        *,
        schema: str,
        label: str,
    ) -> None:
        if set(record) != expected_fields:
            missing = sorted(expected_fields - set(record))
            extra = sorted(set(record) - expected_fields)
            raise EvidenceError(
                f"declaration-admission {label} field mismatch: "
                f"missing={missing!r} extra={extra!r}"
            )
        cwd = record.get("cwd")
        if (
            not isinstance(cwd, str)
            or not Path(cwd).is_absolute()
            or Path(cwd).parts[-2:] != ("crates", "fln-env")
        ):
            raise EvidenceError(
                f"declaration-admission {label} cwd is not the fln-env crate"
            )
        if (
            record.get("schema") != schema
            or record.get("version") != 1
            or record.get("run_id") != expected_run_id
            or record.get("bead") != "franken_lean-j8h"
            or record.get("claim_id")
            != "franken_lean-j8h-declaration-admission-resource-bounds"
            or record.get("claim_type") != "bounded_model"
            or record.get("invariant_id") != "FL-INV-07"
            or record.get("invariant_relation")
            != "inconclusive-is-not-rejected"
            or record.get("gate_id") != "W2"
            or record.get("gate_relation") != "partial-component-evidence"
            or record.get("parity_ledger_row")
            != "not_applicable_internal_declaration_admission"
            or record.get("data_grade") != "verified"
            or record.get("epoch") != "lean-v4.32.0"
            or record.get("mode") != "sound"
            or record.get("profile") != "e2e"
            or record.get("platform") != "linux-x86_64"
            or record.get("cache_state") != "uncontrolled"
            or record.get("canonical_input_root")
            != DECLARATION_ADMISSION_INPUT_ROOT
            or record.get("argv") != [DECLARATION_ADMISSION_ARGV]
            or record.get("stdout_artifact") != expected_stdout_artifact
            or record.get("stderr_artifact") != expected_stderr_artifact
            or record.get("timing_used_as_gate") is not False
            or record.get("status") != "pass"
        ):
            raise EvidenceError(
                f"declaration-admission {label} shared envelope differs"
            )

    expected_order = [
        (0, "admitted-transaction", "admitted"),
        *[
            (index, "limit-refusal", f"refusal-{row[0]}")
            for index, row in enumerate(DECLARATION_ADMISSION_REFUSALS, 1)
        ],
        (8, "cancellation", "cancel-before-expression"),
        (9, "cancellation", "cancel-before-publication"),
        (10, "superseded-plan", "superseded-nonpublication"),
        *[
            (index, "adequate-budget-recovery", f"recovery-{row[0]}")
            for index, row in enumerate(DECLARATION_ADMISSION_RECOVERIES, 11)
        ],
        (None, "declaration-admission-real-path", None),
    ]
    actual_order = [
        (record.get("step_index"), record.get("scenario"), record.get("step"))
        for record in records
    ]
    if actual_order != expected_order:
        raise EvidenceError(
            "declaration-admission scenario or step order differs: "
            f"{actual_order!r}"
        )

    admitted = records[0]
    require_row(
        admitted,
        admitted_fields,
        schema=DECLARATION_ADMISSION_SCHEMA,
        label="admitted",
    )
    admitted_usage = {
        "level_params": 2,
        "mutual_rows": 0,
        "constructor_rows": 0,
        "recursor_rules": 0,
        "canonical_bytes": 87,
        "expressions": 1,
        "expr_nodes": 1,
        "expanded_weight": 1,
        "max_logical_depth": 1,
    }
    if (
        admitted.get("declaration") != "Admitted"
        or admitted.get("budget") != DECLARATION_ADMISSION_UNBOUNDED_BUDGET
        or admitted.get("usage") != admitted_usage
        or admitted.get("canonical_digest")
        != "8de3ad5e3cb6525929228ad73fea85aa71b4685d32a4b647599c7e9e31f80291"
        or admitted.get("base_root") != DECLARATION_ADMISSION_BASE_ROOT
        or admitted.get("published_root")
        != "4b6ce45719dce319af9c2bf24b3c12bf012e194b49952173f35a9563690d6abf"
        or admitted.get("authoritative") is not True
        or admitted.get("published") is not True
        or admitted.get("cacheable") is not True
        or admitted.get("expected_outcome") != "admitted"
        or admitted.get("actual_outcome") != "admitted"
        or any(
            admitted.get(field) is not None
            for field in (
                "limit_name",
                "allowed",
                "observed",
                "structural_unit",
                "first_divergence",
            )
        )
        or admitted.get("cleanup_status") != "not_applicable"
        or admitted.get("final_state")
        != "declaration-published-and-base-unchanged"
    ):
        raise EvidenceError("declaration-admission admitted transaction differs")
    for field in ("canonical_digest", "base_root", "published_root"):
        require_environment_identity_hex(
            admitted[field], label=f"declaration-admission admitted {field}"
        )

    refusals = records[1:8]
    for offset, (record, expected) in enumerate(
        zip(refusals, DECLARATION_ADMISSION_REFUSALS, strict=True)
    ):
        (
            limit_name,
            is_dimension,
            measured_by,
            observed,
            structural_unit,
            progress,
        ) = expected
        require_row(
            record,
            refusal_fields,
            schema=DECLARATION_ADMISSION_SCHEMA,
            label=f"refusal-{limit_name}",
        )
        budget = dict(DECLARATION_ADMISSION_UNBOUNDED_BUDGET)
        budget[f"max_{limit_name}"] = 0
        if (
            record.get("declaration") != f"Refused{offset}"
            or record.get("limit_name") != limit_name
            or record.get("is_declaration_dimension") is not is_dimension
            or record.get("measured_by") != measured_by
            or record.get("allowed") != 0
            or record.get("observed") != observed
            or record.get("structural_unit") != structural_unit
            or record.get("progress") != progress
            or record.get("budget") != budget
            or record.get("usage") is not None
            or record.get("canonical_digest") is not None
            or record.get("base_root") != DECLARATION_ADMISSION_BASE_ROOT
            or record.get("published_root") is not None
            or record.get("authoritative") is not False
            or record.get("published") is not False
            or record.get("cacheable") is not False
            or record.get("expected_outcome")
            != "inconclusive-resource-exhausted"
            or record.get("actual_outcome")
            != "inconclusive-resource-exhausted"
            or record.get("first_divergence") is not None
            or record.get("cleanup_status") != "not_applicable"
            or record.get("final_state")
            != "nothing-published-and-base-unchanged"
        ):
            raise EvidenceError(
                f"declaration-admission refusal {limit_name} differs"
            )
        if not isinstance(record["observed"], int) or (
            isinstance(record["observed"], bool)
            or record["observed"] <= record["allowed"]
        ):
            raise EvidenceError(
                f"declaration-admission refusal {limit_name} is not exhaustion"
            )

    cancellations = records[8:10]
    for record, step, checkpoint in (
        (
            cancellations[0],
            "cancel-before-expression",
            "before-expression/0",
        ),
        (
            cancellations[1],
            "cancel-before-publication",
            "before-publication",
        ),
    ):
        require_row(
            record,
            cancellation_fields,
            schema=DECLARATION_ADMISSION_SCHEMA,
            label=step,
        )
        if (
            record.get("declaration") != "Cancelled"
            or record.get("checkpoint") != checkpoint
            or record.get("base_root") != DECLARATION_ADMISSION_BASE_ROOT
            or record.get("published_root") is not None
            or record.get("authoritative") is not False
            or record.get("published") is not False
            or record.get("cacheable") is not False
            or record.get("expected_outcome") != "inconclusive-cancelled"
            or record.get("actual_outcome") != "inconclusive-cancelled"
            or record.get("first_divergence") is not None
            or record.get("cleanup_status") != "not_applicable"
            or record.get("final_state")
            != "nothing-published-and-base-unchanged"
        ):
            raise EvidenceError(
                f"declaration-admission cancellation {step} differs"
            )

    superseded = records[10]
    require_row(
        superseded,
        superseded_fields,
        schema=DECLARATION_ADMISSION_SCHEMA,
        label="superseded-plan",
    )
    if (
        superseded.get("declaration") != "Stale"
        or superseded.get("plan_base_root") != DECLARATION_ADMISSION_BASE_ROOT
        or superseded.get("commit_target_root") != admitted["published_root"]
        or superseded.get("base_root") != admitted["published_root"]
        or superseded.get("published_root") is not None
        or superseded.get("authoritative") is not False
        or superseded.get("published") is not False
        or superseded.get("cacheable") is not False
        or superseded.get("expected_outcome")
        != "inconclusive-authority-incomplete"
        or superseded.get("actual_outcome")
        != "inconclusive-authority-incomplete"
        or superseded.get("first_divergence")
        != "plan-base-differs-from-commit-target"
        or superseded.get("cleanup_status") != "not_applicable"
        or superseded.get("final_state")
        != "nothing-published-and-target-unchanged"
    ):
        raise EvidenceError("declaration-admission superseded-plan row differs")

    recoveries = records[11:18]
    recovery_digests: set[str] = set()
    recovery_roots: set[str] = set()
    for offset, (record, expected) in enumerate(
        zip(recoveries, DECLARATION_ADMISSION_RECOVERIES, strict=True)
    ):
        limit_name, usage, digest, published_root = expected
        require_row(
            record,
            recovery_fields,
            schema=DECLARATION_ADMISSION_SCHEMA,
            label=f"recovery-{limit_name}",
        )
        if (
            record.get("declaration") != f"Recovered{offset}"
            or record.get("limit_name") != limit_name
            or record.get("budget") != DECLARATION_ADMISSION_UNBOUNDED_BUDGET
            or record.get("usage") != usage
            or record.get("canonical_digest") != digest
            or record.get("base_root") != DECLARATION_ADMISSION_BASE_ROOT
            or record.get("published_root") != published_root
            or record.get("authoritative") is not True
            or record.get("published") is not True
            or record.get("cacheable") is not True
            or record.get("expected_outcome") != "admitted-after-refusal"
            or record.get("actual_outcome") != "admitted-after-refusal"
            or record.get("first_divergence") is not None
            or record.get("cleanup_status") != "not_applicable"
            or record.get("final_state")
            != "declaration-published-after-earlier-refusal"
        ):
            raise EvidenceError(
                f"declaration-admission recovery {limit_name} differs"
            )
        require_environment_identity_hex(
            digest, label=f"declaration-admission recovery {limit_name} digest"
        )
        require_environment_identity_hex(
            published_root,
            label=f"declaration-admission recovery {limit_name} root",
        )
        recovery_digests.add(digest)
        recovery_roots.add(published_root)
    if len(recovery_digests) != 7 or len(recovery_roots) != 7:
        raise EvidenceError(
            "declaration-admission recoveries reuse a digest or published root"
        )

    summary = records[18]
    require_row(
        summary,
        summary_fields,
        schema=DECLARATION_ADMISSION_SUMMARY_SCHEMA,
        label="summary",
    )
    if (
        summary.get("scenario") != "declaration-admission-real-path"
        or summary.get("steps") != 18
        or summary.get("admitted_rows") != 1
        or summary.get("refusal_rows") != 7
        or summary.get("cancellation_rows") != 2
        or summary.get("superseded_rows") != 1
        or summary.get("recovery_rows") != 7
        or summary.get("declaration_dimension_rows") != 5
        or summary.get("delegated_limit_rows") != 2
        or summary.get("cleanup_status") != "retained_by_policy"
        or summary.get("final_state")
        != "every-budgeted-limit-refused-typed-and-recovered"
        or sum(
            record["is_declaration_dimension"] is True for record in refusals
        )
        != 5
        or sum(
            record["is_declaration_dimension"] is False for record in refusals
        )
        != 2
    ):
        raise EvidenceError("declaration-admission summary or limit split differs")

    return {
        "schema": "fln.validation/1",
        "validator": "declaration-admission/1",
        "subject": stdout_relative,
        "valid": True,
        "run_id": expected_run_id,
        "observed_exit": observed_exit,
        "records": len(records),
        "steps": 18,
        "refusal_rows": len(refusals),
        "declaration_dimension_rows": 5,
        "delegated_limit_rows": 2,
        "canonical_input_root": DECLARATION_ADMISSION_INPUT_ROOT,
        "base_root": DECLARATION_ADMISSION_BASE_ROOT,
        "stdout_artifact": stdout_relative,
        "stderr_artifact": stderr_relative,
        "stdout_sha256": stdout_digest,
        "stderr_sha256": stderr_digest,
    }


def read_kernel_admission_stream(
    path: Path, artifact_root: Path, *, label: str
) -> tuple[Path, bytes, str, str, str]:
    root = lexical_absolute(artifact_root)
    absolute = require_within(path, root, label=f"kernel-admission {label}")
    data, _size, digest = stable_file_facts(absolute, max_bytes=MAX_LOG_BYTES)
    if data and not data.endswith(b"\n"):
        raise EvidenceError(f"kernel-admission {label} is unterminated: {absolute}")
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        raise EvidenceError(f"kernel-admission {label} is not UTF-8: {absolute}") from error
    for number, raw_line in enumerate(data.splitlines(), 1):
        if len(raw_line) > MAX_RECORD_BYTES:
            raise EvidenceError(
                f"{absolute}:{number}: kernel-admission {label} line is too large"
            )
    relative = absolute.relative_to(root).as_posix()
    return absolute, data, text, digest, relative


def kernel_admission_failure_material(text: str) -> bool:
    failed_forms = set()
    for test in KERNEL_ADMISSION_TESTS:
        failed_forms.add(f"{test} --- FAILED")
        failed_forms.add(f"test {test} ... FAILED")
    for line in text.splitlines():
        stripped = line.strip()
        if (
            stripped in failed_forms
            or stripped.startswith("test result: FAILED.")
            or stripped.startswith("thread '")
            and " panicked at " in stripped
            or re.fullmatch(r"assertion .* failed(?:: .*)?", stripped) is not None
            or stripped.startswith("error: test failed")
        ):
            return True
    return False


def validate_kernel_admission(
    stdout_path: Path,
    stderr_path: Path,
    phase: str,
    expected_run_id: str,
    observed_exit: int,
    *,
    artifact_root: Path,
    expected_stdout_artifact: str,
    expected_stderr_artifact: str,
    expected_cwd: str | None = None,
    expected_argv: str | None = None,
    expected_cache_state: str | None = None,
    expected_input_root: str | None = None,
) -> dict[str, Any]:
    """Validate the kernel admission replay's NDJSON detail streams (bead
    franken_lean-ap6): the {1,8,32} thread matrix must be byte-identical, the
    pinned census exact, every named mutant killed typed, every resource phase
    typed Inconclusive-never-verdict, and the machine/human streams disjoint.
    """
    if phase not in {"positive", "recovery"}:
        raise EvidenceError(f"unsupported kernel-admission phase: {phase!r}")
    if not re.fullmatch(r"[A-Za-z0-9_-]+", expected_run_id):
        raise EvidenceError("kernel-admission run id is malformed")
    if not isinstance(observed_exit, int) or isinstance(observed_exit, bool):
        raise EvidenceError("kernel-admission observed exit is not an integer")
    if observed_exit != 0:
        raise EvidenceError(
            f"kernel-admission {phase} exit {observed_exit}, expected 0"
        )
    required_cli_values = {
        "expected cwd": expected_cwd,
        "expected argv": expected_argv,
        "expected cache state": expected_cache_state,
    }
    missing_cli = sorted(
        label
        for label, value in required_cli_values.items()
        if not isinstance(value, str) or not value
    )
    if missing_cli:
        raise EvidenceError(f"kernel-admission {phase} validation lacks {missing_cli!r}")
    if not Path(expected_cwd).is_absolute():
        raise EvidenceError("kernel-admission expected cwd is not absolute")
    if expected_input_root is not None and not re.fullmatch(
        r"fln-fixture:[0-9a-f]{64}", expected_input_root
    ):
        raise EvidenceError("kernel-admission expected input root is malformed")

    root = lexical_absolute(artifact_root)
    stdout_path, stdout_data, stdout_text, stdout_digest, stdout_relative = (
        read_kernel_admission_stream(stdout_path, root, label="stdout")
    )
    stderr_path, stderr_data, stderr_text, stderr_digest, stderr_relative = (
        read_kernel_admission_stream(stderr_path, root, label="stderr")
    )
    if stdout_path == stderr_path:
        raise EvidenceError("kernel-admission stdout and stderr are not distinct")
    for label, expected, actual in (
        ("stdout", expected_stdout_artifact, stdout_relative),
        ("stderr", expected_stderr_artifact, stderr_relative),
    ):
        expected_as_path = Path(expected)
        if (
            not expected
            or expected_as_path.is_absolute()
            or ".." in expected_as_path.parts
            or expected in {"."}
            or expected_as_path.as_posix() != expected
        ):
            raise EvidenceError(
                f"kernel-admission expected {label} artifact is not a canonical relative path"
            )
        if expected != actual:
            raise EvidenceError(
                f"kernel-admission {label} path {actual!r}, expected {expected!r}"
            )

    matrix_marker = KERNEL_ADMISSION_SCHEMA.encode("ascii")
    fault_marker = KERNEL_ADMISSION_FAULT_SCHEMA.encode("ascii")
    if matrix_marker in stderr_data or fault_marker in stderr_data:
        raise EvidenceError("kernel-admission detail rows leaked into stderr")
    if "kernel_replay census:" in stdout_text:
        raise EvidenceError("kernel-admission human census line leaked into stdout")
    census_lines = [
        line
        for line in stderr_text.splitlines()
        if line.startswith("kernel_replay census:")
    ]
    if len(census_lines) != 1:
        raise EvidenceError(
            "kernel-admission stderr lacks exactly one human census line"
        )
    if kernel_admission_failure_material(stdout_text):
        raise EvidenceError(f"kernel-admission {phase} stdout contains failure material")
    if kernel_admission_failure_material(stderr_text):
        raise EvidenceError(f"kernel-admission {phase} stderr contains failure material")
    pass_result_lines = [
        line.strip()
        for line in stdout_text.splitlines()
        if line.strip().startswith("test result: ok.")
    ]
    if len(pass_result_lines) != 1 or not re.match(
        r"^test result: ok\. 2 passed; 0 failed;", pass_result_lines[0]
    ):
        raise EvidenceError(
            f"kernel-admission {phase} log lacks the exact two-test pass summary"
        )

    matrix_records: list[dict[str, Any]] = []
    fault_records: list[dict[str, Any]] = []
    artifact_records: list[dict[str, Any]] = []
    for number, raw_line in enumerate(stdout_data.splitlines(), 1):
        is_fault = fault_marker in raw_line
        if not is_fault and matrix_marker not in raw_line:
            continue
        object_start = raw_line.find(b"{")
        if object_start < 0:
            raise EvidenceError(
                f"{stdout_path}:{number}: kernel-admission evidence is not a JSON object"
            )
        value = parse_json(
            raw_line[object_start:].strip(), subject=f"{stdout_path}:{number}"
        )
        if not isinstance(value, dict):
            raise EvidenceError(
                f"{stdout_path}:{number}: kernel-admission evidence is not an object"
            )
        if is_fault:
            fault_records.append(value)
        elif value.get("scenario") == "init-prelude-artifact-incomplete-census":
            artifact_records.append(value)
        else:
            matrix_records.append(value)

    expected_shared_identity = {
        "bead": "franken_lean-ap6",
        "claim_type": "bounded_model",
        "invariant_relation": "single-authority-admission",
        "determinism_invariant": "FL-INV-01",
        "gate_id": "G1",
        "gate_relation": "partial-component-evidence",
        "parity_ledger_row": "init-prelude-admission-replay",
        "data_grade": "verified",
        "epoch": "lean-v4.32.0",
        "mode": "sound",
        "profile": "e2e",
        "seed": "module-order-kahn-v1",
        "cleanup_status": "retained_by_policy",
        "timing_used_as_gate": False,
        "process_exit": 0,
        "signal": None,
    }

    def positive_integer(record: dict[str, Any], key: str) -> int:
        value = record.get(key)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            raise EvidenceError(
                f"kernel-admission {key} {value!r} is not a non-negative integer"
            )
        return value

    shared_input_root: str | None = None
    shared_platform: str | None = None

    def check_shared(record: dict[str, Any], label: str) -> None:
        nonlocal shared_input_root, shared_platform
        for key, expected in expected_shared_identity.items():
            if record.get(key) != expected:
                raise EvidenceError(
                    f"kernel-admission {label} {key} {record.get(key)!r}, "
                    f"expected {expected!r}"
                )
        version = record.get("version")
        if version != KERNEL_ADMISSION_VERSION or isinstance(version, bool):
            raise EvidenceError(f"kernel-admission {label} version {version!r}")
        if record.get("run_id") != expected_run_id:
            raise EvidenceError(f"kernel-admission {label} run id mismatch")
        if record.get("cwd") != expected_cwd:
            raise EvidenceError(f"kernel-admission {label} cwd mismatch")
        if record.get("argv") != [expected_argv]:
            raise EvidenceError(f"kernel-admission {label} argv mismatch")
        if record.get("cache_state") != expected_cache_state:
            raise EvidenceError(f"kernel-admission {label} cache-state mismatch")
        if (
            record.get("stdout_artifact") != expected_stdout_artifact
            or record.get("stderr_artifact") != expected_stderr_artifact
        ):
            raise EvidenceError(f"kernel-admission {label} artifact identity mismatch")
        platform_value = record.get("platform")
        if (
            not isinstance(platform_value, str)
            or not platform_value
            or "-" not in platform_value
        ):
            raise EvidenceError(f"kernel-admission {label} platform is malformed")
        if shared_platform is None:
            shared_platform = platform_value
        elif platform_value != shared_platform:
            raise EvidenceError("kernel-admission platform changed across rows")
        input_root = record.get("canonical_input_root")
        if not isinstance(input_root, str) or not re.fullmatch(
            r"fln-fixture:[0-9a-f]{64}", input_root
        ):
            raise EvidenceError(f"kernel-admission {label} input root is malformed")
        if shared_input_root is None:
            shared_input_root = input_root
        elif input_root != shared_input_root:
            raise EvidenceError("kernel-admission input root changed across rows")
        if (
            positive_integer(record, "budget_steps") != KERNEL_ADMISSION_BUDGET_STEPS
            and record.get("phase")
            not in {
                "resource_boundary_exact_accept",
                "resource_exhaustion_steps",
            }
        ):
            raise EvidenceError(f"kernel-admission {label} step budget differs")
        start_us = positive_integer(record, "monotonic_start_us")
        end_us = positive_integer(record, "monotonic_end_us")
        positive_integer(record, "duration_us")
        if end_us < start_us:
            raise EvidenceError(f"kernel-admission {label} timing facts are inconsistent")

    expected_matrix_phases = [
        f"matrix-threads-{threads}" for threads in KERNEL_ADMISSION_THREADS
    ] + ["matrix-identity"]
    if len(matrix_records) != len(expected_matrix_phases):
        raise EvidenceError(
            f"kernel-admission emitted {len(matrix_records)} matrix rows, "
            f"expected {len(expected_matrix_phases)}"
        )
    shared_digest: str | None = None
    shared_root: str | None = None
    shared_steps: int | None = None
    shared_depth: int | None = None
    for record, expected_phase in zip(
        matrix_records, expected_matrix_phases, strict=True
    ):
        if set(record) != KERNEL_ADMISSION_FIELDS:
            missing = sorted(KERNEL_ADMISSION_FIELDS - set(record))
            extra = sorted(set(record) - KERNEL_ADMISSION_FIELDS)
            raise EvidenceError(
                f"kernel-admission matrix field mismatch: "
                f"missing={missing!r} extra={extra!r}"
            )
        if record.get("schema") != KERNEL_ADMISSION_SCHEMA:
            raise EvidenceError("kernel-admission matrix schema mismatch")
        if record.get("claim_id") != "franken_lean-ap6-admission-determinism":
            raise EvidenceError("kernel-admission matrix claim id mismatch")
        if record.get("invariant_id") != "FL-INV-02":
            raise EvidenceError("kernel-admission matrix invariant id mismatch")
        if record.get("scenario") != "init-prelude-admission-thread-matrix":
            raise EvidenceError("kernel-admission matrix scenario mismatch")
        if record.get("phase") != expected_phase:
            raise EvidenceError(
                f"kernel-admission matrix phase {record.get('phase')!r}, "
                f"expected {expected_phase!r}"
            )
        if record.get("status") != "pass":
            raise EvidenceError(
                f"kernel-admission matrix row {expected_phase} did not pass"
            )
        if record.get("first_divergence") is not None:
            raise EvidenceError(
                "kernel-admission passing matrix row claims a divergence"
            )
        check_shared(record, f"matrix {expected_phase}")
        if positive_integer(record, "budget_depth") != KERNEL_ADMISSION_BUDGET_DEPTH:
            raise EvidenceError("kernel-admission matrix depth budget differs")
        if expected_phase == "matrix-identity":
            if record.get("final_state") != "byte-identical-across-1-8-32":
                raise EvidenceError(
                    "kernel-admission identity row lost its final state"
                )
        else:
            expected_threads = int(expected_phase.rsplit("-", 1)[1])
            if positive_integer(record, "threads") != expected_threads:
                raise EvidenceError(
                    f"kernel-admission matrix threads mismatch for {expected_phase}"
                )
            if record.get("final_state") != "verdict-stream-merged-canonical-order":
                raise EvidenceError(
                    "kernel-admission matrix row lost its final state"
                )
        for key, expected_value in KERNEL_ADMISSION_CENSUS.items():
            if positive_integer(record, key) != expected_value:
                raise EvidenceError(
                    f"kernel-admission census {key} "
                    f"{record.get(key)!r}, expected {expected_value}"
                )
        # Count conservation: validated + artifact-incomplete covers the module
        # exactly — a typed limitation folded into a success total (or dropped)
        # breaks this arithmetic (bead franken_lean-artifact-incomplete-
        # private-refs-sgt).
        if (
            positive_integer(record, "checked")
            + positive_integer(record, "artifact_incomplete")
            != positive_integer(record, "decls_total")
        ):
            raise EvidenceError(
                "kernel-admission census does not conserve declaration counts"
            )
        if record.get("artifact_incomplete_witness") != KERNEL_ADMISSION_ARTIFACT_WITNESS:
            raise EvidenceError(
                "kernel-admission artifact-incomplete witness "
                f"{record.get('artifact_incomplete_witness')!r} is not the pin"
            )
        digest = record.get("verdict_stream_digest")
        if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise EvidenceError("kernel-admission verdict-stream digest is malformed")
        if shared_digest is None:
            shared_digest = digest
        elif digest != shared_digest:  # ubs:ignore — public verdict-stream content digest, not authentication material.
            raise EvidenceError(
                "kernel-admission verdict stream diverged across the thread matrix"
            )
        logical_root = record.get("final_logical_root")
        if not isinstance(logical_root, str) or not re.fullmatch(
            r"[0-9a-f]{64}", logical_root
        ):
            raise EvidenceError("kernel-admission logical root is malformed")
        if shared_root is None:
            shared_root = logical_root
        elif logical_root != shared_root:
            raise EvidenceError("kernel-admission logical root changed across rows")
        steps_total = positive_integer(record, "steps_used_total")
        depth_seen = positive_integer(record, "max_depth_seen")
        if shared_steps is None:
            shared_steps, shared_depth = steps_total, depth_seen
        elif steps_total != shared_steps or depth_seen != shared_depth:
            raise EvidenceError(
                "kernel-admission resource facts diverged across the thread matrix"
            )

    # The typed artifact-incomplete rows: exactly the pinned six, in canonical
    # order, each denying every authority, all bound by the pinned witness.
    if len(artifact_records) != len(KERNEL_ADMISSION_ARTIFACT_ROWS):
        raise EvidenceError(
            f"kernel-admission emitted {len(artifact_records)} artifact-incomplete "
            f"rows, expected {len(KERNEL_ADMISSION_ARTIFACT_ROWS)}"
        )
    for record, (declaration, safety, missing) in zip(
        artifact_records, KERNEL_ADMISSION_ARTIFACT_ROWS, strict=True
    ):
        if set(record) != KERNEL_ADMISSION_ARTIFACT_ROW_FIELDS:
            missing_fields = sorted(KERNEL_ADMISSION_ARTIFACT_ROW_FIELDS - set(record))
            extra = sorted(set(record) - KERNEL_ADMISSION_ARTIFACT_ROW_FIELDS)
            raise EvidenceError(
                f"kernel-admission artifact-incomplete field mismatch: "
                f"missing={missing_fields!r} extra={extra!r}"
            )
        if record.get("schema") != KERNEL_ADMISSION_SCHEMA:
            raise EvidenceError("kernel-admission artifact-incomplete schema mismatch")
        if record.get("claim_id") != "franken_lean-sgt-artifact-completeness":
            raise EvidenceError("kernel-admission artifact-incomplete claim id mismatch")
        if record.get("invariant_id") != "FL-INV-07":
            raise EvidenceError(
                "kernel-admission artifact-incomplete invariant id mismatch"
            )
        if record.get("phase") != "artifact-incomplete-row":
            raise EvidenceError("kernel-admission artifact-incomplete phase mismatch")
        for key, expected in expected_shared_identity.items():
            if key in record and record.get(key) != expected:
                raise EvidenceError(
                    f"kernel-admission artifact-incomplete {key} mismatch"
                )
        version = record.get("version")
        if version != KERNEL_ADMISSION_VERSION or isinstance(version, bool):
            raise EvidenceError("kernel-admission artifact-incomplete version mismatch")
        if record.get("run_id") != expected_run_id:
            raise EvidenceError("kernel-admission artifact-incomplete run id mismatch")
        if record.get("declaration") != declaration:
            raise EvidenceError(
                f"kernel-admission artifact-incomplete row names "
                f"{record.get('declaration')!r}, expected {declaration!r}"
            )
        if record.get("safety") != safety:
            raise EvidenceError(
                f"kernel-admission artifact-incomplete safety collapsed for "
                f"{declaration}: {record.get('safety')!r} != {safety!r}"
            )
        if record.get("missing_references") != list(missing):
            raise EvidenceError(
                f"kernel-admission artifact-incomplete missing references drifted "
                f"for {declaration}: {record.get('missing_references')!r}"
            )
        if record.get("witness") != KERNEL_ADMISSION_ARTIFACT_WITNESS:
            raise EvidenceError(
                f"kernel-admission artifact-incomplete witness drifted for "
                f"{declaration}"
            )
        if record.get("outcome") != "inconclusive-artifact-incomplete":
            raise EvidenceError(
                f"kernel-admission artifact-incomplete outcome laundered for "
                f"{declaration}: {record.get('outcome')!r}"
            )
        if record.get("authority") != "none":
            raise EvidenceError(
                f"kernel-admission artifact-incomplete authority claimed for "
                f"{declaration}"
            )
        for denial in ("kernel_checked", "cacheable", "environment_admissible"):
            if record.get(denial) is not False:
                raise EvidenceError(
                    f"kernel-admission artifact-incomplete {denial} must be false "
                    f"for {declaration} (an Inconclusive is never cached, checked, "
                    f"or admitted)"
                )
        if record.get("evidence_grade") != "verified":
            raise EvidenceError(
                f"kernel-admission artifact-incomplete evidence grade mismatch for "
                f"{declaration}"
            )

    expected_fault_count = len(KERNEL_ADMISSION_MUTANTS) + len(
        KERNEL_ADMISSION_RESOURCE_PHASES
    )
    if len(fault_records) != expected_fault_count:
        raise EvidenceError(
            f"kernel-admission emitted {len(fault_records)} fault rows, "
            f"expected {expected_fault_count}"
        )
    seen_mutants: list[str] = []
    seen_resource: list[str] = []
    for record in fault_records:
        if set(record) != KERNEL_ADMISSION_FAULT_FIELDS:
            missing = sorted(KERNEL_ADMISSION_FAULT_FIELDS - set(record))
            extra = sorted(set(record) - KERNEL_ADMISSION_FAULT_FIELDS)
            raise EvidenceError(
                f"kernel-admission fault field mismatch: "
                f"missing={missing!r} extra={extra!r}"
            )
        if record.get("schema") != KERNEL_ADMISSION_FAULT_SCHEMA:
            raise EvidenceError("kernel-admission fault schema mismatch")
        if record.get("claim_id") != "franken_lean-ap6-admission-fault-matrix":
            raise EvidenceError("kernel-admission fault claim id mismatch")
        if record.get("scenario") != "kernel-admission-fault-matrix":
            raise EvidenceError("kernel-admission fault scenario mismatch")
        if record.get("status") != "pass":
            raise EvidenceError(
                f"kernel-admission fault row {record.get('phase')!r} did not pass"
            )
        if record.get("first_divergence") is not None:
            raise EvidenceError("kernel-admission passing fault row claims a divergence")
        row_phase = record.get("phase")
        if not isinstance(row_phase, str):
            raise EvidenceError("kernel-admission fault phase is malformed")
        check_shared(record, f"fault {row_phase}")
        if row_phase.startswith("mutant:"):
            mutant_id = record.get("mutant_id")
            if row_phase != f"mutant:{mutant_id}":
                raise EvidenceError(
                    "kernel-admission mutant phase and mutant id disagree"
                )
            if mutant_id not in KERNEL_ADMISSION_MUTANTS:
                raise EvidenceError(
                    f"kernel-admission unknown mutant {mutant_id!r}"
                )
            if record.get("invariant_id") != "FL-INV-02":
                raise EvidenceError("kernel-admission mutant invariant id mismatch")
            if record.get("expected_outcome") != "rejected":
                raise EvidenceError(
                    f"kernel-admission mutant {mutant_id} expects a non-rejection"
                )
            if record.get("actual_outcome") != "rejected":
                raise EvidenceError(
                    f"kernel-admission mutant {mutant_id} SURVIVED: "
                    f"{record.get('actual_outcome')!r}"
                )
            reject_class = record.get("reject_class")
            if not isinstance(reject_class, str) or not reject_class:
                raise EvidenceError(
                    f"kernel-admission mutant {mutant_id} rejection is untyped"
                )
            if record.get("final_state") != "mutant-killed-typed-rejection":
                raise EvidenceError(
                    f"kernel-admission mutant {mutant_id} final state mismatch"
                )
            if record.get("atomicity_held") is not True:
                raise EvidenceError(
                    f"kernel-admission mutant {mutant_id} broke failure atomicity"
                )
            if record.get("root_before") != record.get("root_after"):
                raise EvidenceError(
                    f"kernel-admission mutant {mutant_id} mutated the environment root"
                )
            if record.get("recovery_outcome") != "accepted":
                raise EvidenceError(
                    f"kernel-admission mutant {mutant_id} recovery failed"
                )
            seen_mutants.append(mutant_id)
        elif row_phase in KERNEL_ADMISSION_RESOURCE_PHASES:
            if record.get("invariant_id") != "FL-INV-07":
                raise EvidenceError("kernel-admission resource invariant id mismatch")
            if record.get("mutant_id") is not None:
                raise EvidenceError(
                    f"kernel-admission resource row {row_phase} carries a mutant id"
                )
            expected_outcome = KERNEL_ADMISSION_RESOURCE_PHASES[row_phase]
            if record.get("actual_outcome") != expected_outcome:
                raise EvidenceError(
                    f"kernel-admission resource row {row_phase} outcome "
                    f"{record.get('actual_outcome')!r}, expected {expected_outcome!r}"
                )
            if record.get("atomicity_held") is not True:
                raise EvidenceError(
                    f"kernel-admission resource row {row_phase} broke atomicity"
                )
            seen_resource.append(row_phase)
        else:
            raise EvidenceError(f"kernel-admission unknown fault phase {row_phase!r}")
    if sorted(seen_mutants) != sorted(KERNEL_ADMISSION_MUTANTS):
        missing_mutants = sorted(set(KERNEL_ADMISSION_MUTANTS) - set(seen_mutants))
        raise EvidenceError(
            f"kernel-admission mutant coverage incomplete: missing={missing_mutants!r}"
        )
    if sorted(seen_resource) != sorted(KERNEL_ADMISSION_RESOURCE_PHASES):
        missing_phases = sorted(set(KERNEL_ADMISSION_RESOURCE_PHASES) - set(seen_resource))
        raise EvidenceError(
            f"kernel-admission resource coverage incomplete: missing={missing_phases!r}"
        )

    if shared_input_root is None or shared_digest is None or shared_root is None:
        raise EvidenceError("kernel-admission shared identity facts are incomplete")
    if expected_input_root is not None and shared_input_root != expected_input_root:
        raise EvidenceError(
            f"kernel-admission input root {shared_input_root!r} is stale: "
            f"expected {expected_input_root!r}"
        )
    return {
        "schema": "fln.validation/1",
        "validator": "kernel-admission/1",
        "subject": stdout_relative,
        "valid": True,
        "phase": phase,
        "run_id": expected_run_id,
        "observed_exit": observed_exit,
        "matrix_records": len(matrix_records),
        "fault_records": len(fault_records),
        "artifact_incomplete_records": len(artifact_records),
        "artifact_incomplete_witness": KERNEL_ADMISSION_ARTIFACT_WITNESS,
        "thread_matrix": list(KERNEL_ADMISSION_THREADS),
        "census": dict(KERNEL_ADMISSION_CENSUS),
        "mutants_killed": sorted(seen_mutants),
        "resource_phases": sorted(seen_resource),
        "canonical_input_root": shared_input_root,
        "verdict_stream_digest": shared_digest,
        "final_logical_root": shared_root,
        "stdout_artifact": stdout_relative,
        "stderr_artifact": stderr_relative,
        "stdout_sha256": stdout_digest,
        "stderr_sha256": stderr_digest,
    }


def validate_run(
    path: Path,
    schema: str,
    expected_verdict: str,
    *,
    expected_active_stage: str | None = None,
    expected_planted_stage: str | None = None,
    live_context: bool = True,
) -> dict[str, Any]:
    if schema not in RUN_SCHEMAS:
        raise EvidenceError(f"unsupported run schema: {schema!r}")
    path = lexical_absolute(path)
    records, digest = load_ndjson_snapshot(path)
    if records[0].get("event") != "run_start":
        raise EvidenceError(f"{path}: first record is not run_start")
    terminals = [record for record in records if record.get("event") == "run_end"]
    if len(terminals) != 1 or records[-1] is not terminals[0]:
        raise EvidenceError(f"{path}: expected exactly one final run_end")
    run_id = records[0].get("run_id")
    bead = records[0].get("bead")
    if (
        not isinstance(run_id, str)
        or not run_id
        or not isinstance(bead, str)
        or not bead
    ):
        raise EvidenceError(f"{path}: invalid run identity")
    scenario = records[0].get("scenario")
    if not isinstance(scenario, str) or not scenario:
        raise EvidenceError(f"{path}: scenario identity is missing")
    prior_monotonic = -1
    for index, record in enumerate(records):
        if record.get("schema") != schema:
            raise EvidenceError(f"{path}:{index + 1}: wrong schema")
        if record.get("run_id") != run_id or record.get("bead") != bead:
            raise EvidenceError(f"{path}:{index + 1}: mixed run or bead identity")
        if record.get("scenario") != scenario:
            raise EvidenceError(f"{path}:{index + 1}: mixed scenario identity")
        if record.get("sequence") != index:
            raise EvidenceError(f"{path}:{index + 1}: non-contiguous sequence")
        if not isinstance(record.get("monotonic_ns"), int) or isinstance(
            record.get("monotonic_ns"), bool
        ):
            raise EvidenceError(f"{path}:{index + 1}: missing monotonic_ns")
        if record["monotonic_ns"] < prior_monotonic:
            raise EvidenceError(f"{path}:{index + 1}: monotonic time moved backwards")
        prior_monotonic = record["monotonic_ns"]
        if not isinstance(record.get("wall_time_utc"), str):
            raise EvidenceError(f"{path}:{index + 1}: missing wall_time_utc")
    terminal = terminals[0]
    if terminal.get("verdict") != expected_verdict:
        raise EvidenceError(
            f"{path}: verdict {terminal.get('verdict')!r}, expected {expected_verdict!r}"
        )
    start_required = {
        "argv",
        "cwd",
        "claim_ids",
        "invariant_ids",
        "gate_ids",
        "epoch",
        "mode",
        "profile",
        "platform",
        "host_facts",
        "thread_count",
        "seed",
        "cache_state",
        "input_root",
        "budgets",
        "parity_ledger_row",
        "scenario",
    }
    if schema == "fln.check/2":
        start_required.add("verification_manifest")
    missing = sorted(key for key in start_required if key not in records[0])
    if missing:
        raise EvidenceError(f"{path}: run_start missing fields {missing!r}")
    for key in ("claim_ids", "invariant_ids", "gate_ids"):
        value = records[0][key]
        if (
            not isinstance(value, list)
            or not value
            or not all(isinstance(item, str) and item for item in value)
        ):
            raise EvidenceError(f"{path}: {key} must be a non-empty string array")
    if not isinstance(records[0]["argv"], list) or not all(
        isinstance(item, str) for item in records[0]["argv"]
    ):
        raise EvidenceError(f"{path}: argv must be a string array")
    if not re.fullmatch(r"sha256:[0-9a-f]{64}", str(records[0]["input_root"])):
        raise EvidenceError(f"{path}: input_root is not a canonical SHA-256 tree root")
    budgets = records[0]["budgets"]
    if (
        not isinstance(budgets, dict)
        or not budgets
        or not all(
            isinstance(value, int) and not isinstance(value, bool) and value > 0
            for value in budgets.values()
        )
    ):
        raise EvidenceError(f"{path}: budgets must be positive integer facts")
    host_facts = records[0]["host_facts"]
    if not isinstance(host_facts, dict) or not all(
        isinstance(host_facts.get(key), str) and host_facts[key]
        for key in ("system", "release", "machine", "python")
    ):
        raise EvidenceError(f"{path}: host facts are incomplete")
    if (
        not isinstance(records[0]["parity_ledger_row"], str)
        or not records[0]["parity_ledger_row"]
    ):
        raise EvidenceError(f"{path}: parity ledger classification is missing")
    if (
        not isinstance(records[0]["thread_count"], int)
        or isinstance(records[0]["thread_count"], bool)
        or records[0]["thread_count"] <= 0
    ):
        raise EvidenceError(f"{path}: thread count must be a positive integer")
    profile = records[0]["profile"]
    allowed_profiles = (
        {
            "local",
            "ci",
            "self-test-driver",
            "self-test-plant",
            "self-test-cancellation",
            "finalizer-self-test",
            "early-fault-self-test",
            "evidence-manifest-self-test",
        }
        if schema == "fln.check/2"
        else {"e2e"}
    )
    if profile not in allowed_profiles:
        raise EvidenceError(f"{path}: unknown run profile {profile!r}")
    if schema == "fln.check/2" and not isinstance(records[0].get("planted"), str):
        raise EvidenceError(f"{path}: planted-stage binding must be a string")
    binding_free_profiles = {
        "evidence-manifest-self-test",
        "finalizer-self-test",
        "early-fault-self-test",
    }
    if schema == "fln.check/2" and profile not in binding_free_profiles:
        if records[0].get("ubs_inventory") != "ubs-inventory.json":
            raise EvidenceError(f"{path}: quality gate lacks its UBS inventory binding")
        validate_ubs_inventory(
            path.parent / "ubs-inventory.json",
            Path(records[0]["cwd"]) if live_context else None,
        )
    if schema == "fln.check/2":
        if records[0].get("verification_manifest") != VERIFICATION_MANIFEST_PATH:
            raise EvidenceError(
                f"{path}: quality gate names an unknown verification manifest"
            )
        # The explicit verification-manifest stage is the execution authority.
        # Re-reading mutable tracker state during terminal publication would
        # turn a later bead transition into an unrelated bundle failure.
    if schema == "fln.e2e/2" or profile not in binding_free_profiles:
        if records[0].get("vendor_binding") != "vendor-binding.json":
            raise EvidenceError(f"{path}: run lacks its Reference vendor binding")
        recorded_binding = read_json_object(path.parent / "vendor-binding.json")
        validate_vendor_binding_document(recorded_binding)
        if live_context:
            live_binding = verify_vendor_binding(
                Path(records[0]["cwd"]), "vendor/lean4-src"
            )
            if recorded_binding != live_binding:
                raise EvidenceError(f"{path}: Reference vendor binding is stale")
    terminal_required = {
        "reason_code",
        "process_exit",
        "duration_ns",
        "cleanup_status",
        "final_state",
        "evidence_manifest",
        "bundle_commit",
        "evidence_state",
        "logical_root",
        "receipt_root",
        "first_divergence",
    }
    missing = sorted(key for key in terminal_required if key not in terminal)
    if missing:
        raise EvidenceError(f"{path}: run_end missing fields {missing!r}")
    expected_process_exits = {
        "pass": {0},
        "fail": {1},
        "internal_fault": {2},
        "inconclusive": {3},
        "cancelled": {4, 129, 130, 143},
    }
    if expected_verdict not in expected_process_exits:
        raise EvidenceError(f"{path}: unknown terminal verdict {expected_verdict!r}")
    if terminal.get("process_exit") not in expected_process_exits[expected_verdict]:
        raise EvidenceError(f"{path}: verdict and process_exit disagree")
    if not isinstance(terminal.get("duration_ns"), int) or terminal["duration_ns"] < 0:
        raise EvidenceError(f"{path}: terminal duration is malformed")
    for key in (
        "reason_code",
        "active_stage" if schema == "fln.check/2" else "active_step",
    ):
        if not isinstance(terminal.get(key), str) or not terminal[key]:
            raise EvidenceError(f"{path}: terminal {key} is malformed")
    if terminal.get("cleanup_status") != "retained_by_policy":
        raise EvidenceError(f"{path}: terminal cleanup policy is unknown")
    if (
        expected_verdict == "pass"
        and terminal.get("final_state") != records[0]["input_root"]
    ):
        raise EvidenceError(f"{path}: passing run changed its canonical input root")
    if terminal.get("logical_root") != terminal.get("final_state"):
        raise EvidenceError(f"{path}: terminal logical root disagrees with final state")
    if (
        not isinstance(terminal.get("receipt_root"), str)
        or not terminal["receipt_root"]
    ):
        raise EvidenceError(f"{path}: terminal receipt-root classification is missing")
    if expected_verdict == "pass" and terminal.get("first_divergence") != "none":
        raise EvidenceError(f"{path}: passing run claims a first divergence")
    if expected_verdict != "pass" and not isinstance(
        terminal.get("first_divergence"), str
    ):
        raise EvidenceError(f"{path}: failing run lacks first-divergence data")
    if expected_verdict != "pass" and terminal.get("first_divergence") != terminal.get(
        "reason_code"
    ):
        raise EvidenceError(
            f"{path}: first divergence does not identify the terminal reason"
        )
    if terminal.get("evidence_state") != "pending_bundle_commit":
        raise EvidenceError(f"{path}: run terminal must declare pending bundle commit")
    if terminal.get("bundle_commit") != "bundle.complete.json":
        raise EvidenceError(
            f"{path}: run terminal names an unknown bundle commit marker"
        )
    if expected_active_stage is not None:
        active = terminal.get("active_stage", terminal.get("active_step"))
        if active != expected_active_stage:
            raise EvidenceError(
                f"{path}: terminal active item {active!r}, expected {expected_active_stage!r}"
            )

    allowed_events = (
        {"run_start", "stage", "self_test", "run_end"}
        if schema == "fln.check/2"
        else {"run_start", "step", "run_end"}
    )
    seen_ids: set[str] = set()
    for index, record in enumerate(records[1:-1], 2):
        event = record.get("event")
        if event not in allowed_events:
            raise EvidenceError(f"{path}:{index}: unknown event {event!r}")
        if event == "stage":
            required = {"stage", "outcome", "reason_code", "expected", "actual"}
            missing = sorted(key for key in required if key not in record)
            if missing:
                raise EvidenceError(f"{path}:{index}: stage missing {missing!r}")
            if not isinstance(record["stage"], str) or not record["stage"]:
                raise EvidenceError(f"{path}:{index}: invalid stage identity")
            event_id = record["stage"]
            base_keys = {
                "schema",
                "event",
                "run_id",
                "bead",
                "scenario",
                "sequence",
                "monotonic_ns",
                "wall_time_utc",
                "stage",
                "outcome",
                "reason_code",
                "expected",
                "actual",
            }
            if record["outcome"] == "not_run":
                expected_keys = base_keys | {"causal_stage", "causal_reason"}
                if set(record) != expected_keys:
                    raise EvidenceError(
                        f"{path}:{index}: not_run stage shape mismatch"
                    )
                if (
                    record["reason_code"] != "blocked_by_prior_stage"
                    or record["expected"] != "not_run"
                    or record["actual"] != "not_run"
                    or not isinstance(record.get("causal_stage"), str)
                    or not record["causal_stage"]
                    or not isinstance(record.get("causal_reason"), str)
                    or not record["causal_reason"]
                ):
                    raise EvidenceError(
                        f"{path}:{index}: invalid not_run causal record"
                    )
            elif record["outcome"] != "skipped":
                if record.get("supervisor_available") is False:
                    expected_keys = base_keys | {
                        "supervisor_available",
                        "wrapper_exit",
                    }
                    if set(record) != expected_keys:
                        raise EvidenceError(
                            f"{path}:{index}: missing-supervisor stage shape mismatch"
                        )
                    if (
                        record["outcome"] != "internal_fault"
                        or record.get("reason_code") != "missing_supervisor_metadata"
                        or record.get("expected") != "exit_zero"
                        or record.get("actual") != "metadata_unavailable"
                        or record.get("wrapper_exit") != SETUP_FAILURE
                    ):
                        raise EvidenceError(
                            f"{path}:{index}: invalid missing-supervisor event"
                        )
                else:
                    expected_keys = base_keys | {"supervisor", "wrapper_exit"}
                    if set(record) != expected_keys:
                        raise EvidenceError(
                            f"{path}:{index}: supervised stage shape mismatch"
                        )
                    validate_supervisor_object(
                        path,
                        index,
                        record.get("supervisor"),
                        expected_stage_id=event_id,
                    )
                    wrapper_mismatch = (
                        record.get("outcome") == "internal_fault"
                        and record.get("reason_code") == "wrapper_exit_mismatch"
                    )
                    if (
                        record["supervisor"]["classification"] != record["outcome"]
                        and not wrapper_mismatch
                    ):
                        raise EvidenceError(
                            f"{path}:{index}: stage/supervisor outcome mismatch"
                        )
                    if (
                        record.get("wrapper_exit")
                        != record["supervisor"]["wrapper_exit"]
                        and not wrapper_mismatch
                    ):
                        raise EvidenceError(
                            f"{path}:{index}: stage/supervisor exit mismatch"
                        )
                    if wrapper_mismatch and (
                        record.get("wrapper_exit")
                        == record["supervisor"]["wrapper_exit"]
                    ):
                        raise EvidenceError(
                            f"{path}:{index}: false wrapper-exit mismatch"
                        )
                    if wrapper_mismatch:
                        if (
                            record.get("expected") != "supervisor_wrapper_exit"
                            or record.get("actual")
                            != "shell_wrapper_exit_mismatch"
                        ):
                            raise EvidenceError(
                                f"{path}:{index}: malformed wrapper-exit mismatch"
                            )
                    elif (
                        record.get("reason_code")
                        != record["supervisor"]["reason_code"]
                        or record.get("expected") != "exit_zero"
                        or record.get("actual") != record["outcome"]
                    ):
                        raise EvidenceError(
                            f"{path}:{index}: stage decision differs from supervisor"
                        )
            else:
                expected_keys = base_keys | {"limitation"}
                if set(record) != expected_keys:
                    raise EvidenceError(
                        f"{path}:{index}: skipped stage shape mismatch"
                    )
                if (
                    event_id != "ubs"
                    or records[0]["profile"] == "ci"
                    or record.get("reason_code") != "typed_limitation"
                    or record.get("expected") != "not_applicable"
                    or record.get("actual") != "skipped"
                    or not isinstance(record.get("limitation"), str)
                    or not record["limitation"]
                ):
                    raise EvidenceError(
                        f"{path}:{index}: invalid skipped obligation"
                    )
        elif event == "step":
            required = {
                "step_id",
                "assertion",
                "expected",
                "actual",
                "input_root",
                "final_state",
                "validation_artifact",
                "supervisor",
                "expected_supervisor_classification",
                "expected_wrapper_exit",
                "expected_child_exit",
                "subject_root",
                "subject_final_state",
            }
            missing = sorted(key for key in required if key not in record)
            if missing:
                raise EvidenceError(f"{path}:{index}: step missing {missing!r}")
            if not isinstance(record["step_id"], str) or not record["step_id"]:
                raise EvidenceError(f"{path}:{index}: invalid step identity")
            event_id = record["step_id"]
            validate_supervisor_object(
                path, index, record.get("supervisor"), expected_stage_id=event_id
            )
            supervisor = record["supervisor"]
            if record["assertion"] not in {"pass", "fail"}:
                raise EvidenceError(f"{path}:{index}: unknown assertion outcome")
            if record["assertion"] == "pass":
                if (
                    supervisor["classification"]
                    != record["expected_supervisor_classification"]
                ):
                    raise EvidenceError(
                        f"{path}:{index}: unexpected supervisor classification"
                    )
                if supervisor["wrapper_exit"] != record["expected_wrapper_exit"]:
                    raise EvidenceError(
                        f"{path}:{index}: unexpected supervisor wrapper exit"
                    )
                if supervisor["child_exit"] != record["expected_child_exit"]:
                    raise EvidenceError(
                        f"{path}:{index}: unexpected supervised child exit"
                    )
            for root_key in (
                "input_root",
                "final_state",
                "subject_root",
                "subject_final_state",
            ):
                if not re.fullmatch(r"sha256:[0-9a-f]{64}", str(record[root_key])):
                    raise EvidenceError(
                        f"{path}:{index}: {root_key} is not a canonical tree root"
                    )
            if record["subject_root"] != record["subject_final_state"]:
                raise EvidenceError(
                    f"{path}:{index}: step subject changed during assertion"
                )
            if record["assertion"] == "pass" and (
                record["input_root"] != records[0]["input_root"]
                or record["final_state"] != records[0]["input_root"]
            ):
                raise EvidenceError(
                    f"{path}:{index}: passing step used a foreign global root"
                )
            validation_artifact = record["validation_artifact"]
            if validation_artifact != "not_applicable":
                candidate = require_within(
                    path.parent / str(validation_artifact),
                    path.parent,
                    label="validation artifact",
                )
                stable_file_facts(candidate)
        elif event == "self_test":
            required = {"stage", "ok", "planted_exit", "artifact"}
            missing = sorted(key for key in required if key not in record)
            if missing or not isinstance(record.get("ok"), bool):
                raise EvidenceError(f"{path}:{index}: malformed self_test event")
            if not isinstance(record["stage"], str) or not record["stage"]:
                raise EvidenceError(f"{path}:{index}: invalid self-test identity")
            event_id = f"self_test:{record['stage']}"
        else:
            raise EvidenceError(f"{path}:{index}: nested run boundary")
        if event_id in seen_ids:
            raise EvidenceError(f"{path}:{index}: duplicate event id {event_id!r}")
        seen_ids.add(event_id)

    exercised = records[1:-1]
    if schema == "fln.check/2":
        profile = records[0]["profile"]
        if profile == "evidence-manifest-self-test":
            expected_ids = ["manifest-stage"]
            actual_ids = [
                str(record.get("stage"))
                for record in exercised
                if record.get("event") == "stage"
            ]
            if len(actual_ids) != len(exercised):
                raise EvidenceError(
                    f"{path}: manifest self-test contains foreign events"
                )
        elif profile == "self-test-driver":
            expected_ids = CHECK_SELF_TEST_ORDER
            actual_ids = [
                str(record.get("stage"))
                for record in exercised
                if record.get("event") == "self_test"
            ]
            if len(actual_ids) != len(exercised):
                raise EvidenceError(f"{path}: check self-test contains foreign events")
        elif profile in {"finalizer-self-test", "early-fault-self-test"}:
            expected_ids = ["finalizer-probe"]
            actual_ids = [
                str(record.get("stage"))
                for record in exercised
                if record.get("event") == "self_test"
            ]
            if len(actual_ids) != len(exercised):
                raise EvidenceError(
                    f"{path}: finalizer self-test contains foreign events"
                )
        else:
            expected_ids = CHECK_STAGE_ORDER
            stage_records = [
                record for record in exercised if record.get("event") == "stage"
            ]
            actual_ids = [str(record.get("stage")) for record in stage_records]
            if len(stage_records) != len(exercised):
                raise EvidenceError(f"{path}: quality gate contains foreign events")
        if actual_ids != expected_ids[: len(actual_ids)]:
            raise EvidenceError(
                f"{path}: non-canonical check obligation order: {actual_ids!r}"
            )
        if expected_verdict == "pass" and actual_ids != expected_ids:
            raise EvidenceError(f"{path}: passing check omitted mandatory obligations")
        failed_stage_records = [
            record
            for record in exercised
            if record.get("event") == "stage"
            and record.get("outcome")
            not in {"pass", "skipped", "not_run"}
        ]
        if failed_stage_records:
            if len(failed_stage_records) != 1 or actual_ids != expected_ids:
                raise EvidenceError(
                    f"{path}: failed check omitted explicit downstream not_run stages"
                )
            failed_record = failed_stage_records[0]
            failed_index = exercised.index(failed_record)
            for record in exercised[failed_index + 1 :]:
                if (
                    record.get("event") != "stage"
                    or record.get("outcome") != "not_run"
                    or record.get("causal_stage") != failed_record.get("stage")
                    or record.get("causal_reason")
                    != failed_record.get("reason_code")
                ):
                    raise EvidenceError(
                        f"{path}: downstream stage lacks exact failure causality"
                    )
        elif any(
            record.get("event") == "stage"
            and record.get("outcome") == "not_run"
            for record in exercised
        ):
            raise EvidenceError(f"{path}: not_run stages have no failed cause")
        bound_plant = records[0]["planted"]
        planted_events = [
            record
            for record in exercised
            if record.get("event") == "stage"
            and isinstance(record.get("supervisor"), dict)
            and record["supervisor"].get("planted") is True
        ]
        if isinstance(bound_plant, str) and bound_plant.startswith("unexpected:"):
            # The deliberate unexpected-failure plant: the planted stage must
            # type internal_fault with the unexpected-exit reason, never a
            # semantic stage failure.
            unexpected_stage = bound_plant.removeprefix("unexpected:")
            if (
                profile != "self-test-plant"
                or expected_verdict != "internal_fault"
                or not unexpected_stage
                or len(planted_events) != 1
                or planted_events[0].get("stage") != unexpected_stage
                or planted_events[0].get("outcome") != "internal_fault"
                or planted_events[0].get("reason_code") != "unexpected_child_exit"
            ):
                raise EvidenceError(
                    f"{path}: planted unexpected-failure contract is inconsistent"
                )
        elif bound_plant:
            if (
                profile != "self-test-plant"
                or expected_verdict != "fail"
                or len(planted_events) != 1
                or planted_events[0].get("stage") != bound_plant
                or planted_events[0].get("outcome") != "fail"
            ):
                raise EvidenceError(f"{path}: planted failure contract is inconsistent")
        elif planted_events:
            raise EvidenceError(f"{path}: unbound planted failure evidence")
    else:
        if scenario not in E2E_STEP_ORDERS:
            raise EvidenceError(f"{path}: unknown E2E scenario {scenario!r}")
        expected_ids = E2E_STEP_ORDERS[scenario]
        actual_ids = [
            str(record.get("step_id"))
            for record in exercised
            if record.get("event") == "step"
        ]
        if len(actual_ids) != len(exercised):
            raise EvidenceError(f"{path}: E2E run contains foreign events")
        if actual_ids != expected_ids[: len(actual_ids)]:
            raise EvidenceError(
                f"{path}: non-canonical E2E obligation order: {actual_ids!r}"
            )
        if expected_verdict == "pass" and actual_ids != expected_ids:
            raise EvidenceError(
                f"{path}: passing E2E run omitted mandatory obligations"
            )
    if expected_verdict == "pass":
        if not records[1:-1]:
            raise EvidenceError(
                f"{path}: passing run contains no exercised obligations"
            )
        for index, record in enumerate(records[1:-1], 2):
            if record.get("event") == "stage" and record.get("outcome") not in {
                "pass",
                "skipped",
            }:
                raise EvidenceError(
                    f"{path}:{index}: passing run contains failed stage"
                )
            if record.get("event") == "step" and record.get("assertion") != "pass":
                raise EvidenceError(
                    f"{path}:{index}: passing run contains failed assertion"
                )
            if record.get("event") == "self_test" and record.get("ok") is not True:
                raise EvidenceError(
                    f"{path}:{index}: passing run contains failed self-test"
                )
    if expected_planted_stage is not None:
        matching = [
            record
            for record in records[1:-1]
            if record.get("event") == "stage"
            and record.get("stage") == expected_planted_stage
        ]
        if len(matching) != 1:
            raise EvidenceError(f"{path}: expected exactly one planted stage event")
        planted_record = matching[0]
        if (
            planted_record.get("outcome") != "fail"
            or planted_record["supervisor"].get("planted") is not True
        ):
            raise EvidenceError(f"{path}: requested stage is not the planted failure")
        for record in records[1 : records.index(planted_record)]:
            if record.get("event") == "stage" and record.get("outcome") not in {
                "pass",
                "skipped",
            }:
                raise EvidenceError(
                    f"{path}: an earlier stage failed before the requested plant"
                )
        for record in records[records.index(planted_record) + 1 : -1]:
            if (
                record.get("event") != "stage"
                or record.get("outcome") != "not_run"
                or record.get("causal_stage") != expected_planted_stage
                or record.get("causal_reason")
                != planted_record.get("reason_code")
            ):
                raise EvidenceError(
                    f"{path}: planted failure lacks explicit downstream not_run records"
                )
        if records[0].get("planted") != expected_planted_stage:
            raise EvidenceError(f"{path}: run start does not bind the requested plant")
    return {
        "schema": "fln.validation/1",
        "subject": path.name,
        "valid": True,
        "records": len(records),
        "run_id": run_id,
        "verdict": expected_verdict,
        "sha256": digest,
        "bundle_committed": False,
    }


def validate_supervisor_object(
    path: Path,
    record_number: int,
    value: Any,
    *,
    expected_stage_id: str,
) -> None:
    if not isinstance(value, dict) or value.get("schema") not in {
        "fln.supervisor/1",
        "fln.supervisor/2",
        "fln.supervisor/3",
        "fln.supervisor/4",
        "fln.supervisor/5",
    }:
        raise EvidenceError(f"{path}:{record_number}: missing supervisor envelope")
    schema = value["schema"]
    expected_keys = {
        "schema",
        "stage_id",
        "argv",
        "argv_redacted",
        "cwd",
        "classification",
        "reason_code",
        "wrapper_exit",
        "child_exit",
        "child_signal",
        "cancel_signal",
        "started_utc",
        "ended_utc",
        "monotonic_start_ns",
        "monotonic_end_ns",
        "duration_ns",
        "resource",
        "stdout",
        "stderr",
        "planted",
        "semantic_failure_exits",
        "readiness",
        "errors",
        "host",
    }
    if schema in {
        "fln.supervisor/2",
        "fln.supervisor/3",
        "fln.supervisor/4",
        "fln.supervisor/5",
    }:
        expected_keys.update({"phase_timing", "target_exec"})
    if schema in {
        "fln.supervisor/3",
        "fln.supervisor/4",
        "fln.supervisor/5",
    }:
        expected_keys.add("test_control")
    if schema in {"fln.supervisor/4", "fln.supervisor/5"}:
        expected_keys.add("sealed_compiler")
    if schema == "fln.supervisor/5":
        expected_keys.add("sealed_interpreter")
    if set(value) != expected_keys:
        raise EvidenceError(
            f"{path}:{record_number}: supervisor envelope shape mismatch"
        )
    if schema in {"fln.supervisor/4", "fln.supervisor/5"}:
        sealed = value["sealed_compiler"]
        if sealed is not None:
            if not isinstance(sealed, dict):
                raise EvidenceError(
                    f"{path}:{record_number}: sealed-compiler facts are not an object"
                )
            commit = sealed.get("commit")
            if "commit" in sealed and (
                not isinstance(commit, str) or not re.fullmatch(r"[0-9a-f]{40}", commit)
            ):
                raise EvidenceError(
                    f"{path}:{record_number}: sealed-compiler commit is malformed"
                )
            for environment_field in (
                "admitted_env",
                "overridden_env",
                "rejected_env",
            ):
                environment_names = sealed.get(environment_field)
                if environment_field in sealed and (
                    not isinstance(environment_names, list)
                    or not all(
                        isinstance(item, str) and item
                        for item in environment_names
                    )
                    or environment_names != sorted(set(environment_names))
                ):
                    raise EvidenceError(
                        f"{path}:{record_number}: sealed-compiler "
                        f"{environment_field} is malformed"
                    )
    if schema == "fln.supervisor/5":
        sealed_interpreter = value["sealed_interpreter"]
        if not isinstance(sealed_interpreter, dict):
            raise EvidenceError(
                f"{path}:{record_number}: sealed-interpreter facts are not an object"
            )
        expected_interpreter_keys = {
            "executable",
            "version",
            "stdlib_prefix",
            "base_prefix",
            "exec_prefix",
            "flags",
            "overridden_env",
        }
        if set(sealed_interpreter) != expected_interpreter_keys:
            raise EvidenceError(
                f"{path}:{record_number}: sealed-interpreter shape mismatch"
            )
        host_identity = effective_interpreter_identity({})
        for identity_field in (
            "executable",
            "version",
            "stdlib_prefix",
            "base_prefix",
            "exec_prefix",
        ):
            if sealed_interpreter[identity_field] != host_identity[identity_field]:
                raise EvidenceError(
                    f"{path}:{record_number}: sealed-interpreter "
                    f"{identity_field} is stale"
                )
        flags = sealed_interpreter["flags"]
        expected_flags = {
            "isolated": True,
            "ignore_environment": True,
            "no_site": True,
            "no_user_site": True,
            "safe_path": True,
        }
        if (
            not isinstance(flags, dict)
            or set(flags) != set(expected_flags)
            or not all(isinstance(flag, bool) for flag in flags.values())
        ):
            raise EvidenceError(
                f"{path}:{record_number}: sealed-interpreter flags are malformed"
            )
        overridden_env = sealed_interpreter["overridden_env"]
        if (
            not isinstance(overridden_env, list)
            or not all(
                isinstance(name, str) and name.startswith("PYTHON")
                for name in overridden_env
            )
            or overridden_env != sorted(set(overridden_env))
        ):
            raise EvidenceError(
                f"{path}:{record_number}: sealed-interpreter environment names "
                "are malformed"
            )
        if value["reason_code"] == "sealed_interpreter_unsealed_startup":
            if flags == expected_flags:
                raise EvidenceError(
                    f"{path}:{record_number}: unsealed-startup reason lacks effect"
                )
        elif flags != expected_flags:
            raise EvidenceError(
                f"{path}:{record_number}: sealed interpreter lacks -I -S facts"
            )
        if value["reason_code"] == "sealed_interpreter_hostile_environment":
            if not overridden_env:
                raise EvidenceError(
                    f"{path}:{record_number}: hostile-interpreter reason lacks names"
                )
        elif overridden_env:
            raise EvidenceError(
                f"{path}:{record_number}: non-hostile result carries Python channels"
            )
    if not isinstance(value["argv"], list) or not value["argv"] or not all(
        isinstance(item, str) for item in value["argv"]
    ):
        raise EvidenceError(
            f"{path}:{record_number}: supervisor argv is not a string array"
        )
    if (
        not isinstance(value["stage_id"], str)
        or not value["stage_id"]
        or value["stage_id"] != expected_stage_id
    ):
        raise EvidenceError(
            f"{path}:{record_number}: supervisor stage identity mismatch"
        )
    if not isinstance(value["planted"], bool):
        raise EvidenceError(
            f"{path}:{record_number}: supervisor planted flag is not boolean"
        )
    if (
        not isinstance(value["argv_redacted"], bool)
        or not isinstance(value["cwd"], str)
        or not value["cwd"]
        or not Path(value["cwd"]).is_absolute()
        or not isinstance(value["classification"], str)
        or not isinstance(value["reason_code"], str)
        or not value["reason_code"]
    ):
        raise EvidenceError(
            f"{path}:{record_number}: malformed supervisor scalar facts"
        )
    if value["child_exit"] is not None and (
        not isinstance(value["child_exit"], int)
        or isinstance(value["child_exit"], bool)
        or not 0 <= value["child_exit"] <= 255
    ):
        raise EvidenceError(f"{path}:{record_number}: malformed child exit")
    valid_signal_names = {member.name for member in signal.Signals}
    if value["child_signal"] is not None and value["child_signal"] not in (
        valid_signal_names
    ):
        raise EvidenceError(f"{path}:{record_number}: malformed child signal")
    if value["cancel_signal"] not in {None, "SIGHUP", "SIGINT", "SIGTERM"}:
        raise EvidenceError(f"{path}:{record_number}: malformed cancel signal")
    if (
        not isinstance(value["errors"], list)
        or not all(isinstance(item, str) and item for item in value["errors"])
    ):
        raise EvidenceError(f"{path}:{record_number}: malformed supervisor errors")
    host = value["host"]
    if (
        not isinstance(host, dict)
        or set(host) != {"platform", "machine", "python"}
        or not all(isinstance(item, str) and item for item in host.values())
    ):
        raise EvidenceError(f"{path}:{record_number}: malformed supervisor host facts")
    for key in ("started_utc", "ended_utc"):
        if not isinstance(value[key], str):
            raise EvidenceError(f"{path}:{record_number}: malformed UTC timing")
        try:
            parsed_utc = dt.datetime.fromisoformat(value[key])
        except ValueError as error:
            raise EvidenceError(
                f"{path}:{record_number}: malformed UTC timing"
            ) from error
        if (
            parsed_utc.tzinfo is None
            or parsed_utc.utcoffset() != dt.timedelta(0)
        ):
            raise EvidenceError(f"{path}:{record_number}: timing is not UTC")
    semantic_exits = value["semantic_failure_exits"]
    if (
        not isinstance(semantic_exits, list)
        or semantic_exits != sorted(set(semantic_exits))
        or any(
            not isinstance(item, int)
            or isinstance(item, bool)
            or item <= 0
            or item > 255
            for item in semantic_exits
        )
    ):
        raise EvidenceError(f"{path}:{record_number}: malformed semantic failure exits")
    for key in ("monotonic_start_ns", "monotonic_end_ns", "duration_ns"):
        if (
            not isinstance(value[key], int)
            or isinstance(value[key], bool)
            or value[key] < 0
        ):
            raise EvidenceError(f"{path}:{record_number}: malformed supervisor timing")
    if value["monotonic_end_ns"] - value["monotonic_start_ns"] != value["duration_ns"]:
        raise EvidenceError(f"{path}:{record_number}: supervisor duration mismatch")
    if schema in {
        "fln.supervisor/2",
        "fln.supervisor/3",
        "fln.supervisor/4",
        "fln.supervisor/5",
    }:
        phase = value["phase_timing"]
        expected_phase_keys = {
            "admission_protocol",
            "setup_start_ns",
            "readiness_ns",
            "release_decision_ns",
            "setup_end_ns",
            "setup_duration_ns",
            "execution_start_ns",
            "child_reaped_ns",
            "execution_duration_ns",
        }
        if schema in {
            "fln.supervisor/3",
            "fln.supervisor/4",
            "fln.supervisor/5",
        }:
            expected_phase_keys.update(
                {
                    "setup_deadline_ns",
                    "synthetic_cancel_deadline_ns",
                    "termination_decision_ns",
                    "child_terminal_observed_ns",
                }
            )
        if not isinstance(phase, dict) or set(phase) != expected_phase_keys:
            raise EvidenceError(
                f"{path}:{record_number}: malformed supervisor phase timing"
            )
        expected_admission_protocol = (
            "same_pid_stopped_exec_pidfd/1"
            if schema == "fln.supervisor/2"
            else "same_pid_stopped_private_gate_pidfd/1"
        )
        if phase["admission_protocol"] != expected_admission_protocol:
            raise EvidenceError(
                f"{path}:{record_number}: unknown target admission protocol"
            )
        for key in (
            "setup_start_ns",
            "setup_end_ns",
            "setup_duration_ns",
            *(
                ("setup_deadline_ns",)
                if schema
                in {
                    "fln.supervisor/3",
                    "fln.supervisor/4",
                    "fln.supervisor/5",
                }
                else ()
            ),
        ):
            if (
                not isinstance(phase[key], int)
                or isinstance(phase[key], bool)
                or phase[key] < 0
            ):
                raise EvidenceError(
                    f"{path}:{record_number}: malformed phase timing {key}"
                )
        for key in (
            "readiness_ns",
            "release_decision_ns",
            "execution_start_ns",
            "child_reaped_ns",
            "execution_duration_ns",
            *(
                ("synthetic_cancel_deadline_ns", "termination_decision_ns")
                if schema
                in {
                    "fln.supervisor/3",
                    "fln.supervisor/4",
                    "fln.supervisor/5",
                }
                else ()
            ),
            *(
                ("child_terminal_observed_ns",)
                if schema
                in {
                    "fln.supervisor/3",
                    "fln.supervisor/4",
                    "fln.supervisor/5",
                }
                else ()
            ),
        ):
            if phase[key] is not None and (
                not isinstance(phase[key], int)
                or isinstance(phase[key], bool)
                or phase[key] < 0
            ):
                raise EvidenceError(
                    f"{path}:{record_number}: malformed phase timing {key}"
                )
        if (
            phase["setup_start_ns"] != value["monotonic_start_ns"]
            or phase["setup_end_ns"] - phase["setup_start_ns"]
            != phase["setup_duration_ns"]
            or phase["setup_end_ns"] > value["monotonic_end_ns"]
        ):
            raise EvidenceError(
                f"{path}:{record_number}: inconsistent setup phase timing"
            )
        readiness_ns = phase["readiness_ns"]
        release_ns = phase["release_decision_ns"]
        execution_ns = phase["execution_start_ns"]
        child_terminal_observed_ns = phase.get("child_terminal_observed_ns")
        child_reaped_ns = phase["child_reaped_ns"]
        synthetic_cancel_deadline_ns = phase.get("synthetic_cancel_deadline_ns")
        termination_decision_ns = phase.get("termination_decision_ns")
        if readiness_ns is not None and not (
            phase["setup_start_ns"] <= readiness_ns <= phase["setup_end_ns"]
        ):
            raise EvidenceError(
                f"{path}:{record_number}: readiness lies outside setup phase"
            )
        if release_ns is not None and (
            readiness_ns is None
            or not readiness_ns <= release_ns <= phase["setup_end_ns"]
            or (
                schema
                in {
                    "fln.supervisor/3",
                    "fln.supervisor/4",
                    "fln.supervisor/5",
                }
                and release_ns >= phase["setup_deadline_ns"]
            )
        ):
            raise EvidenceError(
                f"{path}:{record_number}: release decision timing is inconsistent"
            )
        if execution_ns is None:
            if phase["execution_duration_ns"] is not None:
                raise EvidenceError(
                    f"{path}:{record_number}: unstarted execution has a duration"
                )
        else:
            terminal_ns = (
                child_reaped_ns
                if schema == "fln.supervisor/2"
                else child_terminal_observed_ns
            )
            if (
                release_ns is None
                or execution_ns != phase["setup_end_ns"]
                or execution_ns < release_ns
                or terminal_ns is None
                or terminal_ns < execution_ns
                or child_reaped_ns is None
                or child_reaped_ns < terminal_ns
                or phase["execution_duration_ns"] != terminal_ns - execution_ns
                or child_reaped_ns > value["monotonic_end_ns"]
            ):
                raise EvidenceError(
                    f"{path}:{record_number}: inconsistent execution phase timing"
                )
        if schema in {
            "fln.supervisor/3",
            "fln.supervisor/4",
            "fln.supervisor/5",
        } and synthetic_cancel_deadline_ns is not None and (
            execution_ns is None
            or synthetic_cancel_deadline_ns < execution_ns
        ):
            raise EvidenceError(
                f"{path}:{record_number}: synthetic cancellation predates execution"
            )
        if schema in {
            "fln.supervisor/3",
            "fln.supervisor/4",
            "fln.supervisor/5",
        } and termination_decision_ns is not None and not (
            phase["setup_start_ns"]
            <= termination_decision_ns
            <= value["monotonic_end_ns"]
        ):
            raise EvidenceError(
                f"{path}:{record_number}: termination decision timing is inconsistent"
            )
        for key in (
            "readiness_ns",
            "release_decision_ns",
            "execution_start_ns",
            "child_reaped_ns",
            *(
                (
                    "synthetic_cancel_deadline_ns",
                    "termination_decision_ns",
                    "child_terminal_observed_ns",
                )
                if schema
                in {
                    "fln.supervisor/3",
                    "fln.supervisor/4",
                    "fln.supervisor/5",
                }
                else ()
            ),
        ):
            timestamp = phase[key]
            if timestamp is not None and (
                timestamp < phase["setup_start_ns"]
                or (
                    key != "synthetic_cancel_deadline_ns"
                    and timestamp > value["monotonic_end_ns"]
                )
            ):
                raise EvidenceError(
                    f"{path}:{record_number}: phase timestamp lies outside run: {key}"
                )
        if schema in {
            "fln.supervisor/3",
            "fln.supervisor/4",
            "fln.supervisor/5",
        } and (
            (child_terminal_observed_ns is None)
            != (child_reaped_ns is None)
            or (
                child_terminal_observed_ns is not None
                and child_reaped_ns < child_terminal_observed_ns
            )
        ):
            raise EvidenceError(
                f"{path}:{record_number}: child observation/reap timing mismatch"
            )
        target_exec = value["target_exec"]
        if (
            not isinstance(target_exec, dict)
            or set(target_exec) != {"status", "failure"}
            or target_exec["status"]
            not in {"succeeded", "failed", "not_released", "unknown"}
        ):
            raise EvidenceError(
                f"{path}:{record_number}: malformed target exec status"
            )
        if target_exec["status"] == "failed":
            failure = target_exec["failure"]
            if (
                not isinstance(failure, dict)
                or set(failure)
                != {"schema", "status", "error_type", "errno", "errno_name"}
                or failure.get("schema") != "fln.exec-status/1"
                or failure.get("status") != "failed"
                or not isinstance(failure.get("error_type"), str)
                or not failure["error_type"]
                or (
                    failure.get("errno") is not None
                    and (
                        not isinstance(failure["errno"], int)
                        or isinstance(failure["errno"], bool)
                        or failure["errno"] <= 0
                        or failure.get("errno_name")
                        != errno.errorcode.get(failure["errno"])
                    )
                )
                or (
                    failure.get("errno") is None
                    and failure.get("errno_name") is not None
                )
            ):
                raise EvidenceError(
                    f"{path}:{record_number}: malformed target exec failure"
                )
        elif target_exec["failure"] is not None:
            raise EvidenceError(
                f"{path}:{record_number}: non-failed exec has failure facts"
            )
        if (
            execution_ns is None
            and target_exec["status"] != "not_released"
        ) or (
            execution_ns is not None
            and target_exec["status"] == "not_released"
        ):
            raise EvidenceError(
                f"{path}:{record_number}: target exec/release status mismatch"
            )
        if target_exec["status"] == "failed" and value["classification"] in {
            "pass",
            "fail",
        }:
            raise EvidenceError(
                f"{path}:{record_number}: target exec failure was misclassified"
            )
        if (
            value["classification"] in {"pass", "fail"}
            and target_exec["status"] != "succeeded"
        ):
            raise EvidenceError(
                f"{path}:{record_number}: terminal verdict lacks target exec proof"
            )
        if (
            value["classification"] == "internal_fault"
            and value["reason_code"] == "unexpected_child_exit"
            and target_exec["status"] != "succeeded"
        ):
            raise EvidenceError(
                f"{path}:{record_number}: child-exit fault lacks target exec proof"
            )
        if target_exec["status"] == "not_released" and value["classification"] in {
            "pass",
            "fail",
        }:
            raise EvidenceError(
                f"{path}:{record_number}: unreleased target has a semantic outcome"
            )
        if schema in {
            "fln.supervisor/3",
            "fln.supervisor/4",
            "fln.supervisor/5",
        }:
            test_control = value["test_control"]
            if (
                not isinstance(test_control, dict)
                or set(test_control)
                != {
                    "before_stop_delay_ms",
                    "before_release_delay_ms",
                    "gate_mode",
                    "terminal_delay_ms",
                    "terminal_ready_enabled",
                    "fault_point",
                }
                or not isinstance(test_control["before_stop_delay_ms"], int)
                or isinstance(test_control["before_stop_delay_ms"], bool)
                or test_control["before_stop_delay_ms"] < 0
                or not isinstance(test_control["before_release_delay_ms"], int)
                or isinstance(test_control["before_release_delay_ms"], bool)
                or test_control["before_release_delay_ms"] < 0
                or not isinstance(test_control["terminal_delay_ms"], int)
                or isinstance(test_control["terminal_delay_ms"], bool)
                or test_control["terminal_delay_ms"] < 0
                or not isinstance(test_control["terminal_ready_enabled"], bool)
                or test_control["fault_point"] not in SUPERVISOR_TEST_FAULT_POINTS
                or test_control["gate_mode"]
                not in {
                    "normal",
                    "exit_before_stop",
                    "never_stop",
                    "die_after_stop",
                }
            ):
                raise EvidenceError(
                    f"{path}:{record_number}: malformed stopped-gate test control"
                )
            if (
                test_control["before_stop_delay_ms"] != 0
                or test_control["before_release_delay_ms"] != 0
                or test_control["gate_mode"] != "normal"
                or test_control["terminal_delay_ms"] != 0
                or test_control["terminal_ready_enabled"]
                or test_control["fault_point"] != "none"
            ) and value["planted"] is not True:
                raise EvidenceError(
                    f"{path}:{record_number}: injected gate fault is not planted"
                )
            fault_point = test_control["fault_point"]
            if fault_point == "metadata_parent_open":
                raise EvidenceError(
                    f"{path}:{record_number}: metadata-open fault cannot publish metadata"
                )
            if fault_point in {"capture_stdout", "capture_stderr"}:
                stream = fault_point.removeprefix("capture_")
                if (
                    value["classification"] != "internal_fault"
                    or value["reason_code"] != "artifact_publication_failure"
                    or not any(
                        error.startswith(
                            f"capture publication failure: {stream}:"
                        )
                        for error in value["errors"]
                    )
                ):
                    raise EvidenceError(
                        f"{path}:{record_number}: planted capture fault lacks effect"
                    )
            if fault_point == "readiness_publication" and (
                value["classification"] != "internal_fault"
                or value["reason_code"] != "supervisor_or_capture_failure"
                or value["phase_timing"]["readiness_ns"] is not None
                or value["phase_timing"]["execution_start_ns"] is not None
                or not any(
                    "injected readiness publication failure" in error
                    for error in value["errors"]
                )
            ):
                raise EvidenceError(
                    f"{path}:{record_number}: planted readiness fault lacks effect"
                )
            if fault_point in {"thread_start_stdout", "thread_start_stderr"}:
                stream = fault_point.removeprefix("thread_start_")
                if (
                    value["classification"] != "internal_fault"
                    or value["reason_code"] != "supervisor_or_capture_failure"
                    or value["phase_timing"]["execution_start_ns"] is not None
                    or not any(
                        f"injected {stream} drainer start failure" in error
                        for error in value["errors"]
                    )
                ):
                    raise EvidenceError(
                        f"{path}:{record_number}: planted thread fault lacks effect"
                    )
            if fault_point == "admission_fd_exhaustion" and (
                value["classification"] != "internal_fault"
                or value["reason_code"] != "supervisor_or_capture_failure"
                or value["phase_timing"]["execution_start_ns"] is not None
                or not any(
                    "Too many open files" in error for error in value["errors"]
                )
            ):
                raise EvidenceError(
                    f"{path}:{record_number}: planted descriptor exhaustion lacks effect"
                )
    expected_wrapper = {
        "pass": 0,
        "fail": 1,
        "internal_fault": 2,
        "inconclusive": 3,
        "cancelled": 4,
    }
    classification = value["classification"]
    if (
        classification not in expected_wrapper
        or value["wrapper_exit"] != expected_wrapper[classification]
    ):
        raise EvidenceError(
            f"{path}:{record_number}: supervisor classification/exit mismatch"
        )
    allowed_reason_codes = {
        "pass": {"exit_zero"},
        "fail": {"child_exit_semantic_failure"},
        "internal_fault": {
            "artifact_publication_failure",
            "supervisor_or_capture_failure",
            "unexpected_child_exit",
            "target_exec_failure",
            # Sealed compiler environment (bead fln-evidence-runner-bootstrap-
            # btk): typed setup faults of the compiler-sealing envelope step.
            "sealed_compiler_hostile_environment",
            "sealed_compiler_ambient_config",
            "sealed_compiler_lock_unreadable",
            "sealed_compiler_lock_incomplete",
            "sealed_compiler_toolchain_toml_unreadable",
            "sealed_compiler_channel_disagreement",
            "sealed_compiler_unsupported_host",
            "sealed_compiler_toolchain_unresolved",
            "sealed_compiler_probe_failure",
            "sealed_compiler_identity_mismatch",
            "sealed_compiler_build_root_unavailable",
            "sealed_interpreter_unsealed_startup",
            "sealed_interpreter_hostile_environment",
        },
        "inconclusive": {
            "setup_timeout",
            "timeout",
            "output_budget_exhausted",
            *(f"child_signal_{name}" for name in valid_signal_names),
        },
        "cancelled": {"signal_SIGHUP", "signal_SIGINT", "signal_SIGTERM"},
    }
    if value["reason_code"] not in allowed_reason_codes[classification]:
        raise EvidenceError(
            f"{path}:{record_number}: classification/reason mismatch"
        )
    if schema == "fln.supervisor/1" and value["reason_code"] == "target_exec_failure":
        raise EvidenceError(
            f"{path}:{record_number}: legacy envelope claims target exec proof"
        )
    if value["errors"] and classification != "internal_fault":
        raise EvidenceError(
            f"{path}:{record_number}: non-internal outcome carries supervisor errors"
        )
    if value["reason_code"] == "supervisor_or_capture_failure" and not value["errors"]:
        raise EvidenceError(
            f"{path}:{record_number}: supervisor failure lacks recorded error"
        )
    if value["reason_code"] == "artifact_publication_failure" and not any(
        error.startswith("capture publication failure:") for error in value["errors"]
    ):
        raise EvidenceError(
            f"{path}:{record_number}: artifact failure lacks publication error"
        )
    if (
        value["errors"]
        and value["reason_code"]
        not in {
            "artifact_publication_failure",
            "supervisor_or_capture_failure",
        }
        and not (
            value["reason_code"].startswith("sealed_compiler_")
            and any(
                error.startswith("sealed compiler rejection:")
                for error in value["errors"]
            )
        )
        and not (
            value["reason_code"].startswith("sealed_interpreter_")
            and any(
                error.startswith("sealed interpreter rejection:")
                for error in value["errors"]
            )
        )
    ):
        raise EvidenceError(
            f"{path}:{record_number}: recorded errors do not bind terminal reason"
        )
    if (
        schema
        in {
            "fln.supervisor/2",
            "fln.supervisor/3",
            "fln.supervisor/4",
            "fln.supervisor/5",
        }
        and value["reason_code"] == "target_exec_failure"
        and value["target_exec"]["status"] != "failed"
    ):
        raise EvidenceError(
            f"{path}:{record_number}: target exec reason lacks failure status"
        )
    if (value["child_exit"] is None) == (value["child_signal"] is None):
        if not (
            value["child_exit"] is None
            and value["child_signal"] is None
            and classification
            in {"internal_fault", "inconclusive", "cancelled"}
        ):
            raise EvidenceError(
                f"{path}:{record_number}: child terminal facts are inconsistent"
            )
    if classification in {"pass", "fail"} and value["cancel_signal"] is not None:
        raise EvidenceError(
            f"{path}:{record_number}: conclusive target has cancellation facts"
        )
    if classification == "cancelled" and (
        value["cancel_signal"] is None
        or value["reason_code"] != f"signal_{value['cancel_signal']}"
    ):
        raise EvidenceError(
            f"{path}:{record_number}: cancellation reason/signal mismatch"
        )
    if classification == "pass" and (
        value["child_exit"] != 0 or value["child_signal"] is not None
    ):
        raise EvidenceError(
            f"{path}:{record_number}: passing supervisor has nonzero child"
        )
    if classification == "fail" and (
        value["child_exit"] not in semantic_exits or value["child_signal"] is not None
    ):
        raise EvidenceError(
            f"{path}:{record_number}: failed supervisor lacks semantic failure"
        )
    if value["reason_code"] == "unexpected_child_exit" and (
        value["child_exit"] in {None, 0}
        or value["child_exit"] in semantic_exits
        or value["child_signal"] is not None
    ):
        raise EvidenceError(
            f"{path}:{record_number}: unexpected-exit reason lacks child exit"
        )
    if classification == "inconclusive" and value["reason_code"].startswith(
        "child_signal_"
    ):
        if (
            not isinstance(value["child_signal"], str)
            or value["child_exit"] is not None
            or value["reason_code"] != f"child_signal_{value['child_signal']}"
        ):
            raise EvidenceError(
                f"{path}:{record_number}: child signal is not typed inconclusive"
            )
    if (
        classification == "internal_fault"
        and not (
            schema
            in {
                "fln.supervisor/2",
                "fln.supervisor/3",
                "fln.supervisor/4",
                "fln.supervisor/5",
            }
            and value["reason_code"] == "target_exec_failure"
            and value["target_exec"]["status"] == "failed"
        )
        and value["child_exit"] not in {None, 0}
    ):
        if value["child_exit"] in semantic_exits:
            raise EvidenceError(
                f"{path}:{record_number}: semantic child failure was marked internal"
            )
    resource_facts = value["resource"]
    if not isinstance(resource_facts, dict):
        raise EvidenceError(
            f"{path}:{record_number}: supervisor resource facts missing"
        )
    expected_resource_keys = {
        "capture_bytes_per_stream",
        "output_budget_bytes",
        "kill_grace_ms",
        "total_output_bytes",
        "user_cpu_seconds",
        "system_cpu_seconds",
        "max_rss_kib_observed",
        "term_sent",
        "kill_sent",
        "process_tree_scope",
        "surviving_pids",
    }
    if schema == "fln.supervisor/1":
        expected_resource_keys.add("timeout_ms")
    elif schema == "fln.supervisor/2":
        expected_resource_keys.update({"setup_timeout_ms", "timeout_ms"})
    else:
        expected_resource_keys.update(
            {"setup_timeout_ms", "execution_timeout_ms", "cancel_after_ms"}
        )
    if set(resource_facts) != expected_resource_keys:
        raise EvidenceError(
            f"{path}:{record_number}: supervisor resource shape mismatch"
        )
    positive_integer_facts = (
        "capture_bytes_per_stream",
        "output_budget_bytes",
        "kill_grace_ms",
    )
    if schema == "fln.supervisor/2":
        positive_integer_facts = (
            *positive_integer_facts,
            "setup_timeout_ms",
            "timeout_ms",
        )
    elif schema in {
        "fln.supervisor/3",
        "fln.supervisor/4",
        "fln.supervisor/5",
    }:
        positive_integer_facts = (
            *positive_integer_facts,
            "setup_timeout_ms",
            "execution_timeout_ms",
        )
    else:
        positive_integer_facts = (*positive_integer_facts, "timeout_ms")
    for key in positive_integer_facts:
        fact = resource_facts.get(key)
        if not isinstance(fact, int) or isinstance(fact, bool) or fact <= 0:
            raise EvidenceError(
                f"{path}:{record_number}: malformed resource fact {key}"
            )
    if schema in {
        "fln.supervisor/3",
        "fln.supervisor/4",
        "fln.supervisor/5",
    }:
        cancel_after = resource_facts.get("cancel_after_ms")
        if cancel_after is not None and (
            not isinstance(cancel_after, int)
            or isinstance(cancel_after, bool)
            or cancel_after < 0
        ):
            raise EvidenceError(
                f"{path}:{record_number}: malformed cancel-after budget"
            )
        execution_ns = value["phase_timing"]["execution_start_ns"]
        cancel_deadline_ns = value["phase_timing"]["synthetic_cancel_deadline_ns"]
        expected_cancel_deadline = (
            execution_ns + cancel_after * 1_000_000
            if execution_ns is not None and cancel_after is not None
            else None
        )
        if cancel_deadline_ns != expected_cancel_deadline:
            raise EvidenceError(
                f"{path}:{record_number}: synthetic cancellation deadline mismatch"
            )
        if (
            classification in {"pass", "fail"}
            and cancel_deadline_ns is not None
            and value["phase_timing"]["child_terminal_observed_ns"]
            >= cancel_deadline_ns
        ):
            raise EvidenceError(
                f"{path}:{record_number}: conclusive target crossed cancellation deadline"
            )
        phase = value["phase_timing"]
        if (
            phase["setup_deadline_ns"]
            != phase["setup_start_ns"]
            + resource_facts["setup_timeout_ms"] * 1_000_000
        ):
            raise EvidenceError(
                f"{path}:{record_number}: setup deadline/budget mismatch"
            )
        execution_duration = phase["execution_duration_ns"]
        if classification in {"pass", "fail"} and (
            execution_duration is None
            or execution_duration
            > resource_facts["execution_timeout_ms"] * 1_000_000
        ):
            raise EvidenceError(
                f"{path}:{record_number}: conclusive execution exceeded its budget"
            )
        if classification in {"pass", "fail"} and phase[
            "termination_decision_ns"
        ] is not None:
            raise EvidenceError(
                f"{path}:{record_number}: conclusive execution has termination decision"
            )
        if value["reason_code"] == "timeout":
            expected_timeout_ns = (
                phase["execution_start_ns"]
                + resource_facts["execution_timeout_ms"] * 1_000_000
            )
            if (
                phase["execution_start_ns"] is None
                or phase["termination_decision_ns"] is None
                or phase["termination_decision_ns"] < expected_timeout_ns
            ):
                raise EvidenceError(
                    f"{path}:{record_number}: execution timeout decision is premature"
                )
        if value["reason_code"] == "setup_timeout" and (
            phase["termination_decision_ns"] is None
            or phase["termination_decision_ns"] < phase["setup_deadline_ns"]
            or phase["release_decision_ns"] is not None
            or phase["execution_start_ns"] is not None
            or value["target_exec"]["status"] != "not_released"
        ):
            raise EvidenceError(
                f"{path}:{record_number}: setup timeout decision is premature"
            )
        if value["reason_code"] == "output_budget_exhausted" and (
            phase["execution_start_ns"] is None
            or phase["termination_decision_ns"] is None
            or phase["termination_decision_ns"] < phase["execution_start_ns"]
        ):
            raise EvidenceError(
                f"{path}:{record_number}: output termination decision is missing"
            )
        if (
            phase["termination_decision_ns"] is not None
            and phase["execution_start_ns"] is not None
            and value["reason_code"] != "setup_timeout"
            and phase["termination_decision_ns"] < phase["execution_start_ns"]
        ):
            raise EvidenceError(
                f"{path}:{record_number}: runtime termination predates execution"
            )
    if (
        resource_facts["output_budget_bytes"]
        < resource_facts["capture_bytes_per_stream"]
    ):
        raise EvidenceError(f"{path}:{record_number}: impossible output budget")
    for key in ("total_output_bytes", "max_rss_kib_observed"):
        fact = resource_facts.get(key)
        if not isinstance(fact, int) or isinstance(fact, bool) or fact < 0:
            raise EvidenceError(
                f"{path}:{record_number}: malformed resource fact {key}"
            )
    for key in ("user_cpu_seconds", "system_cpu_seconds"):
        fact = resource_facts.get(key)
        if (
            not isinstance(fact, (int, float))
            or isinstance(fact, bool)
            or not float(fact) >= 0.0
            or not float(fact) < float("inf")
        ):
            raise EvidenceError(
                f"{path}:{record_number}: malformed resource fact {key}"
            )
    for key in ("term_sent", "kill_sent"):
        if not isinstance(resource_facts.get(key), bool):
            raise EvidenceError(
                f"{path}:{record_number}: malformed resource fact {key}"
            )
    if classification in {"pass", "fail"} and (
        resource_facts["term_sent"] or resource_facts["kill_sent"]
    ):
        raise EvidenceError(
            f"{path}:{record_number}: conclusive outcome required forced cleanup"
        )
    if classification == "inconclusive" and value["cancel_signal"] is not None:
        raise EvidenceError(
            f"{path}:{record_number}: inconclusive outcome carries cancellation"
        )
    if (
        schema
        in {
            "fln.supervisor/2",
            "fln.supervisor/3",
            "fln.supervisor/4",
            "fln.supervisor/5",
        }
        and value["reason_code"].startswith("child_signal_")
        and (
            value["phase_timing"]["execution_start_ns"] is None
            or value["target_exec"]["status"] in {"not_released", "failed"}
        )
    ):
        raise EvidenceError(
            f"{path}:{record_number}: child signal lacks released target execution"
        )
    if (
        schema
        in {
            "fln.supervisor/2",
            "fln.supervisor/3",
            "fln.supervisor/4",
            "fln.supervisor/5",
        }
        and value["reason_code"] == "target_exec_failure"
        and (
            value["phase_timing"]["execution_start_ns"] is None
            or value["child_exit"] != SETUP_FAILURE
            or value["child_signal"] is not None
            or value["errors"]
        )
    ):
        raise EvidenceError(
            f"{path}:{record_number}: target exec failure facts are inconsistent"
        )
    if resource_facts.get("process_tree_scope") not in {
        "linux_nested_subreapers_pidfd_procfs_best_effort",
        "linux_subreaper_pidfd_procfs_best_effort",
    }:
        raise EvidenceError(f"{path}:{record_number}: unknown process-tree scope")
    if resource_facts.get("surviving_pids") != []:
        raise EvidenceError(f"{path}:{record_number}: supervisor left live descendants")
    readiness_name = value["readiness"]
    if (
        not isinstance(readiness_name, str)
        or not readiness_name
        or Path(readiness_name).is_absolute()
        or Path(readiness_name).name != readiness_name
    ):
        raise EvidenceError(f"{path}:{record_number}: malformed readiness path")
    readiness_path = require_within(
        path.parent / readiness_name, path.parent, label="readiness artifact"
    )
    readiness_data, _readiness_size, _readiness_digest = stable_file_facts(
        readiness_path, max_bytes=MAX_RECORD_BYTES
    )
    readiness = parse_json(readiness_data, subject=str(readiness_path))
    if not isinstance(readiness, dict):
        raise EvidenceError(f"{path}:{record_number}: malformed readiness artifact")
    readiness_keys = {
        "schema",
        "stage_id",
        "wrapper_pid",
        "wrapper_start_ticks",
        "supervisor_pid",
        "supervisor_start_ticks",
        "child_pid",
        "child_pgid",
        "child_start_ticks",
        "monotonic_ns",
        "status",
    }
    if readiness.get("schema") == "fln.supervisor-readiness/3":
        readiness_keys.add("child_sid")
    if (
        set(readiness) != readiness_keys
        or not isinstance(readiness.get("monotonic_ns"), int)
        or isinstance(readiness.get("monotonic_ns"), bool)
        or readiness.get("monotonic_ns", 0) <= 0
        or readiness.get("schema")
        not in {
            "fln.supervisor-readiness/1",
            "fln.supervisor-readiness/2",
            "fln.supervisor-readiness/3",
        }
        or readiness.get("stage_id") != expected_stage_id
    ):
        raise EvidenceError(f"{path}:{record_number}: malformed readiness artifact")
    if (
        schema == "fln.supervisor/1"
        and readiness.get("schema") != "fln.supervisor-readiness/1"
    ) or (
        schema == "fln.supervisor/2"
        and readiness.get("schema") != "fln.supervisor-readiness/2"
    ) or (
        schema
        in {
            "fln.supervisor/3",
            "fln.supervisor/4",
            "fln.supervisor/5",
        }
        and readiness.get("schema") != "fln.supervisor-readiness/3"
    ):
        raise EvidenceError(f"{path}:{record_number}: supervisor/readiness version drift")
    readiness_status = readiness.get("status")
    allowed_readiness = (
        {"ready", "spawn_failed"}
        if schema == "fln.supervisor/1"
        else {"ready", "setup_failed", "setup_timeout", "setup_cancelled"}
    )
    if readiness_status not in allowed_readiness:
        raise EvidenceError(f"{path}:{record_number}: unknown readiness status")
    expected_readiness_class = {
        "spawn_failed": ("internal_fault", None),
        "setup_failed": ("internal_fault", None),
        "setup_timeout": ("inconclusive", "setup_timeout"),
        "setup_cancelled": ("cancelled", None),
    }.get(readiness_status)
    if expected_readiness_class is not None:
        later_internal_override = classification == "internal_fault"
        later_cancel_override = (
            readiness_status == "setup_timeout" and classification == "cancelled"
        )
        phase_terminal = (
            classification == expected_readiness_class[0]
            and (
                expected_readiness_class[1] is None
                or value["reason_code"] == expected_readiness_class[1]
            )
        )
        if (
            not later_internal_override
            and not later_cancel_override
            and not phase_terminal
        ):
            raise EvidenceError(
                f"{path}:{record_number}: readiness/terminal classification mismatch"
            )
    if schema in {
        "fln.supervisor/2",
        "fln.supervisor/3",
        "fln.supervisor/4",
        "fln.supervisor/5",
    }:
        phase = value["phase_timing"]
        if readiness_status == "ready":
            if readiness["monotonic_ns"] != phase["readiness_ns"]:
                raise EvidenceError(
                    f"{path}:{record_number}: readiness timestamp was not bound"
                )
        elif phase["readiness_ns"] is not None:
            raise EvidenceError(
                f"{path}:{record_number}: failed setup claims ready-phase timing"
            )
    wrapper_pid = readiness.get("wrapper_pid")
    wrapper_ticks = readiness.get("wrapper_start_ticks")
    supervisor_pid = readiness.get("supervisor_pid")
    supervisor_ticks = readiness.get("supervisor_start_ticks")
    if (
        not isinstance(wrapper_pid, int)
        or isinstance(wrapper_pid, bool)
        or wrapper_pid <= 1
        or not isinstance(wrapper_ticks, int)
        or isinstance(wrapper_ticks, bool)
        or wrapper_ticks <= 0
        or not isinstance(supervisor_pid, int)
        or isinstance(supervisor_pid, bool)
        or supervisor_pid <= 1
        or not isinstance(supervisor_ticks, int)
        or isinstance(supervisor_ticks, bool)
        or supervisor_ticks <= 0
        or (
            supervisor_pid == wrapper_pid and supervisor_ticks != wrapper_ticks
        )
    ):
        raise EvidenceError(
            f"{path}:{record_number}: malformed wrapper readiness identity"
        )
    expected_scope = (
        "linux_nested_subreapers_pidfd_procfs_best_effort"
        if supervisor_pid != wrapper_pid
        else "linux_subreaper_pidfd_procfs_best_effort"
    )
    if resource_facts.get("process_tree_scope") != expected_scope:
        raise EvidenceError(
            f"{path}:{record_number}: readiness/process-tree scope mismatch"
        )
    if readiness_status == "ready":
        child_pid = readiness.get("child_pid")
        child_pgid = readiness.get("child_pgid")
        child_sid = readiness.get("child_sid", child_pid)
        child_ticks = readiness.get("child_start_ticks")
        if (
            not isinstance(child_pid, int)
            or isinstance(child_pid, bool)
            or child_pid <= 1
            or child_pid != child_pgid
            or child_pid != child_sid
            or not isinstance(child_ticks, int)
            or isinstance(child_ticks, bool)
            or child_ticks <= 0
            or child_pid in {wrapper_pid, supervisor_pid}
        ):
            raise EvidenceError(
                f"{path}:{record_number}: malformed child readiness identity"
            )
    elif any(
        readiness.get(key) is not None
        for key in ("child_pid", "child_pgid", "child_sid", "child_start_ticks")
    ):
        raise EvidenceError(
            f"{path}:{record_number}: spawn-failed readiness names a child"
        )
    stream_artifacts: set[str] = set()
    expected_stream_keys = {
        "artifact",
        "sha256",
        "retained_sha256",
        "total_bytes",
        "retained_bytes",
        "head_bytes",
        "tail_bytes",
        "truncated",
    }
    for stream in ("stdout", "stderr"):
        facts = value[stream]
        if not isinstance(facts, dict) or set(facts) != expected_stream_keys:
            raise EvidenceError(f"{path}:{record_number}: missing {stream} facts")
        if (
            not isinstance(facts["artifact"], str)
            or not facts["artifact"]
            or Path(facts["artifact"]).is_absolute()
            or Path(facts["artifact"]).name != facts["artifact"]
        ):
            raise EvidenceError(
                f"{path}:{record_number}: malformed {stream} artifact name"
            )
        if facts["artifact"] in stream_artifacts:
            raise EvidenceError(f"{path}:{record_number}: streams share an artifact")
        stream_artifacts.add(facts["artifact"])
        if not SHA256_HEX.fullmatch(str(facts["sha256"])) or not SHA256_HEX.fullmatch(
            str(facts["retained_sha256"])
        ):
            raise EvidenceError(f"{path}:{record_number}: malformed {stream} digest")
        for key in ("total_bytes", "retained_bytes", "head_bytes", "tail_bytes"):
            fact = facts[key]
            if not isinstance(fact, int) or isinstance(fact, bool) or fact < 0:
                raise EvidenceError(
                    f"{path}:{record_number}: malformed {stream} size facts"
                )
        if not isinstance(facts["truncated"], bool):
            raise EvidenceError(
                f"{path}:{record_number}: malformed {stream} truncation flag"
            )
        if facts["retained_bytes"] > resource_facts["capture_bytes_per_stream"]:
            raise EvidenceError(
                f"{path}:{record_number}: {stream} capture exceeded bound"
            )
        if facts["total_bytes"] < facts["retained_bytes"]:
            raise EvidenceError(
                f"{path}:{record_number}: {stream} retained more than produced"
            )
        if facts["head_bytes"] + facts["tail_bytes"] > facts["retained_bytes"]:
            raise EvidenceError(
                f"{path}:{record_number}: impossible {stream} head/tail facts"
            )
        if not facts["truncated"] and (
            facts["total_bytes"] != facts["retained_bytes"]
            or facts["head_bytes"] != facts["retained_bytes"]
            or facts["tail_bytes"] != 0
            or not hmac.compare_digest(
                str(facts["sha256"]), str(facts["retained_sha256"])
            )
        ):
            raise EvidenceError(
                f"{path}:{record_number}: inconsistent untruncated {stream}"
            )
        if facts["truncated"] and facts["total_bytes"] <= facts["retained_bytes"]:
            raise EvidenceError(
                f"{path}:{record_number}: inconsistent truncated {stream}"
            )
        artifact = require_within(
            path.parent / str(facts["artifact"]),
            path.parent,
            label=f"{stream} artifact",
        )
        _data, size, digest = stable_file_facts(
            artifact, max_bytes=resource_facts["capture_bytes_per_stream"]
        )
        if size != facts["retained_bytes"] or not hmac.compare_digest(
            digest, str(facts["retained_sha256"])
        ):
            raise EvidenceError(
                f"{path}:{record_number}: {stream} artifact facts disagree"
            )
    if resource_facts.get("total_output_bytes") != (
        value["stdout"]["total_bytes"] + value["stderr"]["total_bytes"]
    ):
        raise EvidenceError(f"{path}:{record_number}: total output accounting mismatch")
    if (
        value["reason_code"] == "output_budget_exhausted"
        and resource_facts["total_output_bytes"]
        <= resource_facts["output_budget_bytes"]
    ):
        raise EvidenceError(
            f"{path}:{record_number}: output-budget reason lacks exhaustion"
        )
    if (
        classification in {"pass", "fail"}
        and resource_facts["total_output_bytes"] > resource_facts["output_budget_bytes"]
    ):
        raise EvidenceError(
            f"{path}:{record_number}: conclusive stage exceeded output budget"
        )


def validate_supervisor_file(path: Path, expected_stage_id: str) -> dict[str, Any]:
    data, size, digest = stable_file_facts(path, max_bytes=MAX_RECORD_BYTES)
    value = parse_json(data, subject=str(path))
    validate_supervisor_object(
        path,
        1,
        value,
        expected_stage_id=expected_stage_id,
    )
    return {
        "schema": "fln.supervisor-validation/1",
        "valid": True,
        "stage_id": expected_stage_id,
        "bytes": size,
        "sha256": digest,
    }


def sha256_file(path: Path) -> str:
    _data, _size, digest = stable_file_facts(path)
    return digest


def iter_tree_files(root: Path, requested: Sequence[str]) -> Iterable[tuple[str, Path]]:
    seen: set[str] = set()
    for raw in sorted(requested):
        raw_path = Path(raw)
        if raw_path.is_absolute() or ".." in raw_path.parts:
            raise EvidenceError(f"hash input escapes root: {raw}")
        candidate = require_within(root / raw_path, root, label="hash input")
        try:
            candidate.lstat()
        except FileNotFoundError as error:
            raise EvidenceError(f"hash input does not exist: {raw}") from error
        candidate_mode = candidate.lstat().st_mode
        paths = [candidate]
        if stat.S_ISDIR(candidate_mode):
            paths = sorted(
                candidate.rglob("*"), key=lambda item: item.as_posix().encode()
            )
        elif not (stat.S_ISREG(candidate_mode) or stat.S_ISLNK(candidate_mode)):
            raise EvidenceError(f"special file is not a canonical input: {candidate}")
        for path in paths:
            try:
                mode = path.lstat().st_mode
            except FileNotFoundError as error:
                raise EvidenceError(f"hash input disappeared: {path}") from error
            if stat.S_ISDIR(mode):
                continue
            if not (stat.S_ISREG(mode) or stat.S_ISLNK(mode)):
                raise EvidenceError(f"special file is not a canonical input: {path}")
            rel = path.relative_to(root).as_posix()
            if rel in seen:
                continue
            seen.add(rel)
            yield rel, path


def tree_hash_once(root: Path, requested: Sequence[str]) -> str:
    root = lexical_absolute(root)
    _root, root_fd = open_directory_nofollow(root, create=False)
    os.close(root_fd)
    digest = hashlib.sha256(b"fln-canonical-tree/1\0")
    count = 0
    for rel, path in iter_tree_files(root, requested):
        rel_bytes = rel.encode("utf-8")
        full_mode = path.lstat().st_mode
        mode = full_mode & 0o7777
        if stat.S_ISLNK(full_mode):
            _data, file_size, file_digest_hex = stable_symlink_facts(path)
            kind = b"L"
        else:
            _data, file_size, file_digest_hex = stable_file_facts(path)
            kind = b"F"
        file_digest = bytes.fromhex(file_digest_hex)
        digest.update(len(rel_bytes).to_bytes(8, "big"))
        digest.update(rel_bytes)
        digest.update(kind)
        digest.update(file_size.to_bytes(8, "big"))
        digest.update(mode.to_bytes(4, "big"))
        digest.update(file_digest)
        count += 1
    digest.update(count.to_bytes(8, "big"))
    return f"sha256:{digest.hexdigest()}"


def ubs_inventory_binding(inventory: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": inventory["schema"],
        "scope": inventory["scope"],
        "count": inventory["count"],
        "inventory_root": inventory["inventory_root"],
        "files": inventory["files"],
    }


def tree_hash(
    root: Path,
    requested: Sequence[str],
    *,
    inventory_path: Path | None = None,
    vendor_path: str | None = None,
) -> str:
    previous: str | None = None
    for _attempt in range(6):
        vendor_before = (
            verify_vendor_binding(root, vendor_path) if vendor_path else None
        )
        tree_root = tree_hash_once(root, requested)
        vendor_after = verify_vendor_binding(root, vendor_path) if vendor_path else None
        if vendor_before != vendor_after:
            previous = None
            continue
        components: dict[str, Any] = {
            "schema": "fln-canonical-input/2",
            "tree_root": tree_root,
        }
        if vendor_before is not None:
            components["vendor_binding"] = vendor_before
        if inventory_path is not None:
            inventory = validate_ubs_inventory(inventory_path, root)
            components["ubs_inventory"] = ubs_inventory_binding(inventory)
        if len(components) == 2:
            current = tree_root
        else:
            digest = hashlib.sha256(b"fln-canonical-input/2\0")
            digest.update(canonical_json(components))
            current = f"sha256:{digest.hexdigest()}"
        if current == previous:
            return current
        previous = current
    raise EvidenceError("canonical tree did not stabilize across consecutive snapshots")


def split_git_nul(data: bytes, *, subject: str) -> list[str]:
    if not data:
        return []
    if not data.endswith(b"\0"):
        raise EvidenceError(f"{subject} did not produce NUL-terminated paths")
    result: list[str] = []
    for raw in data[:-1].split(b"\0"):
        if not raw:
            raise EvidenceError(f"{subject} produced an empty path")
        try:
            result.append(raw.decode("utf-8"))
        except UnicodeDecodeError as error:
            raise EvidenceError(f"{subject} produced a non-UTF-8 path") from error
    return result


def git_paths(root: Path, args: Sequence[str], *, subject: str) -> list[str]:
    return split_git_nul(run_git(root, args, subject=subject), subject=subject)


def run_git(
    root: Path,
    args: Sequence[str],
    *,
    subject: str,
    accepted_exits: set[int] | None = None,
) -> bytes:
    root = lexical_absolute(root)
    git_dir = root / ".git"
    try:
        git_mode = git_dir.lstat().st_mode
    except FileNotFoundError as error:
        raise EvidenceError(f"{subject} requires an explicit repository .git directory") from error
    if stat.S_ISLNK(git_mode) or not stat.S_ISDIR(git_mode):
        raise EvidenceError(f"{subject} requires a real repository .git directory")
    git_environment = {
        key: value for key, value in os.environ.items() if not key.startswith("GIT_")
    }
    git_environment.update(
        {
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_OPTIONAL_LOCKS": "0",
            "GIT_TERMINAL_PROMPT": "0",
        }
    )
    command = [
        "git",
        f"--git-dir={git_dir}",
        f"--work-tree={root}",
        "-c",
        "core.fsmonitor=false",
        "-c",
        "core.ignoreStat=false",
        "-c",
        "core.filemode=true",
        "-c",
        "maintenance.auto=false",
        *args,
    ]
    completed = subprocess.run(
        command,
        cwd=root,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        env=git_environment,
    )
    permitted = accepted_exits or {0}
    if completed.returncode not in permitted:
        detail = completed.stderr.decode("utf-8", errors="replace")[-1000:]
        raise EvidenceError(
            f"{subject} failed with exit {completed.returncode}: {detail}"
        )
    if len(completed.stdout) > MAX_LOG_BYTES or len(completed.stderr) > MAX_LOG_BYTES:
        raise EvidenceError(f"{subject} exceeded the Git output budget")
    return completed.stdout


def git_text(root: Path, args: Sequence[str], *, subject: str) -> str:
    data = run_git(root, args, subject=subject)
    try:
        value = data.decode("ascii").strip()
    except UnicodeDecodeError as error:
        raise EvidenceError(f"{subject} produced non-ASCII identity data") from error
    if not value or "\n" in value:
        raise EvidenceError(f"{subject} produced malformed identity data")
    return value


def parse_reference_lock(root: Path) -> dict[str, str]:
    data, _size, _digest = stable_file_facts(
        root / "SUITE.lock", max_bytes=MAX_RECORD_BYTES
    )
    try:
        lines = data.decode("utf-8").splitlines()
    except UnicodeDecodeError as error:
        raise EvidenceError("SUITE.lock is not UTF-8") from error
    rows = [line.split() for line in lines if line.startswith("reference ")]
    if len(rows) != 1 or len(rows[0]) != 5:
        raise EvidenceError("SUITE.lock must contain exactly one strict Reference row")
    directive, repository, tag_field, commit_field, tree_field, *extra = rows[0]
    if directive != "reference" or extra:
        raise EvidenceError("SUITE.lock Reference row is malformed")
    fields = {
        "repository": repository,
        "tag": tag_field.removeprefix("tag="),
        "commit": commit_field.removeprefix("commit="),
        "tree": tree_field.removeprefix("tree="),
    }
    if (
        fields["repository"] != "leanprover/lean4"
        or tag_field == fields["tag"]
        or commit_field == fields["commit"]
        or tree_field == fields["tree"]
        or not re.fullmatch(r"[0-9a-f]{40}", fields["commit"])
        or not re.fullmatch(r"[0-9a-f]{40}", fields["tree"])
    ):
        raise EvidenceError("SUITE.lock Reference identity is malformed")
    return fields


def verify_vendor_binding(root: Path, vendor_path: str) -> dict[str, Any]:
    root = lexical_absolute(root)
    if vendor_path != "vendor/lean4-src":
        raise EvidenceError(
            "only the constitutional vendor/lean4-src binding is supported"
        )
    vendor = require_within(root / vendor_path, root, label="Reference vendor tree")
    mode = vendor.lstat().st_mode
    if stat.S_ISLNK(mode) or not stat.S_ISDIR(mode):
        raise EvidenceError("Reference vendor tree must be a real directory")
    for required in (vendor / "LICENSE", vendor / "LICENSES", root / "vendor/NOTICE"):
        _data, _size, _digest = stable_file_facts(required, max_bytes=MAX_LOG_BYTES)
    if os.path.lexists(vendor / ".git"):
        raise EvidenceError(
            "nested Git metadata is forbidden in the Reference vendor tree"
        )
    reference = parse_reference_lock(root)

    def repository_state() -> tuple[str, str]:
        toplevel = git_text(
            root, ["rev-parse", "--show-toplevel"], subject="repository top level"
        )
        if lexical_absolute(Path(toplevel)) != root:
            raise EvidenceError(
                f"repository top level mismatch: expected={root} actual={toplevel}"
            )
        head = git_text(root, ["rev-parse", "HEAD"], subject="repository HEAD")
        tree = git_text(
            root,
            ["rev-parse", f"{head}:{vendor_path}"],
            subject="Reference HEAD subtree",
        )
        if tree != reference["tree"]:
            raise EvidenceError(
                f"Reference HEAD tree mismatch: expected={reference['tree']} actual={tree}"
            )
        run_git(
            root,
            [
                "diff",
                "--cached",
                "--quiet",
                "--no-ext-diff",
                "--ignore-submodules=none",
                head,
                "--",
                vendor_path,
            ],
            subject="Reference staged-index diff",
        )
        return head, tree

    def scan_index_and_worktree() -> None:
        unmerged = run_git(
            root,
            ["ls-files", "-u", "-z", "--", vendor_path],
            subject="Reference unmerged-index scan",
        )
        if unmerged:
            raise EvidenceError("Reference vendor tree contains unmerged index entries")
        flags = split_git_nul(
            run_git(
                root,
                ["ls-files", "-v", "-z", "--", vendor_path],
                subject="Reference index-flag scan",
            ),
            subject="Reference index-flag scan",
        )
        for value in flags:
            if len(value) < 3 or value[1] != " ":
                raise EvidenceError(
                    "Reference index-flag scan produced a malformed row"
                )
            if value[0] == "S" or value[0].islower():
                raise EvidenceError(
                    "Reference index entry carries a hidden-worktree flag: "
                    f"{value[2:]}"
                )
        run_git(
            root,
            [
                "diff",
                "--quiet",
                "--no-ext-diff",
                "--ignore-submodules=none",
                "--",
                vendor_path,
            ],
            subject="Reference worktree diff",
        )
        if run_git(
            root,
            ["ls-files", "--others", "-z", "--", vendor_path],
            subject="Reference untracked scan",
        ):
            raise EvidenceError("Reference vendor tree contains untracked files")
        if run_git(
            root,
            [
                "ls-files",
                "--others",
                "--ignored",
                "--exclude-standard",
                "-z",
                "--",
                vendor_path,
            ],
            subject="Reference ignored-file scan",
        ):
            raise EvidenceError(
                "Reference vendor tree contains ignored untracked files"
            )

    first_head, first_tree = repository_state()
    scan_index_and_worktree()
    second_head, second_tree = repository_state()
    scan_index_and_worktree()
    third_head, third_tree = repository_state()
    if not (
        (first_head, first_tree)
        == (second_head, second_tree)
        == (third_head, third_tree)
    ):
        raise EvidenceError("Reference repository state changed during verification")
    object_format = git_text(
        root, ["rev-parse", "--show-object-format"], subject="Git object format"
    )
    if object_format != "sha1":
        raise EvidenceError(
            f"unexpected Git object format for pinned Reference tree: {object_format}"
        )
    return {
        "schema": "fln.git-tree-binding/1",
        "path": vendor_path,
        "repository": reference["repository"],
        "tag": reference["tag"],
        "commit": reference["commit"],
        "object_format": object_format,
        "tree": first_tree,
    }


def validate_vendor_binding_document(binding: Any) -> dict[str, Any]:
    if not isinstance(binding, dict) or set(binding) != {
        "schema",
        "path",
        "repository",
        "tag",
        "commit",
        "object_format",
        "tree",
    }:
        raise EvidenceError("Reference vendor binding has unknown or missing fields")
    if (
        binding.get("schema") != "fln.git-tree-binding/1"
        or binding.get("path") != "vendor/lean4-src"
        or binding.get("repository") != "leanprover/lean4"
        or binding.get("object_format") != "sha1"
        or not isinstance(binding.get("tag"), str)
        or not binding["tag"]
        or not re.fullmatch(r"[0-9a-f]{40}", str(binding.get("commit")))
        or not re.fullmatch(r"[0-9a-f]{40}", str(binding.get("tree")))
    ):
        raise EvidenceError("Reference vendor binding is malformed")
    return binding


def inventory_root(rows: Sequence[dict[str, Any]]) -> str:
    digest = hashlib.sha256(b"fln-ubs-inventory/1\0")
    digest.update(canonical_json(list(rows)))
    return f"sha256:{digest.hexdigest()}"


def collect_ubs_inventory(root: Path, scope: str) -> dict[str, Any]:
    root = lexical_absolute(root)
    _root, descriptor = open_directory_nofollow(root, create=False)
    os.close(descriptor)
    if scope == "all-tracked":
        candidates = git_paths(
            root,
            ["ls-files", "-z", "--", "*.rs", "*.toml", "*.py"],
            subject="tracked UBS inventory",
        )
    elif scope == "changed":
        candidates = [
            *git_paths(
                root,
                ["diff", "--name-only", "-z", "HEAD", "--"],
                subject="changed UBS inventory",
            ),
            *git_paths(
                root,
                ["ls-files", "--others", "--exclude-standard", "-z", "--"],
                subject="untracked UBS inventory",
            ),
        ]
    else:
        raise EvidenceError(f"unsupported UBS scope: {scope!r}")
    selected: set[str] = set()
    for rel in candidates:
        rel_path = Path(rel)
        if (
            rel_path.is_absolute()
            or ".." in rel_path.parts
            or rel.startswith("vendor/")
        ):
            if rel.startswith("vendor/"):
                continue
            raise EvidenceError(f"non-canonical UBS path: {rel!r}")
        if not rel.endswith((".rs", ".toml", ".py")):
            continue
        candidate = require_within(root / rel_path, root, label="UBS input")
        try:
            mode = candidate.lstat().st_mode
        except FileNotFoundError:
            continue
        if stat.S_ISLNK(mode) or not stat.S_ISREG(mode):
            raise EvidenceError(
                f"UBS input is not a regular no-follow file: {candidate}"
            )
        selected.add(rel_path.as_posix())
    rows: list[dict[str, Any]] = []
    for rel in sorted(selected, key=lambda value: value.encode("utf-8")):
        _data, size, digest = stable_file_facts(root / rel)
        rows.append({"path": rel, "bytes": size, "sha256": digest})
    return {
        "schema": "fln.ubs-inventory/1",
        "scope": scope,
        "count": len(rows),
        "inventory_root": inventory_root(rows),
        "files": rows,
    }


def validate_ubs_inventory_document(inventory: Any) -> dict[str, Any]:
    if not isinstance(inventory, dict) or set(inventory) != {
        "schema",
        "scope",
        "count",
        "inventory_root",
        "files",
    }:
        raise EvidenceError("UBS inventory has unknown or missing fields")
    if inventory.get("schema") != "fln.ubs-inventory/1" or inventory.get(
        "scope"
    ) not in {
        "changed",
        "all-tracked",
    }:
        raise EvidenceError("UBS inventory identity is malformed")
    rows = inventory.get("files")
    if not isinstance(rows, list) or inventory.get("count") != len(rows):
        raise EvidenceError("UBS inventory count is malformed")
    expected_paths: list[str] = []
    for row in rows:
        if not isinstance(row, dict) or set(row) != {"path", "bytes", "sha256"}:
            raise EvidenceError("UBS inventory row is malformed")
        rel = row.get("path")
        if (
            not isinstance(rel, str)
            or not rel
            or Path(rel).is_absolute()
            or ".." in Path(rel).parts
            or rel.startswith("vendor/")
            or not rel.endswith((".rs", ".toml", ".py"))
        ):
            raise EvidenceError(f"UBS inventory path is non-canonical: {rel!r}")
        if (
            not isinstance(row.get("bytes"), int)
            or isinstance(row.get("bytes"), bool)
            or row["bytes"] < 0
            or not SHA256_HEX.fullmatch(str(row.get("sha256")))
        ):
            raise EvidenceError(f"UBS inventory facts are malformed: {rel}")
        expected_paths.append(rel)
    if expected_paths != sorted(
        set(expected_paths), key=lambda value: value.encode("utf-8")
    ):
        raise EvidenceError("UBS inventory paths are duplicate or unsorted")
    if inventory.get("inventory_root") != inventory_root(rows):
        raise EvidenceError("UBS inventory root is inconsistent")
    return inventory


def validate_ubs_inventory(
    path: Path,
    root: Path | None,
    *,
    require_live_scope: bool = False,
) -> dict[str, Any]:
    inventory = validate_ubs_inventory_document(read_json_object(path))
    if root is None:
        return inventory
    root = lexical_absolute(root)
    _root, descriptor = open_directory_nofollow(root, create=False)
    os.close(descriptor)
    if require_live_scope:
        recomputed = collect_ubs_inventory(root, inventory["scope"])
        if recomputed != inventory:
            raise EvidenceError(
                "UBS inventory does not exactly cover its declared live repository scope"
            )
    for row in inventory["files"]:
        rel = row["path"]
        candidate = require_within(root / rel, root, label="UBS inventory input")
        mode = candidate.lstat().st_mode
        if stat.S_ISLNK(mode) or not stat.S_ISREG(mode):
            raise EvidenceError(f"UBS inventory input is not regular: {candidate}")
        _data, size, digest = stable_file_facts(candidate)
        if row["bytes"] != size or not hmac.compare_digest(row["sha256"], digest):
            raise EvidenceError(f"UBS inventory input changed: {rel}")
    if (
        require_live_scope
        and collect_ubs_inventory(root, inventory["scope"]) != inventory
    ):
        raise EvidenceError("UBS inventory scope changed during validation")
    return inventory


def emergency_kill(
    readiness_path: Path, expected_wrapper_pid: int, expected_stage_id: str
) -> None:
    readiness = read_json_object(readiness_path)
    if readiness.get("schema") not in {
        "fln.supervisor-readiness/1",
        "fln.supervisor-readiness/2",
        "fln.supervisor-readiness/3",
    }:
        raise EvidenceError("emergency kill readiness schema mismatch")
    if (
        readiness.get("status") != "ready"
        or readiness.get("stage_id") != expected_stage_id
    ):
        raise EvidenceError("emergency kill readiness identity mismatch")
    wrapper_pid = readiness.get("wrapper_pid")
    supervisor_pid = readiness.get("supervisor_pid")
    child_pid = readiness.get("child_pid")
    child_pgid = readiness.get("child_pgid")
    child_sid = readiness.get("child_sid", child_pid)
    if (
        wrapper_pid != expected_wrapper_pid
        or child_pid != child_pgid
        or child_pid != child_sid
    ):
        raise EvidenceError("emergency kill PID binding mismatch")
    if not all(
        isinstance(value, int) and not isinstance(value, bool) and value > 1
        for value in (wrapper_pid, supervisor_pid, child_pid)
    ):
        raise EvidenceError("emergency kill PIDs are malformed")
    wrapper_facts = proc_stat_facts(wrapper_pid)
    supervisor_facts = proc_stat_facts(supervisor_pid)
    child_facts = proc_stat_facts(child_pid)
    if (
        wrapper_facts is None
        or supervisor_facts is None
        or child_facts is None
        or wrapper_facts[0] == "Z"
        or supervisor_facts[0] == "Z"
        or child_facts[0] == "Z"
        or wrapper_facts[2] != readiness.get("wrapper_start_ticks")
        or supervisor_facts[2] != readiness.get("supervisor_start_ticks")
        or child_facts[2] != readiness.get("child_start_ticks")
        or child_facts[1] != child_pgid
        or os.getpgid(child_pid) != child_pgid
        or os.getsid(child_pid) != child_sid
    ):
        raise EvidenceError("emergency kill readiness is stale")
    handles: ProcessHandles = {}
    frozen_scope: set[int] | None = None
    try:
        if not remember_process(wrapper_pid, handles):
            raise EvidenceError("emergency kill could not bind process lifetimes")
        if supervisor_pid != wrapper_pid and not remember_process(
            supervisor_pid, handles, expected_parent_pid=wrapper_pid
        ):
            raise EvidenceError("emergency kill could not bind supervisor lifetime")
        if not remember_process(
            child_pid, handles, expected_parent_pid=supervisor_pid
        ):
            raise EvidenceError("emergency kill could not bind child lifetime")
        if (
            handles[wrapper_pid][0] != wrapper_facts[2]
            or handles[supervisor_pid][0] != supervisor_facts[2]
            or handles[child_pid][0] != child_facts[2]
        ):
            raise EvidenceError("emergency kill process identity changed")

        # Freeze the wrapper-owned subreaper tree before killing it. This catches
        # descendants that created their own sessions and prevents any bound parent
        # from forking across the final scan. Pidfds make every signal lifetime-safe.
        live = live_tree_members(wrapper_pid, handles)
        if (
            wrapper_pid not in live
            or supervisor_pid not in live
            or child_pid not in live
        ):
            raise EvidenceError("emergency kill readiness tree is incomplete")
        freeze_deadline = time.monotonic() + 1.0
        while time.monotonic() < freeze_deadline:
            for pid in live:
                signal_process_handle(pid, handles[pid], signal.SIGSTOP)
            time.sleep(0.01)
            repeated = live_tree_members(wrapper_pid, handles)
            all_stopped = all(
                (facts := proc_stat_facts(pid)) is not None
                and facts[0] in {"T", "t"}
                and facts[2] == handles[pid][0]
                for pid in repeated
            )
            if repeated == live and all_stopped:
                live = repeated
                frozen_scope = set(repeated)
                break
            live = repeated
        else:
            raise EvidenceError("emergency kill could not freeze the complete tree")

        for pid in sorted(live, key=lambda value: value == wrapper_pid):
            signal_process_handle(pid, handles[pid], signal.SIGKILL)
        deadline = time.monotonic() + 1.0
        while time.monotonic() < deadline:
            live = live_tree_members(wrapper_pid, handles)
            if not live:
                return
            for pid in live:
                signal_process_handle(pid, handles[pid], signal.SIGKILL)
            time.sleep(0.01)
        raise EvidenceError(f"emergency kill left live processes: {sorted(live)}")
    except BaseException:
        if frozen_scope is None:
            # Until a complete fixed point is proven, killing the guardian could
            # orphan an unbound descendant. Resume anything tentatively stopped and
            # leave the outer guardian alive to retain the subreaper boundary.
            for pid, handle in list(handles.items()):
                signal_process_handle(pid, handle, signal.SIGCONT)
        else:
            # Once the whole scope is frozen, finish the authorized teardown with
            # descendants/inner supervisor first and the outer guardian last.
            for pid in sorted(
                frozen_scope, key=lambda value: value == wrapper_pid
            ):
                handle = handles.get(pid)
                if handle is not None:
                    signal_process_handle(pid, handle, signal.SIGKILL)
        raise
    finally:
        close_process_handles(handles)


def kill_bound_process_group(
    pid: int, expected_start_ticks: int, expected_parent_pid: int
) -> None:
    """Freeze and pidfd-kill every member of one exact session process group."""
    if (
        pid <= 1
        or expected_start_ticks <= 0
        or expected_parent_pid <= 1
        or pid == expected_parent_pid
    ):
        raise EvidenceError("bound process-group identity is malformed")
    opened = open_process_handle(pid, expected_parent_pid=expected_parent_pid)
    if opened is None:
        return
    facts = proc_stat_facts(pid)
    if facts is None or facts[2] != expected_start_ticks or opened[0] != expected_start_ticks:
        os.close(opened[1])
        return
    if facts[1] != pid:
        os.close(opened[1])
        raise EvidenceError("bound process is not the expected session leader")
    handles: ProcessHandles = {pid: opened}
    frozen = False
    try:
        deadline = time.monotonic() + PROCESS_GROUP_FREEZE_TIMEOUT_S
        prior_members: set[int] | None = None
        for _attempt in range(PROCESS_GROUP_FREEZE_ATTEMPTS):
            if time.monotonic() >= deadline:
                break
            observed = live_process_group_members(pid)
            for member_pid in observed:
                current = handles.get(member_pid)
                if current is None:
                    current = open_process_handle(member_pid)
                    if current is None:
                        continue
                    member_facts = proc_stat_facts(member_pid)
                    if (
                        member_facts is None
                        or member_facts[0] == "Z"
                        or member_facts[1] != pid
                        or member_facts[2] != current[0]
                    ):
                        os.close(current[1])
                        continue
                    handles[member_pid] = current
                signal_process_handle(member_pid, current, signal.SIGSTOP)
            time.sleep(0.005)
            repeated = live_process_group_members(pid)
            bound_live = {
                member_pid
                for member_pid, member_handle in handles.items()
                if process_handle_alive(member_pid, member_handle)
                and (member_facts := proc_stat_facts(member_pid)) is not None
                and member_facts[1] == pid
            }
            all_stopped = all(
                (member_facts := proc_stat_facts(member_pid)) is not None
                and member_facts[0] in {"T", "t"}
                and member_facts[2] == handles[member_pid][0]
                for member_pid in bound_live
            )
            if repeated == bound_live and repeated == prior_members and all_stopped:
                frozen = True
                break
            prior_members = repeated if repeated == bound_live and all_stopped else None
        if not frozen:
            raise EvidenceError("bound process group did not reach a frozen fixed point")
        for member_pid in sorted(handles, key=lambda value: value == pid):
            signal_process_handle(
                member_pid, handles[member_pid], signal.SIGKILL
            )
        deadline = time.monotonic() + PROCESS_GROUP_KILL_TIMEOUT_S
        for _attempt in range(PROCESS_GROUP_KILL_ATTEMPTS):
            live = {
                member_pid
                for member_pid, member_handle in handles.items()
                if process_handle_alive(member_pid, member_handle)
            }
            if not live and not live_process_group_members(pid):
                return
            for member_pid in live:
                signal_process_handle(
                    member_pid, handles[member_pid], signal.SIGKILL
                )
            if time.monotonic() >= deadline:
                break
            time.sleep(0.005)
        raise EvidenceError("bound process group remained live after pidfd SIGKILL")
    except BaseException:
        # Every signal remains tied to a pidfd-bound lifetime. If the fixed-point
        # proof fails, kill what was proven and report cleanup uncertainty.
        for member_pid, member_handle in handles.items():
            signal_process_handle(member_pid, member_handle, signal.SIGKILL)
        raise
    finally:
        if not frozen:
            for member_pid, member_handle in handles.items():
                signal_process_handle(member_pid, member_handle, signal.SIGKILL)
        close_process_handles(handles)


def signal_bound_process(pid: int, expected_start_ticks: int, signum: int) -> None:
    """Signal one exact Linux process lifetime without numeric-PID reuse risk."""
    if pid <= 1 or expected_start_ticks <= 0:
        raise EvidenceError("bound process identity is malformed")
    handle = open_process_handle(pid)
    if handle is None:
        return
    try:
        if handle[0] != expected_start_ticks:
            return
        signal_process_handle(pid, handle, signum)
    finally:
        os.close(handle[1])


def cleanup_guardian_descendants(worker_pid: int, grace_s: float = 1.0) -> list[int]:
    """Contain descendants adopted after an inner supervisor exits unexpectedly."""
    known: ProcessHandles = {}
    try:
        live = live_tree_members(worker_pid, known)
        if not live:
            time.sleep(0.01)
            live = live_tree_members(worker_pid, known)
        if not live:
            reap_adopted_children()
            return []

        freeze_deadline = time.monotonic() + grace_s
        while time.monotonic() < freeze_deadline:
            for pid in live:
                signal_process_handle(pid, known[pid], signal.SIGSTOP)
            time.sleep(0.01)
            repeated = live_tree_members(worker_pid, known)
            all_stopped = all(
                (facts := proc_stat_facts(pid)) is not None
                and facts[0] in {"T", "t"}
                and facts[2] == known[pid][0]
                for pid in repeated
            )
            if repeated == live and all_stopped:
                live = repeated
                break
            live = repeated

        for pid in live:
            signal_process_handle(pid, known[pid], signal.SIGKILL)
        kill_deadline = time.monotonic() + grace_s
        while time.monotonic() < kill_deadline:
            reap_adopted_children()
            live = live_tree_members(worker_pid, known)
            if not live:
                reap_adopted_children()
                return []
            for pid in live:
                signal_process_handle(pid, known[pid], signal.SIGKILL)
            time.sleep(0.01)
        return sorted(live)
    finally:
        close_process_handles(known)


def artifact_role(rel: str) -> str:
    if rel == "run.ndjson":
        return "run_log"
    if rel == CHECK_HUMAN_LOG:
        return "human_semantic_log"
    if rel == "human.log":
        return "human_telemetry_log"
    if rel.startswith("fixtures/"):
        return "repro_fixture"
    if rel.endswith(".ndjson"):
        return "child_log"
    if rel.endswith(".out"):
        return "stdout"
    if rel.endswith(".err"):
        return "stderr"
    if rel.endswith(".meta.json"):
        return "supervisor_metadata"
    if rel.endswith(".ready.json"):
        return "supervisor_readiness"
    if rel.endswith(".validation.json"):
        return "validation_report"
    if rel == "vendor-binding.json":
        return "reference_tree_binding"
    if rel == "ubs-inventory.json":
        return "ubs_inventory"
    return "artifact"


def artifact_inventory_once(
    art_dir: Path, *, excluded: set[Path]
) -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    for path in sorted(art_dir.rglob("*"), key=lambda item: item.as_posix().encode()):
        absolute = lexical_absolute(path)
        if absolute in excluded:
            continue
        try:
            mode = path.lstat().st_mode
        except FileNotFoundError as error:
            raise EvidenceError(
                f"artifact disappeared during inventory: {path}"
            ) from error
        if stat.S_ISLNK(mode):
            raise EvidenceError(f"artifact symlink is forbidden: {path}")
        rel = path.relative_to(art_dir).as_posix()
        if rel.startswith("/") or ".." in Path(rel).parts or ".partial." in rel:
            raise EvidenceError(f"non-canonical or incomplete artifact path: {rel}")
        if stat.S_ISDIR(mode):
            entries.append(
                {
                    "path": rel,
                    "role": "directory",
                    "bytes": 0,
                    "sha256": hashlib.sha256(b"fln-artifact-directory/1").hexdigest(),
                    "complete": True,
                }
            )
        elif stat.S_ISREG(mode):
            _data, size, digest = stable_file_facts(path)
            entries.append(
                {
                    "path": rel,
                    "role": artifact_role(rel),
                    "bytes": size,
                    "sha256": digest,
                    "complete": True,
                }
            )
        else:
            raise EvidenceError(f"special artifact file is forbidden: {path}")
    return entries


def artifact_inventory(art_dir: Path, *, excluded: set[Path]) -> list[dict[str, Any]]:
    previous: list[dict[str, Any]] | None = None
    for _attempt in range(6):
        current = artifact_inventory_once(art_dir, excluded=excluded)
        if current == previous:
            return current
        previous = current
    raise EvidenceError(
        "artifact inventory did not stabilize across consecutive snapshots"
    )


def generate_manifest(
    art_dir: Path,
    output: Path,
    digest_output: Path,
    run_id: str,
    bead: str,
    scenario: str,
    verdict: str,
    input_root: str,
    final_root: str,
) -> dict[str, Any]:
    art_dir = lexical_absolute(art_dir)
    _root, root_fd = open_directory_nofollow(art_dir, create=False)
    os.close(root_fd)
    output = require_exact_artifact_path(
        output, art_dir, "manifest.json", label="manifest output"
    )
    digest_output = require_exact_artifact_path(
        digest_output, art_dir, "manifest.digest", label="manifest digest"
    )
    run_log = art_dir / "run.ndjson"
    run_records = load_ndjson(run_log)
    run_schema = run_records[0].get("schema")
    if run_schema not in RUN_SCHEMAS:
        raise EvidenceError("run log has an unsupported schema")
    run_report = validate_run(run_log, run_schema, verdict)
    if run_schema == "fln.check/2":
        validate_check_human(run_log, art_dir / CHECK_HUMAN_LOG)
    start = run_records[0]
    terminal = run_records[-1]
    expected_identity = {
        "run_id": run_id,
        "bead": bead,
        "scenario": scenario,
        "verdict": verdict,
        "input_root": input_root,
        "final_root": final_root,
    }
    observed_identity = {
        "run_id": start.get("run_id"),
        "bead": start.get("bead"),
        "scenario": start.get("scenario"),
        "verdict": terminal.get("verdict"),
        "input_root": start.get("input_root"),
        "final_root": terminal.get("final_state"),
    }
    if observed_identity != expected_identity:
        raise EvidenceError(
            f"manifest identity arguments disagree with run: expected={observed_identity!r} actual={expected_identity!r}"
        )
    validation_path = art_dir / "run.validation.json"
    if read_json_object(validation_path) != run_report:
        raise EvidenceError("run validation report does not match the manifested run")
    entries = artifact_inventory(
        art_dir,
        excluded={
            output,
            digest_output,
            art_dir / "bundle.decision",
            art_dir / "bundle.complete.json",
        },
    )
    present = {entry["path"] for entry in entries}
    required = {"run.ndjson", "run.validation.json"}
    if run_schema == "fln.check/2":
        required.add(CHECK_HUMAN_LOG)
    if not required.issubset(present):
        raise EvidenceError(
            f"manifest is missing required artifacts: {sorted(required - present)!r}"
        )
    manifest = {
        "schema": "fln.evidence-manifest/1",
        "run_schema": run_schema,
        "run_id": run_id,
        "bead": bead,
        "scenario": scenario,
        "verdict": verdict,
        "created_utc": utc_now(),
        "input_root": input_root,
        "final_root": final_root,
        "final_state_matches_input": input_root == final_root,
        "artifacts": entries,
    }
    data = canonical_json(manifest)
    write_new(output, data)
    digest = hashlib.sha256(data).hexdigest()
    write_new(digest_output, f"sha256:{digest}  {output.name}\n".encode())
    validate_manifest(art_dir, output, digest_output)
    return manifest


def validate_manifest(
    art_dir: Path,
    manifest_path: Path,
    digest_path: Path,
    *,
    live_context: bool = True,
) -> None:
    art_dir = lexical_absolute(art_dir)
    _root, root_fd = open_directory_nofollow(art_dir, create=False)
    os.close(root_fd)
    manifest_path = require_exact_artifact_path(
        manifest_path, art_dir, "manifest.json", label="manifest"
    )
    digest_path = require_exact_artifact_path(
        digest_path, art_dir, "manifest.digest", label="manifest digest"
    )
    manifest = read_json_object(manifest_path)
    if manifest.get("schema") != "fln.evidence-manifest/1":
        raise EvidenceError("wrong evidence manifest schema")
    if manifest.get("run_schema") not in RUN_SCHEMAS:
        raise EvidenceError("manifest run schema is unsupported")
    if manifest.get("verdict") not in {
        "pass",
        "fail",
        "internal_fault",
        "inconclusive",
        "cancelled",
    }:
        raise EvidenceError("manifest verdict is unsupported")
    for key in ("input_root", "final_root"):
        if not re.fullmatch(r"sha256:[0-9a-f]{64}", str(manifest.get(key))):
            raise EvidenceError(f"manifest {key} is not a canonical tree root")
    entries = manifest.get("artifacts")
    if not isinstance(entries, list):
        raise EvidenceError("manifest artifacts must be a list")
    observed_paths: list[str] = []
    seen_paths: set[str] = set()
    for entry in entries:
        expected_row_keys = {"path", "role", "bytes", "sha256", "complete"}
        if (
            not isinstance(entry, dict)
            or set(entry) != expected_row_keys
            or not isinstance(entry.get("path"), str)
        ):
            raise EvidenceError("malformed manifest artifact row")
        rel = entry["path"]
        if rel in seen_paths:
            raise EvidenceError(f"duplicate manifest artifact row: {rel}")
        seen_paths.add(rel)
        if rel.startswith("/") or ".." in Path(rel).parts or ".partial." in rel:
            raise EvidenceError(f"non-canonical manifest path: {rel}")
        path = require_within(art_dir / rel, art_dir, label="manifest artifact")
        if entry.get("role") == "directory":
            _directory, descriptor = open_directory_nofollow(path, create=False)
            os.close(descriptor)
            expected_directory_digest = hashlib.sha256(
                b"fln-artifact-directory/1"
            ).hexdigest()
            if (
                entry.get("bytes") != 0
                or not hmac.compare_digest(
                    str(entry.get("sha256")), expected_directory_digest
                )
            ):
                raise EvidenceError(f"manifest directory facts mismatch: {rel}")
        else:
            _data, size, digest = stable_file_facts(path)
            if entry.get("bytes") != size:
                raise EvidenceError(f"manifest byte count mismatch: {rel}")
            if not hmac.compare_digest(str(entry.get("sha256")), digest):
                raise EvidenceError(f"manifest digest mismatch: {rel}")
        if entry.get("complete") is not True:
            raise EvidenceError(f"manifest artifact is not complete: {rel}")
        observed_paths.append(rel)
    if observed_paths != sorted(observed_paths, key=lambda value: value.encode()):
        raise EvidenceError("manifest artifact rows are not canonically sorted")
    if manifest.get("final_state_matches_input") != (
        manifest.get("input_root") == manifest.get("final_root")
    ):
        raise EvidenceError("manifest final-state assertion is inconsistent")
    if (
        manifest.get("verdict") == "pass"
        and manifest.get("final_state_matches_input") is not True
    ):
        raise EvidenceError(
            "passing manifest does not preserve its canonical input root"
        )
    actual_entries = artifact_inventory(
        art_dir,
        excluded={
            manifest_path,
            digest_path,
            art_dir / "bundle.decision",
            art_dir / "bundle.complete.json",
        },
    )
    if entries != actual_entries:
        raise EvidenceError(
            f"manifest inventory mismatch: recorded={entries!r} actual={actual_entries!r}"
        )
    required = {"run.ndjson", "run.validation.json"}
    if manifest["run_schema"] == "fln.check/2":
        required.add(CHECK_HUMAN_LOG)
    if not required.issubset(seen_paths):
        raise EvidenceError(
            f"manifest is missing required artifacts: {sorted(required - seen_paths)!r}"
        )
    run_log = art_dir / "run.ndjson"
    run_report = validate_run(
        run_log,
        manifest["run_schema"],
        str(manifest.get("verdict")),
        live_context=live_context,
    )
    if manifest["run_schema"] == "fln.check/2":
        validate_check_human(run_log, art_dir / CHECK_HUMAN_LOG)
    if read_json_object(art_dir / "run.validation.json") != run_report:
        raise EvidenceError("manifested run validation report is stale or forged")
    terminal = load_ndjson(run_log)[-1]
    start = load_ndjson(run_log)[0]
    for key, manifest_key in (
        ("run_id", "run_id"),
        ("bead", "bead"),
        ("verdict", "verdict"),
        ("final_state", "final_root"),
    ):
        if terminal.get(key) != manifest.get(manifest_key):
            raise EvidenceError(f"manifest/run terminal mismatch for {key}")
    for key in ("run_id", "bead", "scenario", "input_root"):
        if start.get(key) != manifest.get(key):
            raise EvidenceError(f"manifest/run start mismatch for {key}")
    if terminal.get("evidence_manifest") != manifest_path.name:
        raise EvidenceError("run terminal names a different evidence manifest")
    expected_digest = f"sha256:{sha256_file(manifest_path)}  {manifest_path.name}\n"
    digest_data, _size, _digest = stable_file_facts(digest_path)
    try:
        digest_text = digest_data.decode("utf-8")
    except UnicodeDecodeError as error:
        raise EvidenceError("manifest digest sidecar is not UTF-8") from error
    if not hmac.compare_digest(digest_text, expected_digest):
        raise EvidenceError("manifest digest sidecar mismatch")


def durably_sync_manifested_bundle(
    art_dir: Path,
    manifest_path: Path,
    digest_path: Path,
    commit_path: Path | None = None,
) -> None:
    """Order every artifact and directory-creation edge before the bundle marker."""
    art_dir = lexical_absolute(art_dir)
    manifest_path = require_exact_artifact_path(
        manifest_path, art_dir, "manifest.json", label="manifest"
    )
    digest_path = require_exact_artifact_path(
        digest_path, art_dir, "manifest.digest", label="manifest digest"
    )
    if commit_path is not None:
        commit_path = require_exact_artifact_path(
            commit_path, art_dir, "bundle.complete.json", label="bundle commit"
        )
    manifest = read_json_object(manifest_path)
    files = [
        require_within(art_dir / entry["path"], art_dir, label="durable artifact")
        for entry in manifest["artifacts"]
        if entry["role"] != "directory"
    ]
    files.extend((manifest_path, digest_path))
    if commit_path is not None:
        files.append(
            require_within(commit_path, art_dir, label="durable bundle commit")
        )
        files.append(
            require_within(
                commit_path.with_name("bundle.decision"),
                art_dir,
                label="durable bundle decision",
            )
        )
    directories = {art_dir}
    for path in files:
        _absolute, descriptor = open_regular_nofollow(path)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
        parent = path.parent
        while parent != art_dir:
            if parent == parent.parent or art_dir not in parent.parents:
                raise EvidenceError(
                    f"durable artifact parent escapes artifact root: {path}"
                )
            directories.add(parent)
            parent = parent.parent
    for entry in manifest["artifacts"]:
        if entry["role"] == "directory":
            directories.add(
                require_within(
                    art_dir / entry["path"], art_dir, label="durable directory"
                )
            )
    # The shells create a fresh per-attempt artifact directory.  Syncing only that
    # directory persists its children but not its own name in the parent.  Include
    # the complete ancestor chain so first-run ART_ROOT creation is durable too.
    ancestor = art_dir.parent
    while True:
        directories.add(ancestor)
        if ancestor == ancestor.parent:
            break
        ancestor = ancestor.parent
    for directory in sorted(
        directories, key=lambda path: len(path.parts), reverse=True
    ):
        _absolute, descriptor = open_directory_nofollow(directory, create=False)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)


def complete_bundle(
    art_dir: Path,
    manifest_path: Path,
    digest_path: Path,
    output: Path,
    *,
    governed_root: Path,
    governed_paths: Sequence[str],
    expected_root: str,
    inventory_path: Path | None = None,
    vendor_path: str | None = None,
    restore_signal_state: bool = True,
    test_fail_after_link: bool = False,
    test_marker_pause: tuple[Path, Path] | None = None,
) -> dict[str, Any]:
    art_dir = lexical_absolute(art_dir)
    manifest_path = require_exact_artifact_path(
        manifest_path, art_dir, "manifest.json", label="manifest"
    )
    digest_path = require_exact_artifact_path(
        digest_path, art_dir, "manifest.digest", label="manifest digest"
    )
    output = require_exact_artifact_path(
        output, art_dir, "bundle.complete.json", label="bundle commit"
    )
    validate_manifest(art_dir, manifest_path, digest_path)
    manifest = read_json_object(manifest_path)
    run_log = art_dir / "run.ndjson"
    terminal = load_ndjson(run_log)[-1]
    if terminal.get("bundle_commit") != output.name:
        raise EvidenceError("run terminal names a different bundle commit marker")
    initial_bindings = (
        sha256_file(run_log),
        sha256_file(manifest_path),
        sha256_file(digest_path),
    )
    marker: dict[str, Any] = {
        "schema": "fln.evidence-bundle-commit/1",
        "status": "committed",
        "run_id": manifest["run_id"],
        "bead": manifest["bead"],
        "scenario": manifest["scenario"],
        "verdict": manifest["verdict"],
        "process_exit": terminal["process_exit"],
        "created_utc": utc_now(),
        "run_log": {"path": "run.ndjson", "sha256": initial_bindings[0]},
        "manifest": {"path": manifest_path.name, "sha256": initial_bindings[1]},
        "manifest_digest": {
            "path": digest_path.name,
            "sha256": initial_bindings[2],
        },
    }
    validate_marker_bindings(marker, manifest, terminal, initial_bindings)
    marker_data = canonical_json(marker)
    current_root = tree_hash(
        governed_root,
        governed_paths,
        inventory_path=inventory_path,
        vendor_path=vendor_path,
    )
    if current_root != expected_root or current_root != manifest.get("final_root"):
        raise EvidenceError("governed inputs changed before bundle commit")
    # The governed hash can be long. Revalidate every artifact after it, then prove
    # both sides stable across another full pass before publishing the marker.
    validate_manifest(art_dir, manifest_path, digest_path)
    repeated_bindings = (
        sha256_file(run_log),
        sha256_file(manifest_path),
        sha256_file(digest_path),
    )
    if repeated_bindings != initial_bindings:
        raise EvidenceError("bundle bindings changed during prospective validation")
    validate_marker_bindings(
        marker,
        read_json_object(manifest_path),
        load_ndjson(run_log)[-1],
        repeated_bindings,
    )
    repeated_root = tree_hash(
        governed_root,
        governed_paths,
        inventory_path=inventory_path,
        vendor_path=vendor_path,
    )
    if repeated_root != current_root:
        raise EvidenceError("governed inputs changed during prospective validation")
    durably_sync_manifested_bundle(art_dir, manifest_path, digest_path)
    validate_manifest(art_dir, manifest_path, digest_path)
    durable_bindings = (
        sha256_file(run_log),
        sha256_file(manifest_path),
        sha256_file(digest_path),
    )
    if durable_bindings != initial_bindings:
        raise EvidenceError("bundle bindings changed during durable synchronization")
    final_root = tree_hash(
        governed_root,
        governed_paths,
        inventory_path=inventory_path,
        vendor_path=vendor_path,
    )
    if final_root != current_root:
        raise EvidenceError("governed inputs changed before durable bundle commit")
    validate_manifest(art_dir, manifest_path, digest_path)
    final_bindings = (
        sha256_file(run_log),
        sha256_file(manifest_path),
        sha256_file(digest_path),
    )
    if final_bindings != initial_bindings:
        raise EvidenceError("bundle bindings changed before durable bundle commit")
    validate_marker_bindings(
        marker,
        read_json_object(manifest_path),
        load_ndjson(run_log)[-1],
        final_bindings,
    )
    # This durable, exclusive publication is deliberately the final operation.
    write_signal_committed_atomic_new(
        output,
        marker_data,
        decision_path=output.with_name("bundle.decision"),
        restore_signal_state=restore_signal_state,
        test_fail_after_link=test_fail_after_link,
        test_marker_pause=test_marker_pause,
    )
    return marker


def validate_marker_bindings(
    marker: dict[str, Any],
    manifest: dict[str, Any],
    terminal: dict[str, Any],
    bindings: tuple[str, str, str],
) -> None:
    if set(marker) != {
        "schema",
        "status",
        "run_id",
        "bead",
        "scenario",
        "verdict",
        "process_exit",
        "created_utc",
        "run_log",
        "manifest",
        "manifest_digest",
    }:
        raise EvidenceError("bundle marker has unknown or missing fields")
    if (
        marker.get("schema") != "fln.evidence-bundle-commit/1"
        or marker.get("status") != "committed"
    ):
        raise EvidenceError("invalid evidence bundle commit marker")
    for key in ("run_id", "bead", "scenario", "verdict"):
        if marker.get(key) != manifest.get(key):
            raise EvidenceError(f"bundle marker identity mismatch for {key}")
    if marker.get("process_exit") != terminal.get("process_exit"):
        raise EvidenceError("bundle marker process exit disagrees with terminal")
    expected_files = {
        "run_log": ("run.ndjson", bindings[0]),
        "manifest": ("manifest.json", bindings[1]),
        "manifest_digest": ("manifest.digest", bindings[2]),
    }
    for key, (expected_name, expected_digest) in expected_files.items():
        value = marker.get(key)
        if (
            not isinstance(value, dict)
            or set(value) != {"path", "sha256"}
            or value.get("path") != expected_name
            or not hmac.compare_digest(str(value.get("sha256")), expected_digest)
        ):
            raise EvidenceError(f"bundle marker has invalid {key} binding")


def validate_bundle(
    art_dir: Path,
    manifest_path: Path,
    digest_path: Path,
    commit_path: Path,
) -> dict[str, Any]:
    """Side-effect-free bundle validation: reads, verifies, and reports only.

    Validation never creates, links, or syncs anything. A winning decision
    whose publisher died before the canonical marker link is recovered only by
    the explicitly named adoption operation (`adopt_bundle`); validation of
    such a bundle fails typed until adoption has run.
    """
    art_dir = lexical_absolute(art_dir)
    manifest_path = require_exact_artifact_path(
        manifest_path, art_dir, "manifest.json", label="manifest"
    )
    digest_path = require_exact_artifact_path(
        digest_path, art_dir, "manifest.digest", label="manifest digest"
    )
    commit_path = require_exact_artifact_path(
        commit_path, art_dir, "bundle.complete.json", label="bundle commit"
    )
    run_log = art_dir / "run.ndjson"
    validate_manifest(art_dir, manifest_path, digest_path, live_context=False)
    manifest = read_json_object(manifest_path)
    terminal = load_ndjson(run_log)[-1]
    bindings = (
        sha256_file(run_log),
        sha256_file(manifest_path),
        sha256_file(digest_path),
    )
    decision_path = art_dir / "bundle.decision"
    decision_marker = read_json_object(decision_path)
    validate_marker_bindings(decision_marker, manifest, terminal, bindings)
    decision_data, _size, _digest = stable_file_facts(decision_path)
    try:
        commit_data, _size, _digest = stable_file_facts(commit_path)
    except FileNotFoundError:
        raise EvidenceError(
            "bundle commit marker is absent; a winning decision is recovered "
            "only by the named adoption operation"
        ) from None
    if not hmac.compare_digest(decision_data, commit_data):
        raise EvidenceError("bundle marker does not match its commit decision")
    marker = read_json_object(commit_path)
    validate_marker_bindings(
        marker,
        manifest,
        terminal,
        bindings,
    )
    return {
        "schema": "fln.bundle-validation/1",
        "valid": True,
        "committed": True,
        "run_id": marker["run_id"],
        "verdict": marker["verdict"],
        "process_exit": marker["process_exit"],
        "commit_sha256": sha256_file(commit_path),
    }


def adopt_bundle(
    art_dir: Path,
    manifest_path: Path,
    digest_path: Path,
    commit_path: Path,
) -> dict[str, Any]:
    """The explicitly named adoption operation (Design: validate/adopt split).

    A publisher can die after its bundle decision wins but before the canonical
    marker link or its durable ordering. Adoption recovers exactly that state:
    it verifies the winning decision against the manifested run, publishes the
    canonical marker exclusively as a hard link of the decision, fsyncs through
    the artifact-directory ancestry, durably orders every manifested artifact,
    and finishes with the full side-effect-free revalidation. Concurrent
    adoption is idempotent — the link either publishes the single canonical
    name or observes it already present — and an empty decision, claimed by
    cancellation, is refused typed: cancellation can never be adopted as pass.
    """
    art_dir = lexical_absolute(art_dir)
    manifest_path = require_exact_artifact_path(
        manifest_path, art_dir, "manifest.json", label="manifest"
    )
    digest_path = require_exact_artifact_path(
        digest_path, art_dir, "manifest.digest", label="manifest digest"
    )
    commit_path = require_exact_artifact_path(
        commit_path, art_dir, "bundle.complete.json", label="bundle commit"
    )
    run_log = art_dir / "run.ndjson"
    decision_path = art_dir / "bundle.decision"
    _decision_data, decision_size, _decision_digest = stable_file_facts(
        decision_path
    )
    if decision_size == 0:
        raise EvidenceError(
            "cancellation claimed the bundle decision; adoption refused"
        )
    validate_manifest(art_dir, manifest_path, digest_path, live_context=False)
    manifest = read_json_object(manifest_path)
    terminal = load_ndjson(run_log)[-1]
    bindings = (
        sha256_file(run_log),
        sha256_file(manifest_path),
        sha256_file(digest_path),
    )
    decision_marker = read_json_object(decision_path)
    validate_marker_bindings(decision_marker, manifest, terminal, bindings)
    _parent, parent_fd = open_directory_nofollow(art_dir, create=False)
    try:
        try:
            os.link(
                decision_path.name,
                commit_path.name,
                src_dir_fd=parent_fd,
                dst_dir_fd=parent_fd,
                follow_symlinks=False,
            )
        except FileExistsError:
            pass
        os.fsync(parent_fd)
    finally:
        os.close(parent_fd)
    durably_sync_manifested_bundle(
        art_dir, manifest_path, digest_path, commit_path=commit_path
    )
    return validate_bundle(art_dir, manifest_path, digest_path, commit_path)


PARTIAL_BUNDLE_CLASSIFICATIONS = {"internal_fault", "inconclusive", "cancelled"}


def publish_partial_bundle(
    art_dir: Path,
    *,
    run_id: str,
    bead: str,
    scenario: str,
    step: str,
    reason: str,
    classification: str,
    argv: Sequence[str],
    cwd: str,
    restore_signal_state: bool = True,
) -> dict[str, Any]:
    """Publish the typed durable partial bundle for an early-envelope fault.

    A consumer whose evidence envelope faulted between artifact-directory
    creation and its run_start emission has no validatable run log, so bundle
    completeness can never be claimed for it. The partial form carries its own
    marker name (`bundle.incomplete.json`) and schemas, is refused typed by
    complete-bundle validation and by adoption alike, and its classification
    can never be pass. Publication still races cancellation on the shared
    write-once `bundle.decision` linearization point.
    """
    art_dir = lexical_absolute(art_dir)
    if classification not in PARTIAL_BUNDLE_CLASSIFICATIONS:
        raise EvidenceError("partial bundle classification is unsupported")
    for label, value in (
        ("run_id", run_id),
        ("bead", bead),
        ("scenario", scenario),
        ("step", step),
        ("reason", reason),
        ("cwd", cwd),
    ):
        if not isinstance(value, str) or not value:
            raise EvidenceError(f"partial bundle {label} must be present")
    rendered_argv, _had_redaction = redacted_argv(list(argv))
    fault = {
        "schema": "fln.check-setup-fault/1",
        "run_id": run_id,
        "bead": bead,
        "scenario": scenario,
        "step": step,
        "reason_code": reason,
        "classification": classification,
        "argv": rendered_argv,
        "cwd": cwd,
        "monotonic_ns": time.monotonic_ns(),
        "wall_time_utc": utc_now(),
    }
    fault_path = art_dir / "setup-fault.json"
    write_new(fault_path, canonical_json(fault))
    manifest_path = art_dir / "manifest-incomplete.json"
    digest_path = art_dir / "manifest-incomplete.digest"
    marker_path = art_dir / "bundle.incomplete.json"
    decision_path = art_dir / "bundle.decision"
    entries = artifact_inventory(
        art_dir,
        excluded={manifest_path, digest_path, decision_path, marker_path},
    )
    present = {entry["path"] for entry in entries}
    if "setup-fault.json" not in present:
        raise EvidenceError("partial manifest lost its setup fault record")
    manifest = {
        "schema": "fln.evidence-manifest-incomplete/1",
        "run_id": run_id,
        "bead": bead,
        "scenario": scenario,
        "step": step,
        "reason_code": reason,
        "classification": classification,
        "created_utc": utc_now(),
        "setup_fault_sha256": sha256_file(fault_path),
        "artifacts": entries,
    }
    manifest_data = canonical_json(manifest)
    write_new(manifest_path, manifest_data)
    manifest_digest = hashlib.sha256(manifest_data).hexdigest()
    write_new(
        digest_path,
        f"sha256:{manifest_digest}  {manifest_path.name}\n".encode(),
    )
    marker = {
        "schema": "fln.evidence-bundle-incomplete-commit/1",
        "status": "incomplete",
        "run_id": run_id,
        "bead": bead,
        "scenario": scenario,
        "step": step,
        "reason_code": reason,
        "classification": classification,
        "created_utc": utc_now(),
        "setup_fault": {
            "path": fault_path.name,
            "sha256": sha256_file(fault_path),
        },
        "manifest": {
            "path": manifest_path.name,
            "sha256": sha256_file(manifest_path),
        },
        "manifest_digest": {
            "path": digest_path.name,
            "sha256": sha256_file(digest_path),
        },
    }
    write_signal_committed_atomic_new(
        marker_path,
        canonical_json(marker),
        decision_path=decision_path,
        restore_signal_state=restore_signal_state,
    )
    return marker


def validate_partial_bundle(art_dir: Path) -> dict[str, Any]:
    """Side-effect-free validation of a typed early-envelope partial bundle."""
    art_dir = lexical_absolute(art_dir)
    fault_path = art_dir / "setup-fault.json"
    manifest_path = art_dir / "manifest-incomplete.json"
    digest_path = art_dir / "manifest-incomplete.digest"
    marker_path = art_dir / "bundle.incomplete.json"
    decision_path = art_dir / "bundle.decision"
    fault = read_json_object(fault_path)
    if fault.get("schema") != "fln.check-setup-fault/1":
        raise EvidenceError("wrong setup-fault schema")
    identity_keys = (
        "run_id",
        "bead",
        "scenario",
        "step",
        "reason_code",
        "classification",
    )
    for key in identity_keys + ("argv", "cwd", "monotonic_ns", "wall_time_utc"):
        if key not in fault:
            raise EvidenceError(f"setup fault is missing {key}")
    if fault["classification"] not in PARTIAL_BUNDLE_CLASSIFICATIONS:
        raise EvidenceError(
            "partial bundle classification can never claim completion"
        )
    manifest = read_json_object(manifest_path)
    if manifest.get("schema") != "fln.evidence-manifest-incomplete/1":
        raise EvidenceError("wrong incomplete-manifest schema")
    for key in identity_keys:
        if manifest.get(key) != fault[key]:
            raise EvidenceError(
                f"incomplete manifest {key} disagrees with the setup fault"
            )
    if manifest.get("setup_fault_sha256") != sha256_file(fault_path):
        raise EvidenceError("incomplete manifest lost its setup-fault binding")
    manifest_data, _manifest_size, _manifest_digest = stable_file_facts(
        manifest_path
    )
    digest_data, _digest_size, _digest_digest = stable_file_facts(digest_path)
    expected_digest_line = (
        f"sha256:{hashlib.sha256(manifest_data).hexdigest()}"
        f"  {manifest_path.name}\n"
    ).encode()
    if not hmac.compare_digest(digest_data, expected_digest_line):
        raise EvidenceError("incomplete manifest digest does not match")
    recomputed = artifact_inventory(
        art_dir,
        excluded={manifest_path, digest_path, decision_path, marker_path},
    )
    if recomputed != manifest.get("artifacts"):
        raise EvidenceError(
            "partial bundle artifacts changed after publication"
        )
    marker = read_json_object(marker_path)
    if (
        marker.get("schema") != "fln.evidence-bundle-incomplete-commit/1"
        or marker.get("status") != "incomplete"
    ):
        raise EvidenceError("wrong incomplete-bundle marker schema")
    for key in identity_keys:
        if marker.get(key) != fault[key]:
            raise EvidenceError(
                f"incomplete marker {key} disagrees with the setup fault"
            )
    if (
        marker.get("setup_fault")
        != {"path": fault_path.name, "sha256": sha256_file(fault_path)}
        or marker.get("manifest")
        != {"path": manifest_path.name, "sha256": sha256_file(manifest_path)}
        or marker.get("manifest_digest")
        != {"path": digest_path.name, "sha256": sha256_file(digest_path)}
    ):
        raise EvidenceError("incomplete marker bindings do not match")
    marker_data, _marker_size, _marker_bytes_digest = stable_file_facts(
        marker_path
    )
    decision_data, _decision_size, _decision_digest = stable_file_facts(
        decision_path
    )
    if not hmac.compare_digest(marker_data, decision_data):
        raise EvidenceError(
            "incomplete marker does not match its commit decision"
        )
    return {
        "schema": "fln.partial-bundle-validation/1",
        "valid": True,
        "committed": False,
        "run_id": fault["run_id"],
        "step": fault["step"],
        "reason_code": fault["reason_code"],
        "classification": fault["classification"],
        "marker_sha256": sha256_file(marker_path),
    }


def add_fields(record: dict[str, Any], args: argparse.Namespace) -> None:
    occupied = set(record)
    for values, kind in (
        (args.string or [], "string"),
        (args.integer or [], "integer"),
        (args.boolean or [], "boolean"),
        (args.json_value or [], "json"),
    ):
        for key, raw in values:
            if key in occupied:
                raise EvidenceError(f"duplicate field: {key}")
            occupied.add(key)
            if kind == "string":
                record[key] = raw
            elif kind == "integer":
                record[key] = int(raw)
            elif kind == "boolean":
                if raw not in {"true", "false"}:
                    raise EvidenceError(f"boolean field {key} must be true or false")
                record[key] = raw == "true"
            else:
                record[key] = parse_json(raw, subject=f"field {key}")
    for key in args.null or []:
        if key in occupied:
            raise EvidenceError(f"duplicate field: {key}")
        occupied.add(key)
        record[key] = None
    for key, value in args.append_string or []:
        prior = record.setdefault(key, [])
        if not isinstance(prior, list):
            raise EvidenceError(f"field {key} is not a list")
        prior.append(value)
    for key, path_raw in args.json_file or []:
        if key in occupied:
            raise EvidenceError(f"duplicate field: {key}")
        occupied.add(key)
        data, _size, _digest = stable_file_facts(
            Path(path_raw), max_bytes=MAX_RECORD_BYTES
        )
        record[key] = parse_json(data, subject=path_raw)


def cmd_emit(args: argparse.Namespace) -> int:
    require_within(Path(args.file), Path(args.artifact_root), label="NDJSON log")
    record: dict[str, Any] = {}
    add_fields(record, args)
    append_record(Path(args.file), record, must_be_new=args.new_log)
    return PASS


def run_supervised_from_args(
    args: argparse.Namespace,
    guardian_identity: tuple[int, int] | None = None,
    initial_signal_mask: set[signal.Signals] | None = None,
) -> int:
    argv = list(args.command)
    if argv and argv[0] == "--":
        argv = argv[1:]
    return run_supervised(
        argv=argv,
        cwd=Path(args.cwd).resolve(strict=True),
        metadata_path=Path(args.metadata),
        stdout_path=Path(args.stdout),
        stderr_path=Path(args.stderr),
        readiness_path=Path(args.readiness),
        artifact_root=Path(args.artifact_root),
        capture_bytes=args.capture_bytes,
        output_budget_bytes=args.output_budget_bytes,
        setup_timeout_ms=args.setup_timeout_ms,
        timeout_ms=args.timeout_ms,
        grace_ms=args.grace_ms,
        stage_id=args.stage_id,
        planted=args.planted,
        semantic_failure_exits=args.semantic_failure_exit or [],
        cancel_after_ms=args.cancel_after_ms,
        restore_signal_state=False,
        test_terminal_delay_ms=args.test_terminal_delay_ms,
        test_terminal_ready_path=(
            Path(args.test_terminal_ready) if args.test_terminal_ready else None
        ),
        guardian_identity=guardian_identity,
        initial_signal_mask=initial_signal_mask,
        test_before_stop_delay_ms=args.test_before_stop_delay_ms,
        test_before_release_delay_ms=args.test_before_release_delay_ms,
        test_gate_mode=args.test_gate_mode,
        test_fault_point=args.test_fault_point,
        sealed_cargo=args.sealed_cargo,
        suite_lock_path=Path(args.suite_lock) if args.suite_lock else None,
        sealed_build_root=(
            Path(args.sealed_build_root) if args.sealed_build_root else None
        ),
    )


def cmd_run(args: argparse.Namespace) -> int:
    """Keep an outer subreaper alive if the inner supervisor is hard-killed."""
    signal.signal(signal.SIGCHLD, signal.SIG_DFL)
    enable_child_subreaper()
    guardian_facts = proc_stat_facts(os.getpid())
    if guardian_facts is None or guardian_facts[0] == "Z":
        raise EvidenceError("cannot bind guardian process identity")
    guardian_identity = (os.getpid(), guardian_facts[2])
    preflight_handle = open_process_handle(os.getpid())
    if preflight_handle is None:
        raise EvidenceError("cannot preflight guardian pidfd support")
    os.close(preflight_handle[1])
    watched = (signal.SIGHUP, signal.SIGINT, signal.SIGTERM)
    previous_mask = signal.pthread_sigmask(signal.SIG_BLOCK, watched)
    guardian_runtime_mask = set(previous_mask).difference(watched)
    if bool(args.launch_ready) != bool(args.launch_release):
        raise EvidenceError("guardian launch gate requires both control paths")
    if args.launch_ready:
        artifact_root = lexical_absolute(Path(args.artifact_root))
        launch_ready = require_within(
            Path(args.launch_ready), artifact_root, label="guardian launch readiness"
        )
        launch_release = require_within(
            Path(args.launch_release), artifact_root, label="guardian launch release"
        )
        launch_identity = {
            "schema": "fln.guardian-launch/1",
            "status": "awaiting_release",
            "stage_id": args.stage_id,
            "guardian_pid": guardian_identity[0],
            "guardian_start_ticks": guardian_identity[1],
        }
        write_atomic_new(launch_ready, canonical_json(launch_identity))
        release_deadline = (
            time.monotonic() + GUARDIAN_LAUNCH_RELEASE_TIMEOUT_MS / 1000
        )
        while True:
            try:
                release = read_json_object(launch_release)
            except FileNotFoundError:
                if time.monotonic() >= release_deadline:
                    raise EvidenceError("guardian launch release timed out")
                time.sleep(0.01)
                continue
            expected_release = dict(launch_identity)
            expected_release["status"] = "released"
            if release != expected_release:
                raise EvidenceError("guardian launch release identity mismatch")
            break
    worker_pid = os.fork()
    if worker_pid == 0:
        try:
            try:
                arm_parent_death_signal(guardian_identity[0], signal.SIGTERM)
                worker_exit = run_supervised_from_args(
                    args,
                    guardian_identity,
                    initial_signal_mask=previous_mask,
                )
            except BaseException as error:
                sys.stderr.write(
                    f"evidence worker: {type(error).__name__}: {error}\n"
                )
                worker_exit = SETUP_FAILURE
            os._exit(worker_exit)
        except BaseException:
            os._exit(SETUP_FAILURE)

    worker_handle: tuple[int, int] | None = None
    waited_status: int | None = None
    waited_pid = 0
    setup_error: BaseException | None = None
    cleanup_errors: list[str] = []
    survivors: list[int] = []
    worker_deadline_ns = time.monotonic_ns() + (
        args.setup_timeout_ms
        + args.timeout_ms
        + max(1_000, args.grace_ms) * 6
        + max(0, args.test_before_release_delay_ms)
        + max(0, args.test_terminal_delay_ms)
        + 30_000
    ) * 1_000_000

    def reap_worker_until(deadline_ns: int) -> bool:
        nonlocal waited_pid, waited_status
        worker_events: select.poll | None = None
        if worker_handle is not None:
            worker_events = select.poll()
            worker_events.register(
                worker_handle[1], select.POLLIN | select.POLLHUP | select.POLLERR
            )
        while waited_status is None:
            try:
                candidate_pid, candidate_status = os.waitpid(
                    worker_pid, os.WNOHANG
                )
            except InterruptedError:
                continue
            if candidate_pid == worker_pid:
                waited_pid = candidate_pid
                waited_status = candidate_status
                return True
            if candidate_pid != 0:
                raise EvidenceError("guardian reaped an unexpected process")
            now_ns = time.monotonic_ns()
            if now_ns >= deadline_ns:
                return False
            wait_ms = max(
                1,
                min(50, (deadline_ns - now_ns + 999_999) // 1_000_000),
            )
            if worker_events is not None:
                worker_events.poll(wait_ms)
            else:
                time.sleep(wait_ms / 1000)
        return True

    try:
        if args.test_fail_guardian_pidfd_open:
            if args.test_guardian_child_ready:
                readiness = require_within(
                    Path(args.test_guardian_child_ready),
                    Path(args.artifact_root),
                    label="guardian fault child readiness",
                )
                deadline = time.monotonic() + 15.0
                previous_payload: bytes | None = None
                stable_reads = 0
                while time.monotonic() < deadline:
                    try:
                        payload, _size, _digest = stable_file_facts(
                            readiness, max_bytes=128
                        )
                        values = tuple(
                            int(value)
                            for value in payload.decode("ascii").splitlines()
                        )
                        if (
                            len(values) == 2
                            and len(set(values)) == 2
                            and all(value > 1 for value in values)
                        ):
                            stable_reads = (
                                stable_reads + 1 if payload == previous_payload else 1
                            )
                            previous_payload = payload
                            if stable_reads >= 2:
                                break
                        else:
                            stable_reads = 0
                            previous_payload = None
                    except (EvidenceError, FileNotFoundError, UnicodeError, ValueError):
                        stable_reads = 0
                        previous_payload = None
                    time.sleep(0.01)
                else:
                    raise EvidenceError(
                        "guardian fault child PID handshake did not stabilize"
                    )
            else:
                readiness = Path(args.readiness)
                deadline = time.monotonic() + 15.0
                while not readiness.exists() and time.monotonic() < deadline:
                    time.sleep(0.01)
                if not readiness.exists():
                    raise EvidenceError("guardian fault readiness timed out")
            raise OSError(errno.EMFILE, "injected post-fork pidfd_open failure")
        worker_handle = open_process_handle(worker_pid)
        if worker_handle is None:
            waited_pid, status = os.waitpid(worker_pid, os.WNOHANG)
            if waited_pid == worker_pid:
                waited_status = status
            else:
                raise EvidenceError("cannot bind live inner supervisor")

        def forward_signal(signum: int, _frame: Any) -> None:
            if worker_handle is not None:
                signal_process_handle(worker_pid, worker_handle, signum)

        for signum in watched:
            signal.signal(signum, forward_signal)
        signal.pthread_sigmask(signal.SIG_SETMASK, guardian_runtime_mask)
        if not reap_worker_until(worker_deadline_ns):
            raise EvidenceError("inner supervisor exceeded guardian wall deadline")
    except BaseException as error:
        setup_error = error
        try:
            signal.pthread_sigmask(signal.SIG_BLOCK, watched)
        except BaseException as cleanup_error:
            cleanup_errors.append(f"cannot block cleanup signals: {cleanup_error}")
        for signum in watched:
            try:
                signal.signal(signum, signal.SIG_IGN)
            except BaseException as cleanup_error:
                cleanup_errors.append(
                    f"cannot ignore cleanup signal {signum}: {cleanup_error}"
                )
        if waited_status is None:
            signalled = False
            if worker_handle is not None:
                try:
                    signalled = signal_process_handle(
                        worker_pid, worker_handle, signal.SIGKILL
                    )
                except BaseException as cleanup_error:
                    cleanup_errors.append(
                        f"cannot signal failed inner supervisor by pidfd: {cleanup_error}"
                    )
            if not signalled:
                try:
                    # W is still our unreaped direct child, so this numeric PID
                    # cannot be recycled before the following waitpid.
                    os.kill(worker_pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                except BaseException as cleanup_error:
                    cleanup_errors.append(
                        f"cannot signal failed inner supervisor by PID: {cleanup_error}"
                    )
            cleanup_deadline_ns = time.monotonic_ns() + max(
                1_000, args.grace_ms + 1_000
            ) * 1_000_000
            try:
                if not reap_worker_until(cleanup_deadline_ns):
                    cleanup_errors.append(
                        "failed inner supervisor did not reap within cleanup budget"
                    )
            except ChildProcessError as cleanup_error:
                cleanup_errors.append(
                    f"cannot reap failed inner supervisor: {cleanup_error}"
                )
            except BaseException as cleanup_error:
                cleanup_errors.append(
                    f"failed while reaping inner supervisor: {cleanup_error}"
                )
            if waited_pid not in {0, worker_pid}:
                setup_error = EvidenceError(
                    "guardian lost the failed inner supervisor"
                )
    finally:
        if worker_handle is not None:
            try:
                os.close(worker_handle[1])
            except BaseException as cleanup_error:
                cleanup_errors.append(
                    f"cannot close inner supervisor pidfd: {cleanup_error}"
                )
        try:
            survivors = cleanup_guardian_descendants(worker_pid)
        except BaseException as cleanup_error:
            cleanup_errors.append(
                f"cannot prove guardian descendant cleanup: {cleanup_error}"
            )
    if survivors:
        raise EvidenceError(
            f"guardian containment remained unproven for PIDs {survivors}"
        )
    if cleanup_errors:
        raise EvidenceError("; ".join(cleanup_errors))
    if setup_error is not None:
        raise EvidenceError(
            f"guardian setup failed after fork: {type(setup_error).__name__}: {setup_error}"
        ) from setup_error
    if waited_status is None:
        raise EvidenceError("guardian lost inner supervisor status")
    worker_exit = os.waitstatus_to_exitcode(waited_status)
    if worker_exit in {PASS, FAIL, SETUP_FAILURE, INCONCLUSIVE, CANCELLED}:
        return worker_exit
    raise EvidenceError(f"inner supervisor died unexpectedly with status {worker_exit}")


def cmd_validate_verification_manifest(args: argparse.Namespace) -> int:
    try:
        report = validate_verification_manifest(
            Path(args.manifest), Path(args.beads)
        )
    except (
        EvidenceError,
        OSError,
        ValueError,
        TypeError,
        KeyError,
        IndexError,
    ) as error:
        print(f"verification-manifest: {error}", file=sys.stderr)
        return FAIL
    if args.output:
        write_new(Path(args.output), canonical_json(report))
    else:
        sys.stdout.buffer.write(canonical_json(report))
    return PASS


def cmd_render_check_human(args: argparse.Namespace) -> int:
    artifact_root = lexical_absolute(Path(args.artifact_root))
    run_path = require_exact_artifact_path(
        Path(args.file), artifact_root, "run.ndjson", label="check run"
    )
    output = require_exact_artifact_path(
        Path(args.output), artifact_root, CHECK_HUMAN_LOG, label="check human log"
    )
    records = load_ndjson(run_path)
    write_new(output, render_check_human(records))
    validate_check_human(run_path, output)
    return PASS


def cmd_validate_guard(args: argparse.Namespace) -> int:
    report = validate_guard(
        Path(args.file),
        args.expected_exit,
        args.expected_verdict,
        args.finding or [],
        args.expected_root,
        args.observed_exit,
    )
    if args.output:
        require_within(
            Path(args.output), Path(args.artifact_root), label="guard validation"
        )
        write_new(Path(args.output), canonical_json(report))
    else:
        sys.stdout.buffer.write(canonical_json(report))
    return PASS


def cmd_validate_environment_collision(args: argparse.Namespace) -> int:
    artifact_root = lexical_absolute(Path(args.artifact_root))
    stdout_path = require_within(
        Path(args.file), artifact_root, label="environment-collision log"
    )
    stderr_path = require_within(
        Path(args.stderr_file), artifact_root, label="environment-collision stderr"
    )
    report = validate_environment_collision(
        stdout_path,
        stderr_path,
        args.phase,
        args.expected_run_id,
        args.observed_exit,
        artifact_root=artifact_root,
        expected_stdout_artifact=args.expected_stdout_artifact,
        expected_stderr_artifact=args.expected_stderr_artifact,
        expected_cwd=args.expected_cwd,
        expected_argv=args.expected_argv,
        expected_cache_state=args.expected_cache_state,
    )
    if args.output:
        output = require_within(
            Path(args.output),
            artifact_root,
            label="environment-collision validation",
        )
        write_new(output, canonical_json(report))
    else:
        sys.stdout.buffer.write(canonical_json(report))
    return PASS


def cmd_validate_verdict_schema(args: argparse.Namespace) -> int:
    artifact_root = lexical_absolute(Path(args.artifact_root))
    semantic_path = require_within(
        Path(args.semantic), artifact_root, label="Verdict semantic evidence"
    )
    telemetry_path = require_within(
        Path(args.telemetry), artifact_root, label="Verdict telemetry"
    )
    stdout_path = require_within(
        Path(args.stdout), artifact_root, label="Verdict stdout"
    )
    stderr_path = require_within(
        Path(args.stderr), artifact_root, label="Verdict stderr"
    )
    positive_semantic_path = (
        require_within(
            Path(args.positive_semantic),
            artifact_root,
            label="Verdict positive semantic baseline",
        )
        if args.positive_semantic
        else None
    )
    report = validate_verdict_schema_evidence(
        semantic_path,
        telemetry_path,
        stdout_path,
        stderr_path,
        args.phase,
        args.observed_exit,
        positive_semantic_path=positive_semantic_path,
    )
    if args.output:
        output = require_within(
            Path(args.output), artifact_root, label="Verdict schema validation"
        )
        write_new(output, canonical_json(report))
    else:
        sys.stdout.buffer.write(canonical_json(report))
    return PASS


def cmd_validate_environment_resource_collision(args: argparse.Namespace) -> int:
    artifact_root = lexical_absolute(Path(args.artifact_root))
    stdout_path = require_within(
        Path(args.file), artifact_root, label="environment-resource-collision log"
    )
    stderr_path = require_within(
        Path(args.stderr_file),
        artifact_root,
        label="environment-resource-collision stderr",
    )
    report = validate_environment_resource_collision(
        stdout_path,
        stderr_path,
        args.phase,
        args.expected_run_id,
        args.observed_exit,
        artifact_root=artifact_root,
        expected_stdout_artifact=args.expected_stdout_artifact,
        expected_stderr_artifact=args.expected_stderr_artifact,
        expected_cwd=args.expected_cwd,
        expected_argv=args.expected_argv,
        expected_cache_state=args.expected_cache_state,
    )
    if args.output:
        output = require_within(
            Path(args.output),
            artifact_root,
            label="environment-resource-collision validation",
        )
        write_new(output, canonical_json(report))
    else:
        sys.stdout.buffer.write(canonical_json(report))
    return PASS


def cmd_validate_environment_identity(
    args: argparse.Namespace,
    validator: Callable[..., dict[str, Any]],
    *,
    label: str,
) -> int:
    artifact_root = lexical_absolute(Path(args.artifact_root))
    stdout_path = require_within(
        Path(args.file), artifact_root, label=f"{label} stdout"
    )
    stderr_path = require_within(
        Path(args.stderr_file), artifact_root, label=f"{label} stderr"
    )
    report = validator(
        stdout_path,
        stderr_path,
        args.expected_run_id,
        args.observed_exit,
        artifact_root=artifact_root,
        expected_stdout_artifact=args.expected_stdout_artifact,
        expected_stderr_artifact=args.expected_stderr_artifact,
    )
    if args.output:
        output = require_within(
            Path(args.output), artifact_root, label=f"{label} validation"
        )
        write_new(output, canonical_json(report))
    else:
        sys.stdout.buffer.write(canonical_json(report))
    return PASS


def cmd_validate_declaration_tag_matrix(args: argparse.Namespace) -> int:
    return cmd_validate_environment_identity(
        args,
        validate_declaration_tag_matrix,
        label="declaration-tag-matrix",
    )


def cmd_validate_declaration_membership(args: argparse.Namespace) -> int:
    return cmd_validate_environment_identity(
        args,
        validate_declaration_membership,
        label="declaration-membership",
    )


def cmd_validate_extension_descriptor_matrix(args: argparse.Namespace) -> int:
    return cmd_validate_environment_identity(
        args,
        validate_extension_descriptor_matrix,
        label="extension-descriptor-matrix",
    )


def cmd_validate_environment_state(args: argparse.Namespace) -> int:
    return cmd_validate_environment_identity(
        args,
        validate_environment_state,
        label="environment-state",
    )


def cmd_validate_declaration_admission(args: argparse.Namespace) -> int:
    return cmd_validate_environment_identity(
        args,
        validate_declaration_admission,
        label="declaration-admission",
    )


def cmd_validate_kernel_admission(args: argparse.Namespace) -> int:
    artifact_root = lexical_absolute(Path(args.artifact_root))
    stdout_path = require_within(
        Path(args.file), artifact_root, label="kernel-admission log"
    )
    stderr_path = require_within(
        Path(args.stderr_file), artifact_root, label="kernel-admission stderr"
    )
    report = validate_kernel_admission(
        stdout_path,
        stderr_path,
        args.phase,
        args.expected_run_id,
        args.observed_exit,
        artifact_root=artifact_root,
        expected_stdout_artifact=args.expected_stdout_artifact,
        expected_stderr_artifact=args.expected_stderr_artifact,
        expected_cwd=args.expected_cwd,
        expected_argv=args.expected_argv,
        expected_cache_state=args.expected_cache_state,
        expected_input_root=args.expected_input_root,
    )
    if args.output:
        output = require_within(
            Path(args.output),
            artifact_root,
            label="kernel-admission validation",
        )
        write_new(output, canonical_json(report))
    else:
        sys.stdout.buffer.write(canonical_json(report))
    return PASS


def cmd_validate_run(args: argparse.Namespace) -> int:
    report = validate_run(
        Path(args.file),
        args.schema,
        args.expected_verdict,
        expected_active_stage=args.expected_active_stage,
        expected_planted_stage=args.expected_planted_stage,
        live_context=not args.offline,
    )
    if args.output:
        require_within(
            Path(args.output), Path(args.artifact_root), label="run validation"
        )
        write_new(Path(args.output), canonical_json(report))
    else:
        sys.stdout.buffer.write(canonical_json(report))
    return PASS


def cmd_validate_supervisor(args: argparse.Namespace) -> int:
    report = validate_supervisor_file(Path(args.file), args.expected_stage_id)
    if args.output:
        if not args.artifact_root:
            raise EvidenceError(
                "validate-supervisor --output requires --artifact-root"
            )
        output = require_within(
            Path(args.output),
            Path(args.artifact_root),
            label="supervisor validation",
        )
        write_new(output, canonical_json(report))
    else:
        sys.stdout.buffer.write(canonical_json(report))
    return PASS


def cmd_hash_tree(args: argparse.Namespace) -> int:
    inventory_path = Path(args.inventory) if args.inventory else None
    if args.test_mutate_input:
        global _TEST_MUTATE_DURING_READ
        _TEST_MUTATE_DURING_READ = lexical_absolute(
            Path(args.root) / args.test_mutate_input
        )
    root = tree_hash(
        Path(args.root),
        args.path,
        inventory_path=inventory_path,
        vendor_path=args.vendor_path,
    )
    if args.output:
        if not args.artifact_root:
            raise EvidenceError("hash-tree --output requires --artifact-root")
        require_within(
            Path(args.output), Path(args.artifact_root), label="tree-hash output"
        )
        write_new(Path(args.output), f"{root}\n".encode())
    else:
        print(root)
    return PASS


def cmd_vendor_binding(args: argparse.Namespace) -> int:
    binding = verify_vendor_binding(Path(args.root), args.vendor_path)
    if args.output:
        require_within(
            Path(args.output), Path(args.artifact_root), label="vendor binding"
        )
        write_new(Path(args.output), canonical_json(binding))
    else:
        sys.stdout.buffer.write(canonical_json(binding))
    return PASS


UNSAFE_NOTE_SITE_SCHEMA = "fln-unsafe-note-clippy-sites/1"
UNSAFE_NOTE_LINT = "clippy::undocumented_unsafe_blocks"
UNSAFE_NOTE_MAX_REPORT_BYTES = 64 * 1024 * 1024
UNSAFE_NOTE_MAX_SOURCE_BYTES = 8 * 1024 * 1024
UNSAFE_NOTE_MAX_REPORT_LINES = 100_000
UNSAFE_NOTE_CONTEXT_LINES = 6
UNSAFE_NOTE_MISMATCH = 101


def render_unsafe_note_sites(rows: Iterable[tuple[str, str, str]]) -> bytes:
    ordered = sorted(rows)
    lines = [
        f"schema {UNSAFE_NOTE_SITE_SCHEMA}",
        f"lint {UNSAFE_NOTE_LINT}",
        "columns\tpath\tfunction\tcontext_sha256",
    ]
    lines.extend(
        f"site\t{path}\t{function}\t{digest}"
        for path, function, digest in ordered
    )
    return ("\n".join(lines) + "\n").encode("utf-8")


def parse_unsafe_note_sites(path: Path) -> set[tuple[str, str, str]]:
    data, _size, _digest = stable_file_facts(
        path, max_bytes=UNSAFE_NOTE_MAX_REPORT_BYTES
    )
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        raise EvidenceError(f"{path}: unsafe-note site list is not UTF-8") from error
    lines = text.splitlines()
    expected_header = [
        f"schema {UNSAFE_NOTE_SITE_SCHEMA}",
        f"lint {UNSAFE_NOTE_LINT}",
        "columns\tpath\tfunction\tcontext_sha256",
    ]
    if lines[:3] != expected_header:
        raise EvidenceError(f"{path}: unsafe-note site-list header is invalid")
    rows: set[tuple[str, str, str]] = set()
    for index, line in enumerate(lines[3:], start=4):
        columns = line.split("\t")
        if len(columns) != 4 or columns[0] != "site":
            raise EvidenceError(f"{path}:{index}: malformed unsafe-note site row")
        relative, function, digest = columns[1:]
        relative_path = Path(relative)
        if (
            relative_path.is_absolute()
            or ".." in relative_path.parts
            or relative_path.as_posix() != relative
            or not relative.startswith("crates/fln-unsafe-")
            or not relative.endswith(".rs")
        ):
            raise EvidenceError(f"{path}:{index}: invalid unsafe-note source path")
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", function) is None:
            raise EvidenceError(f"{path}:{index}: invalid enclosing function")
        if re.fullmatch(r"sha256:[0-9a-f]{64}", digest) is None:
            raise EvidenceError(f"{path}:{index}: invalid context digest")
        row = (relative, function, digest)
        if row in rows:
            raise EvidenceError(f"{path}:{index}: duplicate unsafe-note site row")
        rows.add(row)
    if render_unsafe_note_sites(rows) != data:
        raise EvidenceError(f"{path}: unsafe-note site list is not canonical")
    return rows


def extract_unsafe_note_sites(
    root: Path, report_path: Path
) -> set[tuple[str, str, str]]:
    root = root.resolve(strict=True)
    report, _size, _digest = stable_file_facts(
        report_path, max_bytes=UNSAFE_NOTE_MAX_REPORT_BYTES
    )
    try:
        report_text = report.decode("utf-8")
    except UnicodeDecodeError as error:
        raise EvidenceError(f"{report_path}: Clippy report is not UTF-8") from error
    report_lines = report_text.splitlines()
    if len(report_lines) > UNSAFE_NOTE_MAX_REPORT_LINES:
        raise EvidenceError(
            f"{report_path}: Clippy report exceeds "
            f"{UNSAFE_NOTE_MAX_REPORT_LINES} records"
        )

    diagnostic_spans: set[tuple[str, int, int]] = set()
    rows: set[tuple[str, str, str]] = set()
    function_pattern = re.compile(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(")
    for index, line in enumerate(report_lines, start=1):
        if len(line.encode("utf-8")) > MAX_RECORD_BYTES:
            raise EvidenceError(f"{report_path}:{index}: JSON record is too large")
        record = parse_json(line.encode("utf-8"), subject=f"{report_path}:{index}")
        if not isinstance(record, dict):
            raise EvidenceError(f"{report_path}:{index}: JSON record is not an object")
        if record.get("reason") != "compiler-message":
            continue
        message = record.get("message")
        if not isinstance(message, dict):
            raise EvidenceError(
                f"{report_path}:{index}: compiler-message payload is not an object"
            )
        code = message.get("code")
        if not isinstance(code, dict) or code.get("code") != UNSAFE_NOTE_LINT:
            continue
        primary = [
            span
            for span in message.get("spans", [])
            if isinstance(span, dict) and span.get("is_primary") is True
        ]
        if len(primary) != 1:
            raise EvidenceError(
                f"{report_path}:{index}: unsafe-note diagnostic needs one primary span"
            )
        span = primary[0]
        relative = span.get("file_name")
        byte_start = span.get("byte_start")
        byte_end = span.get("byte_end")
        if (
            not isinstance(relative, str)
            or not isinstance(byte_start, int)
            or not isinstance(byte_end, int)
            or byte_start < 0
            or byte_end <= byte_start
        ):
            raise EvidenceError(
                f"{report_path}:{index}: unsafe-note span facts are invalid"
            )
        relative_path = Path(relative)
        if (
            relative_path.is_absolute()
            or ".." in relative_path.parts
            or relative_path.as_posix() != relative
            or not relative.startswith("crates/fln-unsafe-")
            or not relative.endswith(".rs")
        ):
            raise EvidenceError(
                f"{report_path}:{index}: unsafe-note span escapes boundary crates"
            )
        span_key = (relative, byte_start, byte_end)
        if span_key in diagnostic_spans:
            continue
        diagnostic_spans.add(span_key)

        source_path = require_within(
            root / relative_path, root, label="unsafe-note Clippy source"
        )
        source, _source_size, _source_digest = stable_file_facts(
            source_path, max_bytes=UNSAFE_NOTE_MAX_SOURCE_BYTES
        )
        if byte_end > len(source):
            raise EvidenceError(
                f"{report_path}:{index}: unsafe-note span exceeds {relative}"
            )
        try:
            source_text = source.decode("utf-8")
        except UnicodeDecodeError as error:
            raise EvidenceError(f"{relative}: Rust source is not UTF-8") from error
        line_index = source[:byte_start].count(b"\n")
        source_lines = source_text.splitlines()
        if line_index >= len(source_lines):
            raise EvidenceError(
                f"{report_path}:{index}: unsafe-note span line is absent"
            )
        function = None
        for source_line in reversed(source_lines[: line_index + 1]):
            match = function_pattern.search(source_line)
            if match is not None:
                function = match.group(1)
                break
        if function is None:
            raise EvidenceError(
                f"{report_path}:{index}: unsafe-note site has no enclosing function"
            )
        context = "\n".join(
            source_line.strip()
            for source_line in source_lines[
                line_index : line_index + UNSAFE_NOTE_CONTEXT_LINES
            ]
        ).encode("utf-8")
        context_digest = f"sha256:{hashlib.sha256(context).hexdigest()}"
        row = (relative, function, context_digest)
        if row in rows:
            raise EvidenceError(
                f"{report_path}:{index}: line-independent unsafe-note identity collided"
            )
        rows.add(row)
    return rows


def cmd_unsafe_note_clippy_sites(args: argparse.Namespace) -> int:
    operation = args.operation
    artifact_root = Path(args.artifact_root) if args.artifact_root else None
    if operation == "extract":
        if not args.root or not args.report or not args.output or artifact_root is None:
            raise EvidenceError(
                "unsafe-note extract requires --root, --report, --output, "
                "and --artifact-root"
            )
        rows = extract_unsafe_note_sites(Path(args.root), Path(args.report))
        output = require_within(
            Path(args.output), artifact_root, label="unsafe-note observed sites"
        )
        write_new(output, render_unsafe_note_sites(rows))
        print(f"unsafe-note clippy extract: {len(rows)} unique sites")
        return PASS

    if operation == "compare":
        if not args.declared or not args.observed:
            raise EvidenceError(
                "unsafe-note compare requires --declared and --observed"
            )
        declared = parse_unsafe_note_sites(Path(args.declared))
        observed = parse_unsafe_note_sites(Path(args.observed))
        unexpected = sorted(observed - declared)
        stale = sorted(declared - observed)
        for row in unexpected:
            print(
                "undeclared clippy site: " + "\t".join(row),
                file=sys.stderr,
            )
        for row in stale:
            print(
                "stale declared clippy site: " + "\t".join(row),
                file=sys.stderr,
            )
        if unexpected or stale:
            return UNSAFE_NOTE_MISMATCH
        print(f"unsafe-note clippy match: {len(observed)} sites")
        return PASS

    if operation in {"drop-first", "add-observed", "add-stale"}:
        if not args.declared or not args.output or artifact_root is None:
            raise EvidenceError(
                f"unsafe-note {operation} requires --declared, --output, "
                "and --artifact-root"
            )
        rows = parse_unsafe_note_sites(Path(args.declared))
        if operation == "drop-first":
            if not rows:
                raise EvidenceError("cannot drop a site from an empty declaration")
            removed = sorted(rows)[0]
            rows.remove(removed)
            detail = "dropped " + "\t".join(removed)
        elif operation == "add-observed":
            planted = (
                "crates/fln-unsafe-abi/src/__planted_undeclared__.rs",
                "planted_undeclared_site",
                "sha256:" + ("f" * 64),
            )
            if planted in rows:
                raise EvidenceError("planted undeclared unsafe-note site already exists")
            rows.add(planted)
            detail = "added " + "\t".join(planted)
        else:
            planted = (
                "crates/fln-unsafe-abi/src/__planted_stale__.rs",
                "planted_stale_site",
                "sha256:" + ("0" * 64),
            )
            if planted in rows:
                raise EvidenceError("planted stale unsafe-note site already exists")
            rows.add(planted)
            detail = "added " + "\t".join(planted)
        output = require_within(
            Path(args.output), artifact_root, label="unsafe-note mutant declaration"
        )
        write_new(output, render_unsafe_note_sites(rows))
        print(f"unsafe-note clippy mutant: {detail}")
        return PASS

    raise EvidenceError(f"unknown unsafe-note operation: {operation}")


def cmd_ubs_inventory(args: argparse.Namespace) -> int:
    root = Path(args.root)
    inventory = collect_ubs_inventory(root, args.scope)
    output = Path(args.output)
    require_within(output, Path(args.artifact_root), label="UBS inventory")
    write_new(output, canonical_json(inventory))
    validate_ubs_inventory(output, root, require_live_scope=True)
    return PASS


def cmd_validate_ubs_inventory(args: argparse.Namespace) -> int:
    report = validate_ubs_inventory(
        Path(args.inventory),
        Path(args.root),
        require_live_scope=args.require_live_scope,
    )
    sys.stdout.buffer.write(canonical_json(report))
    return PASS


def cmd_exec_ubs_inventory(args: argparse.Namespace) -> int:
    command = list(args.command)
    if command and command[0] == "--":
        command = command[1:]
    if not command:
        raise EvidenceError("inventory execution requires a command")
    inventory = validate_ubs_inventory(Path(args.inventory), Path(args.root))
    argv = [*command, *(row["path"] for row in inventory["files"])]
    os.execvp(argv[0], argv)
    raise EvidenceError("inventory execution unexpectedly returned")


def cmd_stopped_exec(args: argparse.Namespace) -> int:
    command = list(args.command)
    if command and command[0] == "--":
        command = command[1:]
    if not command:
        raise EvidenceError("stopped exec requires a command")
    if args.exec_status_fd is not None:
        try:
            if args.exec_status_fd <= 2:
                raise EvidenceError("exec status descriptor must not be a stdio stream")
            os.fstat(args.exec_status_fd)
            # subprocess pass_fds admits this descriptor into the helper. Restore
            # CLOEXEC before stopping so EOF is the target-exec success signal.
            os.set_inheritable(args.exec_status_fd, False)
        except BaseException:
            return SETUP_FAILURE
    try:
        arm_parent_death_kill(args.expected_parent_pid)
        os.kill(os.getpid(), signal.SIGSTOP)
    except BaseException:
        return SETUP_FAILURE
    try:
        os.execvp(command[0], command)
        raise EvidenceError("stopped exec unexpectedly returned")
    except BaseException as error:
        if args.exec_status_fd is not None:
            try:
                write_exec_failure_status(args.exec_status_fd, error)
            finally:
                os.close(args.exec_status_fd)
        return SETUP_FAILURE


def cmd_emergency_kill(args: argparse.Namespace) -> int:
    emergency_kill(
        Path(args.readiness), args.expected_wrapper_pid, args.expected_stage_id
    )
    return PASS


def cmd_process_start_ticks(args: argparse.Namespace) -> int:
    if args.wait_ms < 0 or args.wait_ms > MAX_PROCESS_IDENTITY_WAIT_MS:
        raise EvidenceError("process identity wait must be between 0 and 30000 ms")
    if args.pid == os.getpid():
        raise EvidenceError("process identity target cannot be the binder itself")
    deadline = time.monotonic() + args.wait_ms / 1000
    handle = bind_direct_child_until(
        args.pid, args.expected_parent_pid, deadline
    )
    try:
        while True:
            facts = proc_stat_facts(args.pid)
            if (
                facts is None
                or facts[0] == "Z"
                or facts[2] != handle[0]
                or args.pid not in proc_children(args.expected_parent_pid)
            ):
                raise EvidenceError("process disappeared before session binding")
            session_ready = not args.session_leader or facts[1] == args.pid
            stopped_ready = not args.stopped or facts[0] in {"T", "t"}
            if session_ready and stopped_ready:
                print(handle[0])
                return PASS
            if time.monotonic() >= deadline:
                signal_process_handle(args.pid, handle, signal.SIGKILL)
                raise EvidenceError("process did not become a session leader in time")
            time.sleep(0.005)
    finally:
        os.close(handle[1])


def cmd_release_process_launch(args: argparse.Namespace) -> int:
    if args.wait_ms < 0 or args.wait_ms > MAX_PROCESS_IDENTITY_WAIT_MS:
        raise EvidenceError("guardian launch wait must be between 0 and 30000 ms")
    artifact_root = lexical_absolute(Path(args.artifact_root))
    ready_path = require_within(
        Path(args.ready), artifact_root, label="guardian launch readiness"
    )
    output_path = require_within(
        Path(args.output), artifact_root, label="guardian launch release"
    )
    deadline = time.monotonic() + args.wait_ms / 1000
    while True:
        try:
            ready = read_json_object(ready_path)
            break
        except FileNotFoundError:
            if time.monotonic() >= deadline:
                raise EvidenceError("guardian launch readiness timed out")
            time.sleep(0.005)
    expected = {
        "schema": "fln.guardian-launch/1",
        "status": "awaiting_release",
        "stage_id": args.stage_id,
        "guardian_pid": args.pid,
        "guardian_start_ticks": args.expected_start_ticks,
    }
    if ready != expected:
        raise EvidenceError("guardian launch readiness identity mismatch")
    released = dict(expected)
    released["status"] = "released"
    released_data = canonical_json(released)
    try:
        observed, _size, _digest = stable_file_facts(output_path)
    except FileNotFoundError:
        pass
    else:
        if not hmac.compare_digest(observed, released_data):
            raise EvidenceError("guardian launch release already has wrong bytes")
        return PASS
    if args.pid == os.getpid():
        raise EvidenceError("guardian launch target cannot be the releaser itself")
    handle = open_process_handle(
        args.pid, expected_parent_pid=args.expected_parent_pid
    )
    if handle is None or handle[0] != args.expected_start_ticks:
        if handle is not None:
            os.close(handle[1])
        raise EvidenceError("guardian changed before launch release")
    try:
        try:
            write_atomic_new(output_path, released_data)
        except BaseException:
            try:
                observed, _size, _digest = stable_file_facts(output_path)
            except BaseException:
                raise
            if not hmac.compare_digest(observed, released_data):
                raise
    finally:
        os.close(handle[1])
    return PASS


def cmd_kill_bound_group(args: argparse.Namespace) -> int:
    kill_bound_process_group(
        args.pid, args.expected_start_ticks, args.expected_parent_pid
    )
    return PASS


def cmd_kill_direct_child(args: argparse.Namespace) -> int:
    """Kill one currently direct child through a pidfd, never a numeric PID."""
    if (
        args.pid <= 1
        or args.expected_parent_pid <= 1
        or args.pid in {os.getpid(), args.expected_parent_pid}
        or args.wait_ms < 0
        or args.wait_ms > 5000
    ):
        raise EvidenceError("direct-child cleanup identity is malformed")
    handle = open_process_handle(
        args.pid, expected_parent_pid=args.expected_parent_pid
    )
    if handle is None:
        return PASS
    try:
        if not signal_process_handle(args.pid, handle, signal.SIGKILL):
            return PASS
        deadline = time.monotonic() + args.wait_ms / 1000
        while process_handle_alive(args.pid, handle):
            if time.monotonic() >= deadline:
                raise EvidenceError("direct child remained live after pidfd SIGKILL")
            time.sleep(0.005)
    finally:
        os.close(handle[1])
    return PASS


def cmd_signal_bound_process(args: argparse.Namespace) -> int:
    signum = {
        "HUP": signal.SIGHUP,
        "INT": signal.SIGINT,
        "TERM": signal.SIGTERM,
    }[args.signal]
    signal_bound_process(args.pid, args.expected_start_ticks, signum)
    return PASS


def cmd_resume_bound_process(args: argparse.Namespace) -> int:
    if args.pid == os.getpid():
        raise EvidenceError("resume target cannot be the helper itself")
    handle = open_process_handle(
        args.pid, expected_parent_pid=args.expected_parent_pid
    )
    if handle is None or handle[0] != args.expected_start_ticks:
        if handle is not None:
            os.close(handle[1])
        raise EvidenceError("stopped process changed before resume")
    try:
        facts = proc_stat_facts(args.pid)
        if (
            facts is None
            or facts[0] not in {"T", "t"}
            or facts[2] != args.expected_start_ticks
        ):
            raise EvidenceError("process was not stopped at resume linearization")
        if not signal_process_handle(args.pid, handle, signal.SIGCONT):
            raise EvidenceError("stopped process disappeared before resume")
    finally:
        os.close(handle[1])
    return PASS


def cmd_assert_process_group_empty(args: argparse.Namespace) -> int:
    if args.pgid <= 1 or args.wait_ms < 0 or args.wait_ms > 30_000:
        raise EvidenceError("process-group emptiness arguments are malformed")
    deadline = time.monotonic() + args.wait_ms / 1000
    while True:
        live = live_process_group_members(args.pgid)
        if not live:
            return PASS
        if time.monotonic() >= deadline:
            raise EvidenceError(
                f"process group {args.pgid} retained live members {sorted(live)}"
            )
        time.sleep(0.01)


def cmd_manifest(args: argparse.Namespace) -> int:
    generate_manifest(
        Path(args.art_dir),
        Path(args.output),
        Path(args.digest_output),
        args.run_id,
        args.bead,
        args.scenario,
        args.verdict,
        args.input_root,
        args.final_root,
    )
    return PASS


def cmd_validate_manifest(args: argparse.Namespace) -> int:
    validate_manifest(
        Path(args.art_dir),
        Path(args.manifest),
        Path(args.digest),
        live_context=not args.offline,
    )
    return PASS


def cmd_complete_bundle(args: argparse.Namespace) -> int:
    if bool(args.test_marker_pause_ready) != bool(args.test_marker_pause_release):
        raise EvidenceError(
            "marker-link pause requires both its readiness and release paths"
        )
    complete_bundle(
        Path(args.art_dir),
        Path(args.manifest),
        Path(args.digest),
        Path(args.output),
        governed_root=Path(args.governed_root),
        governed_paths=args.governed_path,
        expected_root=args.expected_root,
        inventory_path=Path(args.inventory) if args.inventory else None,
        vendor_path=args.vendor_path,
        restore_signal_state=False,
        test_fail_after_link=args.test_fail_after_link,
        test_marker_pause=(
            (Path(args.test_marker_pause_ready), Path(args.test_marker_pause_release))
            if args.test_marker_pause_ready
            else None
        ),
    )
    return PASS


def cmd_validate_bundle(args: argparse.Namespace) -> int:
    report = validate_bundle(
        Path(args.art_dir),
        Path(args.manifest),
        Path(args.digest),
        Path(args.commit),
    )
    if args.output:
        output = lexical_absolute(Path(args.output))
        art_dir = lexical_absolute(Path(args.art_dir))
        try:
            output.relative_to(art_dir)
        except ValueError:
            pass
        else:
            raise EvidenceError(
                "bundle validation output cannot mutate the committed bundle"
            )
        require_within(
            Path(args.output), Path(args.artifact_root), label="bundle validation"
        )
        write_new(Path(args.output), canonical_json(report))
    else:
        sys.stdout.buffer.write(canonical_json(report))
    return PASS


def cmd_publish_partial_bundle(args: argparse.Namespace) -> int:
    argv_value = parse_json(
        args.argv_json.encode("utf-8"), subject="partial bundle argv"
    )
    if not isinstance(argv_value, list) or not all(
        isinstance(item, str) for item in argv_value
    ):
        raise EvidenceError("partial bundle argv must be a JSON string array")
    publish_partial_bundle(
        Path(args.art_dir),
        run_id=args.run_id,
        bead=args.bead,
        scenario=args.scenario,
        step=args.step,
        reason=args.reason,
        classification=args.classification,
        argv=argv_value,
        cwd=args.cwd,
        restore_signal_state=False,
    )
    return PASS


def cmd_validate_partial_bundle(args: argparse.Namespace) -> int:
    report = validate_partial_bundle(Path(args.art_dir))
    if args.output:
        output = lexical_absolute(Path(args.output))
        art_dir = lexical_absolute(Path(args.art_dir))
        try:
            output.relative_to(art_dir)
        except ValueError:
            pass
        else:
            raise EvidenceError(
                "partial validation output cannot mutate the published bundle"
            )
        require_within(
            Path(args.output),
            Path(args.artifact_root),
            label="partial bundle validation",
        )
        write_new(Path(args.output), canonical_json(report))
    else:
        sys.stdout.buffer.write(canonical_json(report))
    return PASS


def cmd_adopt_bundle(args: argparse.Namespace) -> int:
    report = adopt_bundle(
        Path(args.art_dir),
        Path(args.manifest),
        Path(args.digest),
        Path(args.commit),
    )
    if args.output:
        output = lexical_absolute(Path(args.output))
        art_dir = lexical_absolute(Path(args.art_dir))
        try:
            output.relative_to(art_dir)
        except ValueError:
            pass
        else:
            raise EvidenceError(
                "bundle adoption output cannot mutate the committed bundle"
            )
        require_within(
            Path(args.output), Path(args.artifact_root), label="bundle adoption"
        )
        write_new(Path(args.output), canonical_json(report))
    else:
        sys.stdout.buffer.write(canonical_json(report))
    return PASS


def read_json_object(path: Path) -> dict[str, Any]:
    data, _size, _digest = stable_file_facts(path, max_bytes=MAX_LOG_BYTES)
    value = parse_json(data, subject=str(path))
    if not isinstance(value, dict):
        raise EvidenceError(f"expected JSON object: {path}")
    return value


def require(condition: bool, detail: str) -> None:
    if not condition:
        raise EvidenceError(detail)


def cmd_self_test(args: argparse.Namespace) -> int:
    """Exercise supervisor boundary cases without mocks or disposable fixtures."""
    art_dir = lexical_absolute(Path(args.art_dir))
    if art_dir.exists() or art_dir.is_symlink():
        raise EvidenceError(f"self-test artifact directory already exists: {art_dir}")
    _created, created_fd = open_directory_nofollow(art_dir, create=True)
    os.close(created_fd)
    # Nested-supervision determinism (bead fln-evidence-runner-bootstrap-btk):
    # when the self-test itself runs as a supervised stage, the runner's
    # supervisor above us is a child subreaper, so orphans of our probe trees
    # would be adopted there and never promptly reaped — hanging every
    # "descendant reaped" assertion. The self-test owns every process tree it
    # spawns; becoming the subreaper for its own domain makes orphan adoption
    # and `reap_adopted_children` deterministic on every topology (standalone,
    # nested stage, CI). The process exits at the end of the command, so no
    # restore is needed.
    enable_child_subreaper()
    # Launcher-independence for the signal-boundary campaign: a detached
    # launcher (nohup, shell background jobs) hands this process SIG_IGN
    # dispositions for HUP/INT, every probe shell inherits them, and POSIX
    # forbids a non-interactive shell from trapping a signal that was ignored
    # at entry — the finalizer probes would then never observe their signals.
    # The self-test owns its probe domain, so it pins the watched dispositions
    # to default before spawning anything.
    for owned_signal in (signal.SIGHUP, signal.SIGINT, signal.SIGTERM):
        signal.signal(owned_signal, signal.SIG_DFL)
    cases: list[dict[str, Any]] = []
    require(
        GUARDIAN_LAUNCH_RELEASE_TIMEOUT_MS > MAX_PROCESS_IDENTITY_WAIT_MS * 3,
        "guardian launch window does not cover bind plus release retry budgets",
    )

    def case_dir(name: str) -> Path:
        path = art_dir / name
        path.mkdir()
        return path

    # A supervisor may begin only when it owns no other child lifetime. Recreate
    # the Git 2.54 auto-maintenance topology directly: a launcher forks a
    # detached worker, the launcher exits, and this subreaper adopts the exited
    # worker. The guard must reject that unreaped child instead of silently
    # broadening its authority; only the fixture then reaps the exact child.
    detached_root = case_dir("preexisting_detached_child_refusal")
    detached_program = (
        "import os,sys\n"
        "child = os.fork()\n"
        "if child == 0:\n"
        "    os.setsid()\n"
        "    os._exit(0)\n"
        "sys.stdout.write(str(child))\n"
        "sys.stdout.flush()\n"
    )
    try:
        detached_launcher = subprocess.run(
            [sys.executable, "-c", detached_program],
            cwd=art_dir,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=5,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        raise EvidenceError("detached-child launcher timed out") from error
    require(
        detached_launcher.returncode == 0,
        "detached-child launcher failed: "
        f"{detached_launcher.stderr[-300:]!r}",
    )
    try:
        detached_pid = int(detached_launcher.stdout.decode("ascii"))
    except (UnicodeDecodeError, ValueError) as error:
        raise EvidenceError(
            "detached-child launcher returned a malformed PID"
        ) from error
    detached_deadline = time.monotonic() + 1.0
    detached_facts: tuple[str, int, int] | None = None
    detached_children: set[int] = set()
    while time.monotonic() < detached_deadline:
        detached_children = proc_children(os.getpid())
        if detached_pid in detached_children:
            detached_facts = proc_stat_facts(detached_pid)
            if detached_facts is not None and detached_facts[0] == "Z":
                break
        time.sleep(0.005)
    require(
        detached_facts is not None
        and detached_facts[0] == "Z"
        and detached_children == {detached_pid},
        "detached-child topology did not produce an adopted zombie",
    )
    try:
        run_supervised(
            argv=[sys.executable, "-c", "raise SystemExit('guard bypassed')"],
            cwd=art_dir,
            metadata_path=detached_root / "stage.meta.json",
            stdout_path=detached_root / "stage.out",
            stderr_path=detached_root / "stage.err",
            readiness_path=detached_root / "stage.ready.json",
            artifact_root=art_dir,
            capture_bytes=4096,
            output_budget_bytes=262_144,
            timeout_ms=1000,
            grace_ms=500,
            stage_id="preexisting_detached_child_refusal",
            planted=True,
            setup_timeout_ms=1000,
        )
    except EvidenceError as error:
        require(
            "supervisor process already owns unrelated child lifetimes" in str(error)
            and str(detached_pid) in str(error),
            f"detached-child topology failed for the wrong reason: {error}",
        )
    else:
        raise EvidenceError("supervisor accepted an unrelated adopted child")
    finally:
        reap_adopted_children()
    require(
        proc_stat_facts(detached_pid) is None,
        "detached-child refusal fixture did not reap its adopted zombie",
    )
    cases.append(
        {
            "case": "preexisting_detached_child_refusal",
            "ok": True,
            "observed_state": "adopted_zombie",
            "guard": "typed_refusal",
        }
    )

    # The verification registry is a closed schema with a frozen adoption
    # boundary. Exercise both the real transition law and discriminating
    # authority mutants before any repository stage can rely on it.
    verification_root = case_dir("verification-manifest")
    verification_beads = [
        {"id": "baseline-closed", "status": "closed"},
        {"id": "rur", "status": "in_progress"},
        {"id": "rur-consumer", "status": "in_progress"},
    ]
    verification_ids = sorted(record["id"] for record in verification_beads)
    verification_header = {
        "schema": VERIFICATION_MANIFEST_SCHEMA,
        "kind": "adoption",
        "source": ".beads/issues.jsonl",
        "projection": "sorted-canonical-bead-ids-v1",
        "hash_algorithm": "sha256",
        "hash_preimage": (
            "fln.verification-manifest.adoption.ids/1+nul+"
            "u64le-length-prefixed-utf8"
        ),
        "record_count": len(verification_ids),
        "projection_hash": verification_adoption_hash(verification_ids),
        "adoption_ids": verification_ids,
        "adoption_open_ids": ["rur", "rur-consumer"],
    }
    verification_authority_hash = verification_adoption_authority_hash(
        verification_header["adoption_ids"],
        verification_header["adoption_open_ids"],
    )
    verification_coverage = {
        "schema": VERIFICATION_MANIFEST_SCHEMA,
        "kind": "coverage",
        "bead": "rur",
        "owner": "fixture",
        "workstream": "W1",
        "claim_type": "invariant",
        "evidence_kind": "no_mock_e2e",
        "mock_only": False,
        "skip": "none",
        "requirement_ids": ["REQ-QUALITY-GATE"],
        "claim_ids": ["CLAIM-QUALITY-GATE"],
        "invariant_ids": ["FL-INV-07"],
        "parity_rows": ["not_applicable_fixture"],
        "behavior_notes": [],
        "gate_ids": ["G0"],
        "unit": ["unit:happy"],
        "boundary": ["unit:boundary"],
        "error": ["unit:error"],
        "resource": ["unit:resource"],
        "cancellation": ["unit:cancellation"],
        "failure_atomicity": ["unit:failure-atomicity"],
        "property": [],
        "metamorphic": [],
        "fuzz": [],
        "mutation": ["mutation:missing-stage"],
        "fault": ["fault:cancellation"],
        "scenarios": ["quality_gate"],
        "negative_recovery": ["quality_gate:failure-recovery"],
        "artifacts": ["human.log", "run.ndjson"],
    }
    verification_shared_coverage = dict(verification_coverage)
    verification_shared_coverage.update(
        bead="rur-consumer",
        owner="consumer-fixture",
        requirement_ids=["REQ-SHARED-QUALITY-GATE"],
        claim_ids=["CLAIM-SHARED-QUALITY-GATE"],
    )
    verification_scenario = {
        "schema": VERIFICATION_MANIFEST_SCHEMA,
        "kind": "scenario",
        "scenario": "quality_gate",
        "owner": "rur",
        "activation": "active",
        "claim_type": "invariant",
        "evidence_kind": "no_mock_e2e",
        "gate_ids": ["G0"],
        "ci_required": True,
        "ci_root": "check/quality-gate",
        "artifact_kind": "direct",
        "artifact_name": "-",
    }
    verification_records = [
        verification_header,
        verification_coverage,
        verification_shared_coverage,
        verification_scenario,
    ]

    def clone_records(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
        return parse_json(
            json.dumps(records), subject="verification manifest self-test clone"
        )

    def write_verification_case(
        name: str,
        records: list[dict[str, Any]],
        beads: list[dict[str, Any]] | None = None,
    ) -> tuple[Path, Path]:
        root = verification_root / name
        root.mkdir()
        manifest = root / "manifest.jsonl"
        tracker = root / "issues.jsonl"
        write_new(
            manifest,
            b"".join(canonical_json(record) for record in records),
        )
        write_new(
            tracker,
            b"".join(
                canonical_json(record)
                for record in (verification_beads if beads is None else beads)
            ),
        )
        return manifest, tracker

    positive_manifest, positive_beads = write_verification_case(
        "positive", clone_records(verification_records)
    )
    positive_report = validate_verification_manifest(
        positive_manifest,
        positive_beads,
        expected_adoption_authority_hash=verification_authority_hash,
    )
    require(
        positive_report["coverage_rows"] == 2
        and positive_report["scenario_rows"] == 1
        and positive_report["ci_scenarios"] == ["quality_gate"],
        "verification manifest shared scenario lost its authority rows",
    )
    require(
        positive_report["coverage_state_source"] == ".beads/issues.jsonl"
        and positive_report["derived_state_counts"]["active"] == 2,
        "verification manifest did not derive active lifecycle from the tracker",
    )

    # The exact same human-authored judgment row remains valid when its bead
    # closes: lifecycle is projected from the tracker, never edited into the
    # manifest. This is the regression that killed three full-gate attempts
    # before fln.verification-manifest/2.
    closed_beads = clone_records(verification_beads)
    closed_beads[1]["status"] = "closed"
    derived_closed_manifest, derived_closed_tracker = write_verification_case(
        "derived-closed-lifecycle",
        clone_records(verification_records),
        closed_beads,
    )
    derived_closed_report = validate_verification_manifest(
        derived_closed_manifest,
        derived_closed_tracker,
        expected_adoption_authority_hash=verification_authority_hash,
    )
    require(
        derived_closed_report["derived_state_counts"]["complete"] == 1
        and derived_closed_report["derived_state_counts"]["active"] == 1,
        "verification manifest did not derive closure from the tracker",
    )
    verification_mutants = 0

    def reject_verification_case(
        name: str,
        mutate: Callable[
            [list[dict[str, Any]], list[dict[str, Any]]], None
        ],
    ) -> None:
        nonlocal verification_mutants
        records = clone_records(verification_records)
        beads = clone_records(verification_beads)
        mutate(records, beads)
        manifest, tracker = write_verification_case(name, records, beads)
        try:
            validate_verification_manifest(
                manifest,
                tracker,
                expected_adoption_authority_hash=verification_authority_hash,
            )
        except EvidenceError:
            verification_mutants += 1
        else:
            raise EvidenceError(
                f"verification manifest mutant survived: {name}"
            )

    reject_verification_case(
        "absent-coverage",
        lambda records, _beads: records.pop(1),
    )
    reject_verification_case(
        "mock-only-invariant",
        lambda records, _beads: records[1].update(
            evidence_kind="mock", mock_only=True
        ),
    )
    reject_verification_case(
        "fuzz-closes-invariant",
        lambda records, _beads: records[1].update(evidence_kind="fuzz"),
    )
    reject_verification_case(
        "unclassified-skip",
        lambda records, _beads: records[1].update(skip="silent"),
    )
    reject_verification_case(
        "planned-counted-passed",
        lambda records, _beads: records[-1].update(activation="planned"),
    )
    reject_verification_case(
        "mock-scenario-closes-invariant",
        lambda records, _beads: records[-1].update(evidence_kind="mock"),
    )
    reject_verification_case(
        "active-scenario-not-ci-enforced",
        lambda records, _beads: records[-1].update(
            ci_required=False,
            ci_root="-",
            artifact_kind="none",
            artifact_name="-",
        ),
    )
    reject_verification_case(
        "orphan-scenario",
        lambda records, _beads: records[-1].update(owner="missing-owner"),
    )
    reject_verification_case(
        "extra-field",
        lambda records, _beads: records[1].update(extra="unreviewed"),
    )
    reject_verification_case(
        "stale-adoption-hash",
        lambda records, _beads: records[0].update(
            projection_hash=f"sha256:{'0' * 64}"
        ),
    )
    reject_verification_case(
        "new-bead-without-row",
        lambda _records, beads: beads.append(
            {"id": "new-unregistered", "status": "open"}
        ),
    )

    def expand_adoption_boundary(
        records: list[dict[str, Any]], beads: list[dict[str, Any]]
    ) -> None:
        beads.append({"id": "new-grandfathered", "status": "open"})
        adopted = sorted([*records[0]["adoption_ids"], "new-grandfathered"])
        adopted_open = sorted(
            [*records[0]["adoption_open_ids"], "new-grandfathered"]
        )
        records[0].update(
            adoption_ids=adopted,
            adoption_open_ids=adopted_open,
            record_count=len(adopted),
            projection_hash=verification_adoption_hash(adopted),
        )

    reject_verification_case(
        "dynamic-unbounded-adoption",
        expand_adoption_boundary,
    )
    def close_without_complete_judgment(
        records: list[dict[str, Any]], beads: list[dict[str, Any]]
    ) -> None:
        beads[1]["status"] = "closed"
        records[1]["unit"] = []

    reject_verification_case(
        "closed-bead-without-complete-judgment",
        close_without_complete_judgment,
    )
    reject_verification_case(
        "hand-maintained-lifecycle-field",
        lambda records, _beads: records[1].update(state="active"),
    )
    reject_verification_case(
        "duplicate-row",
        lambda records, _beads: records.insert(2, dict(records[1])),
    )

    duplicate_root = verification_root / "duplicate-key"
    duplicate_root.mkdir()
    duplicate_manifest = duplicate_root / "manifest.jsonl"
    duplicate_tracker = duplicate_root / "issues.jsonl"
    duplicate_coverage = canonical_json(verification_coverage).rstrip(b"\n")
    write_new(
        duplicate_manifest,
        canonical_json(verification_header)
        + duplicate_coverage[:-1]
        + b',"owner":"duplicate-owner"}\n'
        + canonical_json(verification_scenario),
    )
    write_new(
        duplicate_tracker,
        b"".join(canonical_json(record) for record in verification_beads),
    )
    try:
        validate_verification_manifest(
            duplicate_manifest,
            duplicate_tracker,
            expected_adoption_authority_hash=verification_authority_hash,
        )
    except EvidenceError:
        verification_mutants += 1
    else:
        raise EvidenceError("duplicate manifest key was accepted")

    truncated_root = verification_root / "truncated"
    truncated_root.mkdir()
    truncated_manifest = truncated_root / "manifest.jsonl"
    truncated_tracker = truncated_root / "issues.jsonl"
    write_new(
        truncated_manifest,
        b"".join(canonical_json(record) for record in verification_records)[:-1],
    )
    write_new(
        truncated_tracker,
        b"".join(canonical_json(record) for record in verification_beads),
    )
    try:
        validate_verification_manifest(
            truncated_manifest,
            truncated_tracker,
            expected_adoption_authority_hash=verification_authority_hash,
        )
    except EvidenceError:
        verification_mutants += 1
    else:
        raise EvidenceError("truncated verification manifest was accepted")
    require(
        verification_mutants == 17,
        "verification manifest mutation matrix is incomplete",
    )
    cases.append(
        {
            "case": "verification_manifest_model",
            "ok": True,
            "mutants_killed": verification_mutants,
        }
    )
    cases.extend(
        (
            {
                "case": "claim_evidence_authority",
                "ok": True,
                "mutants_killed": 3,
            },
            {
                "case": "scenario_activation_registry",
                "ok": True,
                "mutants_killed": 3,
            },
        )
    )

    # A changed-scope inventory is frozen at run start. Git index/commit
    # transitions can change the live "changed" set without changing any
    # captured bytes, especially in the shared-tree swarm. Those transitions
    # must not break terminal publication; actual byte drift remains fatal.
    ubs_scope_root = case_dir("ubs_inventory_scope_snapshot")
    ubs_scope_repo = ubs_scope_root / "repo"
    ubs_scope_repo.mkdir()
    git_init = subprocess.run(
        ["git", "init", "-q", str(ubs_scope_repo)],
        cwd=ubs_scope_root,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    require(
        git_init.returncode == 0,
        f"UBS scope fixture git init failed: {git_init.stderr[-300:]!r}",
    )
    maintenance_auto = run_git(
        ubs_scope_repo,
        ["config", "--bool", "--get", "maintenance.auto"],
        subject="UBS scope fixture sealed maintenance policy",
    ).decode("ascii").strip()
    require(
        maintenance_auto == "false",
        "evidence Git invocation did not disable automatic maintenance",
    )
    require(
        not proc_children(os.getpid()),
        "sealed Git policy query left an adopted maintenance child",
    )
    tracked_input = ubs_scope_repo / "tracked.py"
    stable_input = ubs_scope_repo / "stable.py"
    write_new(tracked_input, b"value = 1\n")
    write_new(stable_input, b"stable = True\n")
    run_git(
        ubs_scope_repo,
        ["add", "tracked.py", "stable.py"],
        subject="UBS scope fixture initial add",
    )
    run_git(
        ubs_scope_repo,
        [
            "-c",
            "user.name=FrankenLean Tribunal",
            "-c",
            "user.email=tribunal@invalid",
            "commit",
            "-q",
            "-m",
            "initial",
        ],
        subject="UBS scope fixture initial commit",
    )
    require(
        not proc_children(os.getpid()),
        "sealed Git initial commit left an adopted maintenance child",
    )
    with tracked_input.open("ab") as handle:
        handle.write(b"# captured change\n")
        handle.flush()
        os.fsync(handle.fileno())
    captured_inventory = collect_ubs_inventory(ubs_scope_repo, "changed")
    require(
        [row["path"] for row in captured_inventory["files"]] == ["tracked.py"],
        "UBS scope fixture did not capture the intended changed file",
    )
    captured_inventory_path = ubs_scope_root / "ubs-inventory.json"
    write_new(captured_inventory_path, canonical_json(captured_inventory))
    validate_ubs_inventory(
        captured_inventory_path,
        ubs_scope_repo,
        require_live_scope=True,
    )
    captured_root = tree_hash(
        ubs_scope_repo,
        ["tracked.py", "stable.py"],
        inventory_path=captured_inventory_path,
    )
    run_git(
        ubs_scope_repo,
        ["add", "tracked.py"],
        subject="UBS scope fixture transition add",
    )
    run_git(
        ubs_scope_repo,
        [
            "-c",
            "user.name=FrankenLean Tribunal",
            "-c",
            "user.email=tribunal@invalid",
            "commit",
            "-q",
            "-m",
            "scope transition",
        ],
        subject="UBS scope fixture transition commit",
    )
    require(
        not proc_children(os.getpid()),
        "sealed Git transition commit left an adopted maintenance child",
    )
    try:
        validate_ubs_inventory(
            captured_inventory_path,
            ubs_scope_repo,
            require_live_scope=True,
        )
    except EvidenceError as error:
        require(
            "declared live repository scope" in str(error),
            f"UBS live-scope transition failed for the wrong reason: {error}",
        )
    else:
        raise EvidenceError("UBS strict live-scope transition was not detected")
    validate_ubs_inventory(captured_inventory_path, ubs_scope_repo)
    transitioned_root = tree_hash(
        ubs_scope_repo,
        ["tracked.py", "stable.py"],
        inventory_path=captured_inventory_path,
    )
    require(
        transitioned_root == captured_root,
        "Git-only UBS scope transition changed the immutable input root",
    )
    with stable_input.open("ab") as handle:
        handle.write(b"# governed byte drift\n")
        handle.flush()
        os.fsync(handle.fileno())
    drifted_root = tree_hash(
        ubs_scope_repo,
        ["tracked.py", "stable.py"],
        inventory_path=captured_inventory_path,
    )
    require(
        drifted_root != captured_root,
        "governed byte drift did not change the immutable input root",
    )
    with tracked_input.open("ab") as handle:
        handle.write(b"# captured byte drift\n")
        handle.flush()
        os.fsync(handle.fileno())
    try:
        validate_ubs_inventory(captured_inventory_path, ubs_scope_repo)
    except EvidenceError as error:
        require(
            "UBS inventory input changed: tracked.py" in str(error),
            f"UBS captured-byte drift failed for the wrong reason: {error}",
        )
    else:
        raise EvidenceError("UBS captured-byte drift was accepted")
    cases.append(
        {
            "case": "ubs_inventory_scope_snapshot",
            "ok": True,
            "mutants_killed": 2,
        }
    )
    cases.append(
        {
            "case": "git_maintenance_subreaper_boundary",
            "ok": True,
            "maintenance_auto": maintenance_auto,
            "owned_children_after_commits": [],
        }
    )

    # The structure guard's robot stream is a versioned evidence contract, not a
    # best-effort JSON bag. Exercise one complete /3 stream and discriminating
    # mutations here so the validator cannot silently stop checking newly authoritative
    # fields while the E2E lanes continue to look green.
    guard_root = case_dir("structure-guard-contract")
    guard_start = {
        "schema": "structure-guard/3",
        "event": "run_start",
        "root": str(guard_root),
        "root_identity": str(guard_root.resolve(strict=True)),
        "graph_digest": "fnv1a64:0123456789abcdef",
        "crates": 1,
        "edges": 0,
        "authority_inventory": {
            "package_class": "workspace-graph-exact",
            "packages": 1,
            "target_class": "cargo-auto-discovery-closed",
            "targets": 1,
            "feature_class": "manifest-enumerated",
            "features": 0,
            "target_triple_class": "suite-lock-declared",
            "target_triples": 1,
        },
        "effective_compiler_identity": {
            "source": "PATH",
            "channel": "nightly-2026-07-13",
            "release": "1.99.0-nightly",
            "commit": "77cf889bc178ddb44d6a1c78e5a820b5abb31d8d",
            "host": "x86_64-unknown-linux-gnu",
            "contract_declared": True,
            "configuration_match": True,
            "contract_match": True,
        },
        "admitted_environment": {
            "policy": "names-only-no-values/1",
            "admitted_names": ["HOME", "PATH"],
            "compiler_override_names": [],
        },
    }
    guard_end = {
        "schema": "structure-guard/3",
        "event": "run_end",
        "verdict": "pass",
        "exit_code": 0,
        "findings": 0,
        "authority": "complete",
        "contract_handoff_root": "fnv1a64:0123456789abcdef",
        "traversal": {
            "directories_visited": 3,
            "files_discovered": 4,
            "files_scanned": 4,
            "files_skipped_unreadable": 0,
        },
        "authority_count_rule": (
            "files_scanned+files_skipped_unreadable=files_discovered"
        ),
        "authority_count_rule_holds": True,
        "governed_root_before": "fnv1a64:fedcba9876543210",
        "governed_root_after": "fnv1a64:fedcba9876543210",
        "governed_root_unchanged": True,
        "duration_ms": 1,
    }

    def write_guard_stream(
        name: str, mutate: Callable[[list[dict[str, Any]]], None] | None = None
    ) -> Path:
        records = json.loads(json.dumps([guard_start, guard_end]))
        if mutate is not None:
            mutate(records)
        stream = guard_root / f"{name}.ndjson"
        write_new(stream, b"".join(canonical_json(record) for record in records))
        return stream

    guard_valid = write_guard_stream("valid")
    validate_guard(guard_valid, PASS, "pass", [], str(guard_root), PASS)

    def old_guard_schema(records: list[dict[str, Any]]) -> None:
        for record in records:
            record["schema"] = "structure-guard/2"

    def missing_guard_field(records: list[dict[str, Any]]) -> None:
        records[0].pop("root_identity")

    def extra_guard_field(records: list[dict[str, Any]]) -> None:
        records[1]["unversioned_claim"] = True

    def missing_guard_handoff_root(records: list[dict[str, Any]]) -> None:
        records[1]["contract_handoff_root"] = None

    def malformed_guard_handoff_root(records: list[dict[str, Any]]) -> None:
        records[1]["contract_handoff_root"] = "fnv1a64:not-a-root"

    def broken_guard_conservation(records: list[dict[str, Any]]) -> None:
        records[1]["traversal"]["files_scanned"] = 3

    def false_guard_root_equality(records: list[dict[str, Any]]) -> None:
        records[1]["governed_root_after"] = "fnv1a64:1111111111111111"

    def unbound_guard_compiler(records: list[dict[str, Any]]) -> None:
        records[0]["effective_compiler_identity"]["configuration_match"] = False

    def leaked_guard_environment_value(records: list[dict[str, Any]]) -> None:
        records[0]["admitted_environment"]["admitted_names"] = ["/secret/path"]

    guard_mutants = [
        ("old-schema", old_guard_schema),
        ("missing-field", missing_guard_field),
        ("extra-field", extra_guard_field),
        ("missing-contract-handoff-root", missing_guard_handoff_root),
        ("malformed-contract-handoff-root", malformed_guard_handoff_root),
        ("broken-conservation", broken_guard_conservation),
        ("false-root-equality", false_guard_root_equality),
        ("unbound-compiler", unbound_guard_compiler),
        ("environment-value", leaked_guard_environment_value),
    ]
    for mutant_name, mutate in guard_mutants:
        mutant = write_guard_stream(mutant_name, mutate)
        try:
            validate_guard(mutant, PASS, "pass", [], str(guard_root), PASS)
        except EvidenceError:
            pass
        else:
            raise EvidenceError(f"structure-guard validator survived mutant {mutant_name}")
    cases.append(
        {
            "case": "structure_guard_v3_contract",
            "ok": True,
            "mutants_killed": [name for name, _mutate in guard_mutants],
        }
    )

    def run_case(
        name: str,
        command: Sequence[str],
        *,
        capture: int = 4096,
        budget: int = 262_144,
        setup_timeout: int = MAX_PROCESS_IDENTITY_WAIT_MS,
        timeout: int = 30_000,
        cancel_after: int | None = None,
        stdout_override: Path | None = None,
        semantic_exits: Sequence[int] = (),
        before_stop_delay: int = 0,
        before_release_delay: int = 0,
        gate_mode: str = "normal",
        fault_point: str = "none",
    ) -> tuple[int, dict[str, Any], Path]:
        injected_gate_control = (
            before_stop_delay != 0
            or before_release_delay != 0
            or gate_mode != "normal"
            or fault_point != "none"
        )
        root = case_dir(name)
        metadata = root / "stage.meta.json"
        stdout = stdout_override or root / "stage.out"
        stderr = root / "stage.err"
        readiness = root / "stage.ready.json"
        rc = run_supervised(
            argv=command,
            cwd=art_dir,
            metadata_path=metadata,
            stdout_path=stdout,
            stderr_path=stderr,
            readiness_path=readiness,
            artifact_root=art_dir,
            capture_bytes=capture,
            output_budget_bytes=budget,
            setup_timeout_ms=setup_timeout,
            timeout_ms=timeout,
            grace_ms=500,
            stage_id=name,
            planted=injected_gate_control,
            semantic_failure_exits=semantic_exits,
            cancel_after_ms=cancel_after,
            test_before_stop_delay_ms=before_stop_delay,
            test_before_release_delay_ms=before_release_delay,
            test_gate_mode=gate_mode,
            test_fault_point=fault_point,
        )
        meta = read_json_object(metadata)
        validate_supervisor_object(
            metadata,
            1,
            meta,
            expected_stage_id=name,
        )
        require(
            meta["planted"] is injected_gate_control,
            f"{name}: planted marker did not bind stopped-gate controls",
        )
        require(
            meta["test_control"]
            == {
                "before_stop_delay_ms": before_stop_delay,
                "before_release_delay_ms": before_release_delay,
                "gate_mode": gate_mode,
                "terminal_delay_ms": 0,
                "terminal_ready_enabled": False,
                "fault_point": fault_point,
            },
            f"{name}: stopped-gate controls were not retained",
        )
        return rc, meta, root

    def run_shell_finalizer_probe(
        point: str,
        signal_number: int,
        expected_exit: int,
        *,
        expect_committed_bundle: bool,
    ) -> dict[str, Any]:
        repo = Path(__file__).resolve().parent.parent
        check_script = repo / "scripts" / "check.sh"
        probe_signal_name = signal.Signals(signal_number).name.lower()
        probe_root = art_dir / f"shell_finalizer_{point}_{probe_signal_name}"
        control_root = Path(f"{probe_root}.control")
        # The three post-terminal points run the real finalization pipeline
        # before their checkpoint; the entry points die at the first finalizer.
        deep_pipeline = point in {"decision_write", "marker_link", "post_decision"}
        require(
            not probe_root.exists()
            and not probe_root.is_symlink()
            and not control_root.exists()
            and not control_root.is_symlink(),
            f"finalizer probe paths already exist: {point}",
        )
        probe_environment = {
            key: value
            for key, value in os.environ.items()
            if not key.startswith("FLN_CHECK_")
            and not key.startswith("FLN_FINALIZER_")
        }
        probe_environment.update(
            {
                "FLN_CHECK_ART_DIR": str(probe_root),
                "FLN_FINALIZER_TEST_POINT": point,
            }
        )
        child = subprocess.Popen(
            ["bash", str(check_script), "--finalizer-probe"],
            cwd=repo,
            env=probe_environment,
            start_new_session=True,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        child_handle: tuple[int, int] | None = None
        finalizer_handle: tuple[int, int] | None = None
        finalizer_pid = 0
        try:
            deadline = time.monotonic() + 5.0
            while time.monotonic() < deadline:
                child_handle = open_process_handle(
                    child.pid, expected_parent_pid=os.getpid()
                )
                child_facts = proc_stat_facts(child.pid)
                if (
                    child_handle is not None
                    and child_facts is not None
                    and child_facts[1] == child.pid
                    and child_facts[2] == child_handle[0]
                ):
                    break
                if child_handle is not None:
                    os.close(child_handle[1])
                    child_handle = None
                time.sleep(0.005)
            else:
                raise EvidenceError(f"finalizer probe shell was not bindable: {point}")

            ready_path = control_root / "ready"
            ready_timeout_s = 180.0 if deep_pipeline else 60.0
            deadline = time.monotonic() + ready_timeout_s
            ready_values: tuple[int, int] | None = None
            while time.monotonic() < deadline:
                if child.poll() is not None:
                    raise EvidenceError(
                        f"finalizer probe exited before readiness: {point}={child.returncode}"
                    )
                try:
                    payload, _size, _digest = stable_file_facts(
                        ready_path, max_bytes=128
                    )
                    values = tuple(
                        int(value) for value in payload.decode("ascii").split()
                    )
                    if len(values) == 2:
                        ready_values = (values[0], values[1])
                        break
                except (EvidenceError, FileNotFoundError, UnicodeError, ValueError):
                    pass
                time.sleep(0.005)
            if ready_values is None:
                raise EvidenceError(f"finalizer probe readiness timed out: {point}")
            finalizer_pid, finalizer_ticks = ready_values
            if deep_pipeline:
                require(
                    ready_values == (0, 0),
                    f"{point} probe unexpectedly retained an active finalizer",
                )
            else:
                require(finalizer_pid > 1, f"invalid finalizer probe PID: {point}")
                deadline = time.monotonic() + 5.0
                while time.monotonic() < deadline:
                    finalizer_handle = open_process_handle(
                        finalizer_pid, expected_parent_pid=child.pid
                    )
                    finalizer_facts = proc_stat_facts(finalizer_pid)
                    if (
                        finalizer_handle is not None
                        and finalizer_facts is not None
                        and finalizer_facts[1] == finalizer_pid
                        and finalizer_facts[2] == finalizer_handle[0]
                        and (
                            (
                                point == "spawn_bind"
                                and finalizer_ticks == 0
                                and finalizer_facts[0] in {"T", "t"}
                            )
                            or (
                                point != "spawn_bind"
                                and finalizer_ticks > 0
                                and finalizer_handle[0] == finalizer_ticks
                                and finalizer_facts[0] not in {"T", "t", "Z"}
                            )
                        )
                    ):
                        break
                    if finalizer_handle is not None:
                        os.close(finalizer_handle[1])
                        finalizer_handle = None
                    time.sleep(0.005)
                else:
                    raise EvidenceError(
                        f"finalizer probe child was not precisely bound: {point}"
                    )

            require(
                signal_process_handle(child.pid, child_handle, signal_number),
                f"finalizer probe shell disappeared before signal: {point}",
            )
            if point in {"post_decision", "marker_link"}:
                # The decision has already been linked, so the signal must lose:
                # the shell acknowledges it and the committed bundle survives.
                ack_path = control_root / "signal-ack"
                expected_ack = signal.Signals(signal_number).name.removeprefix(
                    "SIG"
                ).encode("ascii")
                deadline = time.monotonic() + 60.0
                while time.monotonic() < deadline:
                    try:
                        ack, _size, _digest = stable_file_facts(
                            ack_path, max_bytes=32
                        )
                    except (EvidenceError, FileNotFoundError):
                        time.sleep(0.005)
                        continue
                    if hmac.compare_digest(ack.strip(), expected_ack):
                        break
                    time.sleep(0.005)
                else:
                    raise EvidenceError(
                        f"{point} signal was not acknowledged correctly"
                    )
                write_new(control_root / "release", b"release\n")

            communicate_timeout_s = 180 if deep_pipeline else 120
            _stdout, stderr = child.communicate(timeout=communicate_timeout_s)
            require(
                child.returncode == expected_exit,
                f"finalizer probe {point} exited {child.returncode}: {stderr[-1000:]!r}",
            )
            if not expect_committed_bundle:
                decision, _size, _digest = stable_file_facts(
                    probe_root / "bundle.decision", max_bytes=1
                )
                require(
                    decision == b"",
                    f"pre-decision finalizer probe crossed its decision: {point}",
                )
            if point in {"spawn_bind", "active_wait", "decision_write"}:
                require(
                    b"CANCELLED: signal_" in stderr,
                    f"finalizer cancellation lacked its terminal reason: {point}",
                )
            if point == "helper_failure":
                require(
                    b"process-tree cleanup was not proven" in stderr,
                    "helper-failure probe did not exercise cleanup uncertainty",
                )
            if finalizer_handle is not None:
                deadline = time.monotonic() + 5.0
                while True:
                    reap_adopted_children()
                    finalizer_facts = proc_stat_facts(finalizer_pid)
                    if (
                        finalizer_facts is None
                        or finalizer_facts[2] != finalizer_handle[0]
                    ):
                        break
                    if time.monotonic() >= deadline:
                        break
                    time.sleep(0.005)
                require(
                    (finalizer_facts := proc_stat_facts(finalizer_pid)) is None
                    or finalizer_facts[2] != finalizer_handle[0],
                    f"finalizer probe left its bound lifetime unreaped: {point}",
                )
            commit_path = probe_root / "bundle.complete.json"
            if expect_committed_bundle:
                validate_run(
                    probe_root / "run.ndjson",
                    "fln.check/2",
                    "pass",
                    live_context=False,
                )
                validate_bundle(
                    probe_root,
                    probe_root / "manifest.json",
                    probe_root / "manifest.digest",
                    commit_path,
                )
            else:
                require(
                    not commit_path.exists(),
                    f"pre-decision finalizer probe committed a bundle: {point}",
                )
        finally:
            if child.poll() is None:
                if child_handle is not None:
                    signal_process_handle(child.pid, child_handle, signal.SIGKILL)
                else:
                    child.kill()
                child.communicate(timeout=10)
            if finalizer_handle is not None:
                try:
                    if process_handle_alive(finalizer_pid, finalizer_handle):
                        signal_process_handle(
                            finalizer_pid, finalizer_handle, signal.SIGKILL
                        )
                finally:
                    os.close(finalizer_handle[1])
            if child_handle is not None:
                os.close(child_handle[1])
            reap_adopted_children()
        return {
            "case": f"shell_finalizer_{point}_{probe_signal_name}",
            "ok": True,
            "signal": signal.Signals(signal_number).name,
            "process_exit": expected_exit,
            "artifact": str(probe_root),
        }

    flood_size = 32_768
    flood_program = (
        "import sys;"
        f"sys.stdout.buffer.write(b'A'*{flood_size}+b'OUT_TAIL');"
        f"sys.stderr.buffer.write(b'B'*{flood_size}+b'ERR_TAIL')"
    )
    rc, meta, root = run_case(
        "large_output_pass",
        [sys.executable, "-c", flood_program, "--token=supersecret"],
        capture=4096,
        budget=262_144,
    )
    require(
        rc == PASS and meta["classification"] == "pass", "large output changed exit"
    )
    require(
        meta["stdout"]["truncated"] and meta["stderr"]["truncated"],
        "flood not truncated",
    )
    out_data, out_size, _out_digest = stable_file_facts(root / "stage.out")
    err_data, err_size, _err_digest = stable_file_facts(root / "stage.err")
    require(out_size <= 4096, "stdout capture exceeded bound")
    require(err_size <= 4096, "stderr capture exceeded bound")
    require(out_data.endswith(b"OUT_TAIL"), "stdout tail lost")
    require(err_data.endswith(b"ERR_TAIL"), "stderr tail lost")
    serialized = canonical_json(meta)
    require(
        b"supersecret" not in serialized and b"<redacted>" in serialized,
        "secret leaked",
    )
    cases.append(
        {
            "case": "large_output_pass",
            "ok": True,
            "metadata": str(root / "stage.meta.json"),
        }
    )

    rc, meta, root = run_case(
        "semantic_failure",
        [sys.executable, "-c", "raise SystemExit(7)"],
        semantic_exits=[7],
    )
    require(
        rc == FAIL and meta["classification"] == "fail",
        "semantic exit was not a failure",
    )
    require(meta["child_exit"] == 7, "semantic child exit was not retained")
    cases.append(
        {
            "case": "semantic_failure",
            "ok": True,
            "metadata": str(root / "stage.meta.json"),
        }
    )

    rc, meta, root = run_case(
        "unexpected_child_exit",
        [sys.executable, "-c", "raise SystemExit(7)"],
    )
    require(
        rc == SETUP_FAILURE and meta["classification"] == "internal_fault",
        "unexpected child exit was mislabeled semantic",
    )
    cases.append(
        {
            "case": "unexpected_child_exit",
            "ok": True,
            "metadata": str(root / "stage.meta.json"),
        }
    )

    rc, meta, root = run_case(
        "unexpected_child_signal",
        [sys.executable, "-c", "import os,signal;os.kill(os.getpid(),signal.SIGKILL)"],
    )
    require(
        rc == INCONCLUSIVE and meta["classification"] == "inconclusive",
        "unexpected child signal was mislabeled semantic",
    )
    cases.append(
        {
            "case": "unexpected_child_signal",
            "ok": True,
            "metadata": str(root / "stage.meta.json"),
        }
    )

    endless_output = "import os; b=b'x'*65536\nwhile True: os.write(1,b); os.write(2,b)"
    rc, meta, root = run_case(
        "output_budget_exhausted",
        [sys.executable, "-c", endless_output],
        capture=4096,
        budget=8192,
        timeout=30_000,
    )
    require(rc == INCONCLUSIVE, "output exhaustion did not return inconclusive")
    require(meta["classification"] == "inconclusive", "output exhaustion misclassified")
    require(
        meta["reason_code"] == "output_budget_exhausted",
        "wrong output exhaustion reason",
    )
    cases.append(
        {
            "case": "output_budget_exhausted",
            "ok": True,
            "metadata": str(root / "stage.meta.json"),
        }
    )

    rc, meta, root = run_case(
        "target_exec_failure",
        [str(art_dir / "definitely-missing-command")],
        capture=4096,
        budget=65_536,
        semantic_exits=(SETUP_FAILURE,),
    )
    require(rc == SETUP_FAILURE, "exec failure did not return internal-fault exit")
    require(
        meta["classification"] == "internal_fault"
        and meta["reason_code"] == "target_exec_failure"
        and meta["target_exec"]["status"] == "failed",
        "exec failure was not distinguished from semantic exit 2",
    )
    exec_ready = read_json_object(root / "stage.ready.json")
    require(
        exec_ready["status"] == "ready",
        "exec failure did not retain admitted same-PID readiness",
    )
    cases.append(
        {
            "case": "target_exec_failure",
            "ok": True,
            "metadata": str(root / "stage.meta.json"),
        }
    )

    rc, meta, root = run_case(
        "semantic_exit_two",
        [sys.executable, "-c", "raise SystemExit(2)"],
        semantic_exits=(SETUP_FAILURE,),
    )
    require(
        rc == FAIL
        and meta["classification"] == "fail"
        and meta["child_exit"] == SETUP_FAILURE
        and meta["target_exec"]["status"] == "succeeded",
        "real semantic exit 2 was confused with helper setup failure",
    )
    cases.append(
        {
            "case": "semantic_exit_two",
            "ok": True,
            "metadata": str(root / "stage.meta.json"),
        }
    )

    rc, meta, root = run_case(
        "delayed_stopped_admission",
        ["/usr/bin/true"],
        setup_timeout=5000,
        timeout=100,
        before_stop_delay=500,
    )
    require(
        rc == PASS
        and meta["phase_timing"]["setup_duration_ns"] > 500_000_000
        and meta["phase_timing"]["execution_duration_ns"] < 100_000_000,
        "setup delay consumed the post-release execution budget",
    )
    cases.append(
        {
            "case": "delayed_stopped_admission",
            "ok": True,
            "metadata": str(root / "stage.meta.json"),
        }
    )

    rc, meta, root = run_case(
        "never_stops",
        ["/usr/bin/true"],
        setup_timeout=100,
        timeout=5000,
        gate_mode="never_stop",
    )
    never_ready = read_json_object(root / "stage.ready.json")
    require(
        rc == INCONCLUSIVE
        and meta["reason_code"] == "setup_timeout"
        and meta["target_exec"]["status"] == "not_released"
        and never_ready["status"] == "setup_timeout"
        and meta["resource"]["surviving_pids"] == [],
        "never-stopping child did not fail closed within setup budget",
    )
    cases.append(
        {
            "case": "never_stops",
            "ok": True,
            "metadata": str(root / "stage.meta.json"),
        }
    )

    rc, meta, root = run_case(
        "exit_before_stop",
        ["/usr/bin/true"],
        setup_timeout=1000,
        gate_mode="exit_before_stop",
    )
    gate_ready = read_json_object(root / "stage.ready.json")
    require(
        rc == SETUP_FAILURE
        and meta["classification"] == "internal_fault"
        and meta["target_exec"]["status"] == "not_released"
        and gate_ready["status"] == "setup_failed",
        "pre-admission gate death was not an internal setup fault",
    )
    cases.append(
        {
            "case": "exit_before_stop",
            "ok": True,
            "metadata": str(root / "stage.meta.json"),
        }
    )

    rc, meta, root = run_case(
        "stop_then_die",
        ["/usr/bin/true"],
        setup_timeout=1000,
        gate_mode="die_after_stop",
    )
    require(
        rc == INCONCLUSIVE
        and meta["reason_code"] == "child_signal_SIGKILL"
        and meta["target_exec"]["status"] == "unknown"
        and meta["resource"]["surviving_pids"] == [],
        "post-release pre-exec death was promoted to a target verdict",
    )
    cases.append(
        {
            "case": "stop_then_die",
            "ok": True,
            "metadata": str(root / "stage.meta.json"),
        }
    )

    mutation_source = meta
    mutation_path = root / "stage.meta.json"

    def reject_supervisor_mutation(
        label: str, mutate: Callable[[dict[str, Any]], None]
    ) -> None:
        candidate = parse_json(
            canonical_json(mutation_source),
            subject=f"supervisor mutation {label}",
        )
        if not isinstance(candidate, dict):
            raise EvidenceError("supervisor mutation source is not an object")
        mutate(candidate)
        try:
            validate_supervisor_object(
                mutation_path,
                1,
                candidate,
                expected_stage_id="stop_then_die",
            )
        except EvidenceError:
            return
        raise EvidenceError(f"supervisor validator accepted mutation: {label}")

    reject_supervisor_mutation(
        "setup_duration",
        lambda candidate: candidate["phase_timing"].__setitem__(
            "setup_duration_ns",
            candidate["phase_timing"]["setup_duration_ns"] + 1,
        ),
    )
    reject_supervisor_mutation(
        "session_identity",
        lambda candidate: candidate["phase_timing"].__setitem__(
            "admission_protocol", "unbound"
        ),
    )
    reject_supervisor_mutation(
        "unknown_exec_promoted",
        lambda candidate: (
            candidate.__setitem__("classification", "pass"),
            candidate.__setitem__("reason_code", "exit_zero"),
            candidate.__setitem__("wrapper_exit", PASS),
            candidate.__setitem__("child_exit", PASS),
            candidate.__setitem__("child_signal", None),
        ),
    )
    cases.append(
        {
            "case": "supervisor_v2_mutation_rejection",
            "ok": True,
            "mutants": 3,
        }
    )

    pid_file = art_dir / "timeout-pids.txt"
    tree_program = (
        "import os,pathlib,subprocess,sys,time;"
        "code='import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)';"
        "p=subprocess.Popen([sys.executable,'-c',code],start_new_session=True);"
        f"pathlib.Path({str(pid_file)!r}).write_text(str(os.getpid())+'\\n'+str(p.pid)+'\\n');"
        "time.sleep(60)"
    )
    rc, meta, root = run_case(
        "timeout",
        [sys.executable, "-c", tree_program],
        capture=4096,
        budget=65_536,
        timeout=5000,
    )
    require(
        rc == INCONCLUSIVE and meta["reason_code"] == "timeout", "timeout misclassified"
    )
    pids = [int(value) for value in pid_file.read_text(encoding="utf-8").splitlines()]
    time.sleep(0.1)
    require(
        not any(process_alive(pid) for pid in pids),
        "timeout left a live process-tree member",
    )
    cases.append(
        {
            "case": "timeout",
            "ok": True,
            "metadata": str(root / "stage.meta.json"),
            "pids": pids,
        }
    )

    leader_root = case_dir("leader_exit_with_inherited_pipe")
    leader_pid_file = leader_root / "pids.txt"
    leader_program = (
        "import os,pathlib,subprocess,sys;"
        "code='import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)';"
        "p=subprocess.Popen([sys.executable,'-c',code],start_new_session=True);"
        f"pathlib.Path({str(leader_pid_file)!r}).write_text(str(os.getpid())+'\\n'+str(p.pid)+'\\n')"
    )
    rc = run_supervised(
        argv=[sys.executable, "-c", leader_program],
        cwd=art_dir,
        metadata_path=leader_root / "stage.meta.json",
        stdout_path=leader_root / "stage.out",
        stderr_path=leader_root / "stage.err",
        readiness_path=leader_root / "stage.ready.json",
        artifact_root=art_dir,
        capture_bytes=4096,
        output_budget_bytes=65_536,
        timeout_ms=5000,
        grace_ms=500,
        stage_id="leader_exit_with_inherited_pipe",
        planted=False,
    )
    leader_meta = read_json_object(leader_root / "stage.meta.json")
    require(
        rc == SETUP_FAILURE, "leader-first descendant leak was not an internal fault"
    )
    leader_pids = [
        int(value) for value in leader_pid_file.read_text(encoding="utf-8").splitlines()
    ]
    require(
        not any(process_alive(pid) for pid in leader_pids),
        "leader-first inherited-pipe descendant survived",
    )
    cases.append(
        {
            "case": "leader_exit_with_inherited_pipe",
            "ok": True,
            "metadata": str(leader_root / "stage.meta.json"),
            "pids": leader_pids,
            "classification": leader_meta["classification"],
        }
    )

    target_selection = (
        graceful_signal_targets(41, {41, 42, 43}, root_only=True),
        graceful_signal_targets(41, {42, 43}, root_only=True),
        graceful_signal_targets(41, {43, 41, 42}, root_only=False),
    )
    match target_selection:
        case ([41], [], [41, 42, 43]):
            pass
        case _:
            raise EvidenceError(
                "graceful signal target selection violated cooperative root-only routing"
            )
    cases.append({"case": "graceful_signal_target_selection", "ok": True})

    cancel_root = case_dir("cancel_term")
    cancel_pid_file = cancel_root / "pids.txt"
    cancel_child_ready = cancel_root / "child.ready"
    cancel_program = (
        "import os,pathlib,signal,subprocess,sys,time;"
        "code=\"import os,pathlib,signal,time;\""
        "\"signal.signal(signal.SIGTERM,lambda *_:os.write(1,b'CHILD\\\\n'));\""
        f"\"pathlib.Path({str(cancel_child_ready)!r}).write_text('ready');\""
        "\"time.sleep(60)\";"
        "p=subprocess.Popen([sys.executable,'-c',code],start_new_session=True);"
        f"ready=pathlib.Path({str(cancel_child_ready)!r});\n"
        "deadline=time.monotonic()+15\n"
        "while not ready.exists() and time.monotonic()<deadline:\n time.sleep(.01)\n"
        "if not ready.exists(): raise SystemExit(9)\n"
        "signal.signal(signal.SIGTERM,lambda *_:(os.write(1,b'PARENT\\n'),time.sleep(.1),os.kill(p.pid,signal.SIGTERM)));"
        f"pathlib.Path({str(cancel_pid_file)!r}).write_text(str(os.getpid())+'\\n'+str(p.pid)+'\\n');"
        "time.sleep(60)"
    )
    wrapper = subprocess.Popen(
        [
            sys.executable,
            "-I",
            "-S",
            str(Path(__file__).resolve()),
            "run",
            "--cwd",
            str(art_dir),
            "--metadata",
            str(cancel_root / "stage.meta.json"),
            "--stdout",
            str(cancel_root / "stage.out"),
            "--stderr",
            str(cancel_root / "stage.err"),
            "--readiness",
            str(cancel_root / "stage.ready.json"),
            "--artifact-root",
            str(art_dir),
            "--capture-bytes",
            "4096",
            "--output-budget-bytes",
            "65536",
            "--timeout-ms",
            "30000",
            "--grace-ms",
            "500",
            "--stage-id",
            "cancel_term",
            "--",
            sys.executable,
            "-c",
            cancel_program,
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    wait_deadline = time.monotonic() + 15
    while (
        not (cancel_pid_file.exists() and (cancel_root / "stage.ready.json").exists())
        and wrapper.poll() is None
        and time.monotonic() < wait_deadline
    ):
        time.sleep(0.02)
    require(cancel_pid_file.exists(), "cancellation child did not publish PIDs")
    require(
        (cancel_root / "stage.ready.json").exists(),
        "supervisor readiness was not published",
    )
    wrapper.send_signal(signal.SIGTERM)
    _wrapper_out, wrapper_err = wrapper.communicate(timeout=30)
    require(
        wrapper.returncode == CANCELLED,
        f"cancellation wrapper exit {wrapper.returncode}: {wrapper_err!r}",
    )
    cancel_meta = read_json_object(cancel_root / "stage.meta.json")
    require(
        cancel_meta["classification"] == "cancelled",
        "TERM was not typed as cancellation",
    )
    cancel_stdout, _cancel_size, _cancel_digest = stable_file_facts(
        cancel_root / "stage.out"
    )
    require(
        cancel_stdout.count(b"PARENT\n") == 1
        and cancel_stdout.count(b"CHILD\n") == 1,
        "cooperative cancellation was not delivered exactly once per layer",
    )
    cancel_pid_data, _cancel_pid_size, _cancel_pid_digest = stable_file_facts(
        cancel_pid_file, max_bytes=128
    )
    cancel_pid_lines = cancel_pid_data.splitlines()
    require(
        len(cancel_pid_lines) == 2
        and all(value.isdigit() for value in cancel_pid_lines),
        "cancellation PID handshake was incomplete or malformed",
    )
    cancel_pids = [int(value) for value in cancel_pid_lines]
    require(
        len(set(cancel_pids)) == 2 and all(value > 1 for value in cancel_pids),
        "cancellation PID handshake did not bind two distinct identities",
    )
    time.sleep(0.1)
    require(
        not any(process_alive(pid) for pid in cancel_pids),
        "TERM left a live process-tree member",
    )
    cases.append(
        {
            "case": "cancel_term",
            "ok": True,
            "metadata": str(cancel_root / "stage.meta.json"),
            "pids": cancel_pids,
        }
    )

    for terminal_signal in (signal.SIGHUP, signal.SIGINT, signal.SIGTERM):
        signal_name = signal.Signals(terminal_signal).name
        terminal_root = case_dir(f"terminal_commit_{signal_name.lower()}")
        child_done = terminal_root / "child.done"
        terminal_ready = terminal_root / "terminal.ready"
        terminal_wrapper = subprocess.Popen(
            [
                sys.executable,
                "-I",
                "-S",
                str(Path(__file__).resolve()),
                "run",
                "--cwd",
                str(art_dir),
                "--metadata",
                str(terminal_root / "stage.meta.json"),
                "--stdout",
                str(terminal_root / "stage.out"),
                "--stderr",
                str(terminal_root / "stage.err"),
                "--readiness",
                str(terminal_root / "stage.ready.json"),
                "--artifact-root",
                str(art_dir),
                "--capture-bytes",
                "4096",
                "--output-budget-bytes",
                "65536",
                "--timeout-ms",
                "30000",
                "--grace-ms",
                "500",
                "--stage-id",
                f"terminal_commit_{signal_name.lower()}",
                "--planted",
                "--test-terminal-delay-ms",
                "500",
                "--test-terminal-ready",
                str(terminal_ready),
                "--",
                sys.executable,
                "-c",
                f"from pathlib import Path; Path({str(child_done)!r}).write_text('done')",
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        signal_deadline = time.monotonic() + 15
        while (
            not terminal_ready.exists()
            and terminal_wrapper.poll() is None
            and time.monotonic() < signal_deadline
        ):
            time.sleep(0.01)
        require(
            terminal_ready.exists(),
            f"{signal_name} terminal candidates were not prepared",
        )
        terminal_wrapper.send_signal(terminal_signal)
        _terminal_out, terminal_err = terminal_wrapper.communicate(timeout=30)
        require(
            terminal_wrapper.returncode == CANCELLED,
            f"{signal_name} terminal wrapper exit {terminal_wrapper.returncode}: {terminal_err!r}",
        )
        terminal_meta = read_json_object(terminal_root / "stage.meta.json")
        require(
            terminal_meta["classification"] == "cancelled"
            and hmac.compare_digest(
                str(terminal_meta["cancel_signal"]), signal_name
            ),
            f"{signal_name} did not win terminal metadata publication",
        )
        cases.append(
            {
                "case": f"terminal_commit_{signal_name.lower()}",
                "ok": True,
                "metadata": str(terminal_root / "stage.meta.json"),
            }
        )

    # --- HUP/INT/TERM boundary-injection campaign, runner-side boundaries
    # (bead fln-evidence-runner-bootstrap-btk). Spawn: the signal is queued
    # against the guardian while its launch gate still holds every watched
    # signal blocked, so cancellation deterministically wins before the
    # stopped child can be admitted. Readiness: the signal lands inside the
    # deliberately widened window between readiness publication and the
    # private release, so cancellation wins before exec. Running: the signal
    # lands only after the released target has published its own PID. The
    # terminal-publication boundary is the terminal_commit_* matrix above;
    # the finalizer-side boundaries (finalizer entry, decision write, marker
    # link, post-fsync) are the shell finalizer probes below. In every
    # pre-release case the target argv must never execute.
    for boundary in ("spawn", "readiness", "running"):
        for boundary_signal in (signal.SIGHUP, signal.SIGINT, signal.SIGTERM):
            signal_name = signal.Signals(boundary_signal).name
            case_name = f"boundary_{boundary}_{signal_name.lower()}"
            boundary_root = case_dir(case_name)
            boundary_marker = boundary_root / "target-executed.marker"
            boundary_ready = boundary_root / "stage.ready.json"
            launch_ready = boundary_root / "launch.ready.json"
            launch_release = boundary_root / "launch.release.json"
            boundary_pid_file = boundary_root / "target.pid"
            if boundary == "running":
                boundary_program = (
                    "import os,pathlib,time;"
                    f"pathlib.Path({str(boundary_marker)!r}).write_text('executed');"
                    f"pathlib.Path({str(boundary_pid_file)!r})"
                    ".write_text(str(os.getpid()));"
                    "time.sleep(60)"
                )
            else:
                boundary_program = (
                    "import pathlib;"
                    f"pathlib.Path({str(boundary_marker)!r}).write_text('executed')"
                )
            boundary_argv = [
                sys.executable,
                "-I",
                "-S",
                str(Path(__file__).resolve()),
                "run",
                "--cwd",
                str(art_dir),
                "--metadata",
                str(boundary_root / "stage.meta.json"),
                "--stdout",
                str(boundary_root / "stage.out"),
                "--stderr",
                str(boundary_root / "stage.err"),
                "--readiness",
                str(boundary_ready),
                "--artifact-root",
                str(art_dir),
                "--capture-bytes",
                "4096",
                "--output-budget-bytes",
                "65536",
                "--timeout-ms",
                "30000",
                "--grace-ms",
                "500",
                "--stage-id",
                case_name,
            ]
            if boundary == "spawn":
                # The stop delay widens the spawn-to-admission window so the
                # queued signal always wins during admission even under
                # pathological scheduling of the guardian's forwarder.
                boundary_argv += [
                    "--launch-ready",
                    str(launch_ready),
                    "--launch-release",
                    str(launch_release),
                    "--planted",
                    "--test-before-stop-delay-ms",
                    "1500",
                ]
            elif boundary == "readiness":
                boundary_argv += [
                    "--planted",
                    "--test-before-release-delay-ms",
                    "2000",
                ]
            boundary_argv += ["--", sys.executable, "-c", boundary_program]
            boundary_wrapper = subprocess.Popen(
                boundary_argv,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            boundary_deadline = time.monotonic() + 15
            if boundary == "spawn":
                launch_identity: dict[str, Any] | None = None
                while time.monotonic() < boundary_deadline:
                    if boundary_wrapper.poll() is not None:
                        break
                    try:
                        launch_identity = read_json_object(launch_ready)
                        break
                    except (EvidenceError, FileNotFoundError, OSError):
                        time.sleep(0.01)
                require(
                    launch_identity is not None
                    and launch_identity.get("status") == "awaiting_release"
                    and launch_identity.get("guardian_pid")
                    == boundary_wrapper.pid,
                    f"{case_name}: guardian launch readiness was not bound",
                )
                # W is our unreaped direct child, so this delivery cannot touch
                # a recycled PID; the guardian holds every watched signal
                # blocked until after its launch release, so the signal is
                # queued ahead of the spawn boundary.
                boundary_wrapper.send_signal(boundary_signal)
                release_payload = dict(launch_identity)
                release_payload["status"] = "released"
                write_atomic_new(
                    launch_release, canonical_json(release_payload)
                )
            else:
                waited_paths = [boundary_ready]
                if boundary == "running":
                    waited_paths.append(boundary_pid_file)
                while (
                    not all(path.exists() for path in waited_paths)
                    and boundary_wrapper.poll() is None
                    and time.monotonic() < boundary_deadline
                ):
                    time.sleep(0.01)
                require(
                    all(path.exists() for path in waited_paths),
                    f"{case_name}: the {boundary} boundary was never reached",
                )
                ready_object = read_json_object(boundary_ready)
                require(
                    ready_object.get("status") == "ready",
                    f"{case_name}: readiness was not the admitted-child form",
                )
                boundary_wrapper.send_signal(boundary_signal)
            _boundary_out, boundary_err = boundary_wrapper.communicate(
                timeout=30
            )
            require(
                boundary_wrapper.returncode == CANCELLED,
                f"{case_name}: wrapper exit {boundary_wrapper.returncode}: "
                f"{boundary_err[-500:]!r}",
            )
            boundary_meta = read_json_object(
                boundary_root / "stage.meta.json"
            )
            validate_supervisor_object(
                boundary_root / "stage.meta.json",
                1,
                boundary_meta,
                expected_stage_id=case_name,
            )
            require(
                boundary_meta["classification"] == "cancelled"
                and boundary_meta["reason_code"] == f"signal_{signal_name}"
                and hmac.compare_digest(
                    str(boundary_meta["cancel_signal"]), signal_name
                ),
                f"{case_name}: cancellation was not typed to its boundary signal",
            )
            if boundary == "running":
                require(
                    boundary_marker.exists(),
                    f"{case_name}: released target never reached execution",
                )
                boundary_pid = int(
                    boundary_pid_file.read_text(encoding="ascii")
                )
                require(
                    boundary_pid > 1 and not process_alive(boundary_pid),
                    f"{case_name}: cancellation left the target alive",
                )
            else:
                require(
                    not boundary_marker.exists(),
                    f"{case_name}: target executed across a {boundary}-boundary "
                    "cancellation",
                )
            if boundary == "spawn":
                spawn_ready_object = read_json_object(boundary_ready)
                require(
                    spawn_ready_object.get("status") == "setup_cancelled",
                    f"{case_name}: spawn-boundary readiness was not typed "
                    "setup_cancelled",
                )
            cases.append(
                {
                    "case": case_name,
                    "ok": True,
                    "metadata": str(boundary_root / "stage.meta.json"),
                }
            )

    # --- named stress gaps (bead fln-evidence-runner-bootstrap-btk): real
    # descriptor exhaustion at admission, cancellation storms, and PID
    # allocation churn under live supervision. Forced same-PID reuse needs
    # namespace privileges the no-mock lane does not hold; reuse safety is
    # carried by the identity-refusal cases (emergency_kill_rejects_unrelated,
    # bound_group_stale_identity, direct_child_cleanup_identity) plus the
    # allocation churn here, and by the unreaped-direct-child law.
    rc, meta, exhaustion_root = run_case(
        "admission_fd_exhaustion",
        [sys.executable, "-c", "import time; time.sleep(60)"],
        setup_timeout=10_000,
        fault_point="admission_fd_exhaustion",
    )
    require(rc == SETUP_FAILURE, "descriptor exhaustion changed the exit law")
    require(
        meta["classification"] == "internal_fault"
        and meta["reason_code"] == "supervisor_or_capture_failure"
        and any("Too many open files" in error for error in meta["errors"])
        and meta["phase_timing"]["execution_start_ns"] is None,
        "descriptor exhaustion was not a typed contained setup fault",
    )
    cases.append(
        {
            "case": "admission_fd_exhaustion",
            "ok": True,
            "metadata": str(exhaustion_root / "stage.meta.json"),
        }
    )

    def run_cancellation_storm(
        name: str,
        wrapper_count: int,
        churn_processes: int = 0,
    ) -> None:
        storm_signals = (signal.SIGTERM, signal.SIGINT, signal.SIGHUP)
        churners: list[subprocess.Popen[bytes]] = []
        wrappers: list[tuple[str, subprocess.Popen[bytes], Path, Path]] = []
        surviving_targets: list[tuple[str, int]] = []
        churn_program = (
            "import os\n"
            "while True:\n"
            "    pid = os.fork()\n"
            "    if pid == 0:\n"
            "        os._exit(0)\n"
            "    os.waitpid(pid, 0)\n"
        )
        try:
            for _ in range(churn_processes):
                churners.append(
                    subprocess.Popen(
                        [sys.executable, "-c", churn_program],
                        stdout=subprocess.DEVNULL,
                        stderr=subprocess.DEVNULL,
                    )
                )
            for index in range(wrapper_count):
                member = f"{name}_{index}"
                member_root = case_dir(member)
                member_pid_file = member_root / "target.pid"
                member_program = (
                    "import os,pathlib,time;"
                    f"pathlib.Path({str(member_pid_file)!r})"
                    ".write_text(str(os.getpid()));"
                    "time.sleep(60)"
                )
                wrappers.append(
                    (
                        member,
                        subprocess.Popen(
                            [
                                sys.executable,
                                "-I",
                                "-S",
                                str(Path(__file__).resolve()),
                                "run",
                                "--cwd",
                                str(art_dir),
                                "--metadata",
                                str(member_root / "stage.meta.json"),
                                "--stdout",
                                str(member_root / "stage.out"),
                                "--stderr",
                                str(member_root / "stage.err"),
                                "--readiness",
                                str(member_root / "stage.ready.json"),
                                "--artifact-root",
                                str(art_dir),
                                "--capture-bytes",
                                "4096",
                                "--output-budget-bytes",
                                "65536",
                                "--timeout-ms",
                                "30000",
                                "--grace-ms",
                                "500",
                                "--stage-id",
                                member,
                                "--",
                                sys.executable,
                                "-c",
                                member_program,
                            ],
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                        ),
                        member_root,
                        member_pid_file,
                    )
                )
            storm_deadline = time.monotonic() + 20
            for member, wrapper, member_root, member_pid_file in wrappers:
                while (
                    not (
                        member_pid_file.exists()
                        and (member_root / "stage.ready.json").exists()
                    )
                    and wrapper.poll() is None
                    and time.monotonic() < storm_deadline
                ):
                    time.sleep(0.01)
                require(
                    member_pid_file.exists()
                    and (member_root / "stage.ready.json").exists(),
                    f"{member}: storm target never became stormable",
                )
            # The storm proper: twenty rapid rounds of alternating watched
            # signals against every wrapper, with no pacing between rounds.
            for round_index in range(20):
                for _member, wrapper, _member_root, _member_pid_file in wrappers:
                    if wrapper.poll() is None:
                        wrapper.send_signal(
                            storm_signals[round_index % len(storm_signals)]
                        )
            for member, wrapper, member_root, member_pid_file in wrappers:
                _storm_out, storm_err = wrapper.communicate(timeout=60)
                require(
                    wrapper.returncode == CANCELLED,
                    f"{member}: storm wrapper exit {wrapper.returncode}: "
                    f"{storm_err[-300:]!r}",
                )
                storm_meta = read_json_object(member_root / "stage.meta.json")
                validate_supervisor_object(
                    member_root / "stage.meta.json",
                    1,
                    storm_meta,
                    expected_stage_id=member,
                )
                require(
                    storm_meta["classification"] == "cancelled"
                    and storm_meta["cancel_signal"]
                    in {"SIGHUP", "SIGINT", "SIGTERM"}
                    and storm_meta["reason_code"]
                    == f"signal_{storm_meta['cancel_signal']}",
                    f"{member}: storm cancellation lost its typed terminal",
                )
                surviving_targets.append(
                    (
                        member,
                        int(member_pid_file.read_text(encoding="ascii")),
                    )
                )
        finally:
            for _member, wrapper, _member_root, _member_pid_file in wrappers:
                if wrapper.poll() is None:
                    wrapper.kill()
                    wrapper.communicate(timeout=10)
            for churner in churners:
                churner.kill()
                churner.communicate(timeout=10)
            reap_adopted_children()
        # Liveness is asserted only after every churner is dead, so a recycled
        # target PID cannot alias a live churn child.
        for member, storm_pid in surviving_targets:
            require(
                storm_pid > 1 and not process_alive(storm_pid),
                f"{member}: storm left the target alive",
            )
        cases.append(
            {
                "case": name,
                "ok": True,
                "wrappers": wrapper_count,
                "churners": churn_processes,
            }
        )

    run_cancellation_storm("cancellation_storm", 1)
    run_cancellation_storm("concurrent_cancellation_storm", 6)
    run_cancellation_storm("pid_churn_storm", 4, churn_processes=4)

    emergency_root = case_dir("emergency_kill_detached")
    emergency_pid_file = emergency_root / "pids.txt"
    emergency_program = (
        "import os,pathlib,subprocess,sys,time;"
        "code='import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)';"
        "p=subprocess.Popen([sys.executable,'-c',code],start_new_session=True);"
        f"pathlib.Path({str(emergency_pid_file)!r}).write_text(str(os.getpid())+'\\n'+str(p.pid)+'\\n');"
        "time.sleep(60)"
    )
    emergency_wrapper = subprocess.Popen(
        [
            sys.executable,
            "-I",
            "-S",
            str(Path(__file__).resolve()),
            "run",
            "--cwd",
            str(art_dir),
            "--metadata",
            str(emergency_root / "stage.meta.json"),
            "--stdout",
            str(emergency_root / "stage.out"),
            "--stderr",
            str(emergency_root / "stage.err"),
            "--readiness",
            str(emergency_root / "stage.ready.json"),
            "--artifact-root",
            str(art_dir),
            "--capture-bytes",
            "4096",
            "--output-budget-bytes",
            "65536",
            "--timeout-ms",
            "30000",
            "--grace-ms",
            "500",
            "--stage-id",
            "emergency_kill_detached",
            "--",
            sys.executable,
            "-c",
            emergency_program,
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    emergency_deadline = time.monotonic() + 15
    while (
        not (
            emergency_pid_file.exists()
            and (emergency_root / "stage.ready.json").exists()
        )
        and emergency_wrapper.poll() is None
        and time.monotonic() < emergency_deadline
    ):
        time.sleep(0.01)
    require(emergency_pid_file.exists(), "emergency-kill child did not publish PIDs")
    os.kill(emergency_wrapper.pid, signal.SIGSTOP)
    emergency_kill(
        emergency_root / "stage.ready.json",
        emergency_wrapper.pid,
        "emergency_kill_detached",
    )
    _emergency_out, emergency_err = emergency_wrapper.communicate(timeout=30)
    require(
        emergency_wrapper.returncode == -signal.SIGKILL,
        f"emergency wrapper exit {emergency_wrapper.returncode}: {emergency_err!r}",
    )
    emergency_pids = [
        int(value)
        for value in emergency_pid_file.read_text(encoding="utf-8").splitlines()
    ]
    time.sleep(0.1)
    require(
        not any(process_alive(pid) for pid in emergency_pids),
        "emergency kill left a detached descendant",
    )
    cases.append(
        {
            "case": "emergency_kill_detached",
            "ok": True,
            "pids": emergency_pids,
        }
    )

    forged_root = case_dir("emergency_kill_rejects_unrelated")
    forged_wrapper = subprocess.Popen(
        [sys.executable, "-c", "import time; time.sleep(60)"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    unrelated = subprocess.Popen(
        [sys.executable, "-c", "import time; time.sleep(60)"],
        start_new_session=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    forged_error: EvidenceError | None = None
    forged_wrapper_survived = False
    unrelated_survived = False
    try:
        forged_wrapper_facts = proc_stat_facts(forged_wrapper.pid)
        unrelated_facts = proc_stat_facts(unrelated.pid)
        require(
            forged_wrapper_facts is not None and unrelated_facts is not None,
            "forged-readiness processes disappeared during setup",
        )
        forged_readiness = forged_root / "stage.ready.json"
        write_new(
            forged_readiness,
            canonical_json(
                {
                    "schema": "fln.supervisor-readiness/1",
                    "status": "ready",
                    "stage_id": "emergency_kill_rejects_unrelated",
                    "wrapper_pid": forged_wrapper.pid,
                    "wrapper_start_ticks": forged_wrapper_facts[2],
                    "supervisor_pid": forged_wrapper.pid,
                    "supervisor_start_ticks": forged_wrapper_facts[2],
                    "child_pid": unrelated.pid,
                    "child_pgid": unrelated.pid,
                    "child_start_ticks": unrelated_facts[2],
                }
            ),
        )
        try:
            emergency_kill(
                forged_readiness,
                forged_wrapper.pid,
                "emergency_kill_rejects_unrelated",
            )
        except EvidenceError as error:
            forged_error = error
        time.sleep(0.05)
        forged_wrapper_survived = process_alive(forged_wrapper.pid)
        unrelated_survived = process_alive(unrelated.pid)
    finally:
        if forged_wrapper.poll() is None:
            forged_wrapper.kill()
        forged_wrapper.communicate(timeout=30)
        forged_wrapper.wait(timeout=0)
        if unrelated.poll() is None:
            unrelated.kill()
        unrelated.communicate(timeout=30)
        unrelated.wait(timeout=0)
    require(forged_error is not None, "forged readiness was accepted")
    require(
        forged_wrapper_survived,
        "unproven emergency cleanup killed the outer guardian",
    )
    require(unrelated_survived, "forged readiness killed an unrelated process")
    cases.append(
        {
            "case": "emergency_kill_rejects_unrelated",
            "ok": True,
            "error": str(forged_error),
        }
    )

    guardian_root = case_dir("guardian_contains_wrapper_death")
    guardian_pid_file = guardian_root / "pids.txt"
    guardian_program = (
        "import os,pathlib,signal,subprocess,sys,time;"
        "p=subprocess.Popen([sys.executable,'-c','import time;time.sleep(60)'],"
        "start_new_session=True);"
        f"pathlib.Path({str(guardian_pid_file)!r}).write_text(str(os.getpid())+'\\n'+str(p.pid)+'\\n');"
        "os.kill(os.getppid(),signal.SIGKILL);time.sleep(60)"
    )
    guardian_wrapper = subprocess.Popen(
        [
            sys.executable,
            "-I",
            "-S",
            str(Path(__file__).resolve()),
            "run",
            "--cwd",
            str(art_dir),
            "--metadata",
            str(guardian_root / "stage.meta.json"),
            "--stdout",
            str(guardian_root / "stage.out"),
            "--stderr",
            str(guardian_root / "stage.err"),
            "--readiness",
            str(guardian_root / "stage.ready.json"),
            "--artifact-root",
            str(art_dir),
            "--capture-bytes",
            "4096",
            "--output-budget-bytes",
            "65536",
            "--timeout-ms",
            "30000",
            "--grace-ms",
            "500",
            "--stage-id",
            "guardian_contains_wrapper_death",
            "--",
            sys.executable,
            "-c",
            guardian_program,
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    _guardian_out, guardian_err = guardian_wrapper.communicate(timeout=30)
    require(
        guardian_wrapper.returncode == SETUP_FAILURE,
        f"guardian wrapper exit {guardian_wrapper.returncode}: {guardian_err!r}",
    )
    require(guardian_pid_file.exists(), "wrapper-death child did not publish PIDs")
    guardian_pids = [
        int(value)
        for value in guardian_pid_file.read_text(encoding="utf-8").splitlines()
    ]
    time.sleep(0.1)
    require(
        not any(process_alive(pid) for pid in guardian_pids),
        "guardian left a process after inner-supervisor death",
    )
    cases.append(
        {
            "case": "guardian_contains_wrapper_death",
            "ok": True,
            "pids": guardian_pids,
        }
    )

    guardian_fault_root = case_dir("guardian_pidfd_open_failure")
    guardian_fault_ready = guardian_fault_root / "stage.ready.json"
    guardian_fault_pids = guardian_fault_root / "pids.txt"
    guardian_fault_program = (
        "import os,pathlib,signal,subprocess,sys,time;"
        "code='import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)';"
        "p=subprocess.Popen([sys.executable,'-c',code],start_new_session=True);"
        f"pathlib.Path({str(guardian_fault_pids)!r}).write_text(str(os.getpid())+'\\n'+str(p.pid)+'\\n');"
        "time.sleep(60)"
    )
    guardian_fault_wrapper = subprocess.Popen(
        [
            sys.executable,
            "-I",
            "-S",
            str(Path(__file__).resolve()),
            "run",
            "--cwd",
            str(art_dir),
            "--metadata",
            str(guardian_fault_root / "stage.meta.json"),
            "--stdout",
            str(guardian_fault_root / "stage.out"),
            "--stderr",
            str(guardian_fault_root / "stage.err"),
            "--readiness",
            str(guardian_fault_ready),
            "--artifact-root",
            str(art_dir),
            "--capture-bytes",
            "4096",
            "--output-budget-bytes",
            "65536",
            "--timeout-ms",
            "30000",
            "--grace-ms",
            "500",
            "--stage-id",
            "guardian_pidfd_open_failure",
            "--test-fail-guardian-pidfd-open",
            "--test-guardian-child-ready",
            str(guardian_fault_pids),
            "--",
            sys.executable,
            "-c",
            guardian_fault_program,
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    _fault_out, fault_err = guardian_fault_wrapper.communicate(timeout=30)
    require(
        guardian_fault_wrapper.returncode == SETUP_FAILURE,
        f"guardian pidfd-fault exit {guardian_fault_wrapper.returncode}: {fault_err!r}",
    )
    guardian_fault_readiness = read_json_object(guardian_fault_ready)
    require(
        guardian_fault_readiness.get("schema") == "fln.supervisor-readiness/3"
        and guardian_fault_readiness.get("status") == "ready"
        and guardian_fault_readiness.get("stage_id")
        == "guardian_pidfd_open_failure",
        "post-fork guardian setup fault lacked exact readiness",
    )
    fault_pids = [
        int(value)
        for value in guardian_fault_pids.read_text(encoding="utf-8").splitlines()
    ]
    require(len(fault_pids) == 2, "guardian fault PID handshake was malformed")
    require(
        guardian_fault_readiness.get("child_pid") == fault_pids[0],
        "guardian fault readiness did not bind its stage leader",
    )
    require(
        not any(process_alive(pid) for pid in fault_pids),
        "post-fork guardian setup failure left its detached tree alive",
    )
    cases.append(
        {
            "case": "guardian_pidfd_open_failure",
            "ok": True,
            "pids": fault_pids,
        }
    )

    pdeath_root = case_dir("stopped_exec_parent_death")
    pdeath_pid_file = pdeath_root / "pids.txt"
    pdeath_program = (
        "import os,pathlib,subprocess,sys,time;"
        "p=subprocess.Popen([sys.executable,'-I','-S',"
        f"{str(Path(__file__).resolve())!r},'stopped-exec',"
        "'--expected-parent-pid',str(os.getpid()),'--',sys.executable,'-c',"
        "'import time;time.sleep(60)'],start_new_session=True,"
        "stdin=subprocess.DEVNULL,stdout=subprocess.DEVNULL,"
        "stderr=subprocess.DEVNULL);"
        f"pathlib.Path({str(pdeath_pid_file)!r}).write_text("
        "str(os.getpid())+'\\n'+str(p.pid)+'\\n');"
        "time.sleep(60)"
    )
    pdeath_launcher: subprocess.Popen[bytes] | None = None
    pdeath_handle: tuple[int, int] | None = None
    pdeath_child_pid = 0
    try:
        pdeath_launcher = subprocess.Popen(
            [sys.executable, "-c", pdeath_program],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        deadline = time.monotonic() + 15.0
        previous_payload: bytes | None = None
        stable_reads = 0
        published_pids: tuple[int, ...] = ()
        while time.monotonic() < deadline:
            try:
                payload, _size, _digest = stable_file_facts(
                    pdeath_pid_file, max_bytes=128
                )
                values = tuple(
                    int(value) for value in payload.decode("ascii").splitlines()
                )
                if (
                    len(values) == 2
                    and values[0] == pdeath_launcher.pid
                    and values[1] > 1
                    and values[0] != values[1]
                ):
                    stable_reads = (
                        stable_reads + 1 if payload == previous_payload else 1
                    )
                    previous_payload = payload
                    published_pids = values
                    if stable_reads >= 2:
                        break
                else:
                    stable_reads = 0
                    previous_payload = None
            except (EvidenceError, FileNotFoundError, UnicodeError, ValueError):
                stable_reads = 0
                previous_payload = None
            time.sleep(0.01)
        else:
            raise EvidenceError("stopped-exec parent-death handshake timed out")
        pdeath_child_pid = published_pids[1]
        pdeath_handle = open_process_handle(
            pdeath_child_pid, expected_parent_pid=pdeath_launcher.pid
        )
        require(pdeath_handle is not None, "stopped-exec child identity was unbound")
        retry_attempts = 0

        def delayed_identity_open() -> tuple[int, int] | None:
            nonlocal retry_attempts
            retry_attempts += 1
            if retry_attempts == 1:
                return None
            return open_process_handle(
                pdeath_child_pid, expected_parent_pid=pdeath_launcher.pid
            )

        retry_handle = bind_direct_child_until(
            pdeath_child_pid,
            pdeath_launcher.pid,
            time.monotonic() + 30.0,
            open_handle=delayed_identity_open,
        )
        try:
            require(
                retry_attempts == 2 and retry_handle[0] == pdeath_handle[0],
                "direct-child identity binding did not retry the same lifetime",
            )
        finally:
            os.close(retry_handle[1])
        replacement_descriptor = os.open(os.devnull, os.O_RDONLY)
        try:
            try:
                bind_direct_child_until(
                    pdeath_child_pid,
                    pdeath_launcher.pid,
                    time.monotonic() + 30.0,
                    open_handle=lambda: (
                        pdeath_handle[0] + 1,
                        replacement_descriptor,
                    ),
                )
            except EvidenceError as exc:
                require(
                    str(exc) == "process identity changed before binding",
                    "replacement direct-child identity did not fail closed",
                )
            else:
                raise EvidenceError("replacement direct-child identity was accepted")
            try:
                os.fstat(replacement_descriptor)
            except OSError as exc:
                require(
                    exc.errno == errno.EBADF,
                    "replacement direct-child handle closed unexpectedly",
                )
            else:
                raise EvidenceError("replacement direct-child handle was not closed")
        finally:
            try:
                os.close(replacement_descriptor)
            except OSError as exc:
                if exc.errno != errno.EBADF:
                    raise
        deadline = time.monotonic() + 5.0
        while True:
            pdeath_facts = proc_stat_facts(pdeath_child_pid)
            if (
                pdeath_facts is None
                or pdeath_facts[0] == "Z"
                or pdeath_facts[2] != pdeath_handle[0]
            ):
                raise EvidenceError("stopped-exec child changed before becoming inert")
            if (
                pdeath_facts[0] in {"T", "t"}
                and pdeath_facts[1] == pdeath_child_pid
            ):
                break
            if time.monotonic() >= deadline:
                raise EvidenceError("stopped-exec child did not become inert in time")
            time.sleep(0.005)
        require(
            pdeath_facts[0] in {"T", "t"}
            and pdeath_facts[1] == pdeath_child_pid
            and pdeath_facts[2] == pdeath_handle[0],
            "stopped-exec child did not reach its inert session state",
        )
        identity_probe = subprocess.run(
            [
                sys.executable,
                "-I",
                "-S",
                str(Path(__file__).resolve()),
                "process-start-ticks",
                "--pid",
                str(pdeath_child_pid),
                "--expected-parent-pid",
                str(pdeath_launcher.pid),
                "--wait-ms",
                "30000",
                "--session-leader",
                "--stopped",
            ],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=60,
        )
        require(
            identity_probe.returncode == PASS,
            "declared readiness budget was rejected by identity binding: "
            f"{identity_probe.stderr[-1000:]!r}",
        )
        require(
            identity_probe.stdout.decode("ascii").strip()
            == str(pdeath_handle[0]),
            "readiness-budget identity probe returned the wrong lifetime",
        )
        pdeath_launcher.kill()
        pdeath_launcher.communicate(timeout=10)
        deadline = time.monotonic() + 5.0
        while process_handle_alive(pdeath_child_pid, pdeath_handle):
            if time.monotonic() >= deadline:
                break
            time.sleep(0.01)
        require(
            not process_handle_alive(pdeath_child_pid, pdeath_handle),
            "stopped-exec child survived its launching parent",
        )
    finally:
        try:
            if pdeath_launcher is not None and pdeath_launcher.poll() is None:
                pdeath_launcher.kill()
                pdeath_launcher.communicate(timeout=10)
        finally:
            if pdeath_handle is not None:
                try:
                    if process_handle_alive(pdeath_child_pid, pdeath_handle):
                        signal_process_handle(
                            pdeath_child_pid, pdeath_handle, signal.SIGKILL
                        )
                finally:
                    os.close(pdeath_handle[1])
    cases.append(
        {
            "case": "stopped_exec_parent_death",
            "ok": True,
            "launcher_pid": published_pids[0],
            "child_pid": pdeath_child_pid,
            "identity_wait_budget_ms": 30_000,
            "identity_bind_attempts": retry_attempts,
        }
    )

    case_dir("direct_child_cleanup_identity")
    direct_child = subprocess.Popen(
        [sys.executable, "-c", "import time;time.sleep(60)"],
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    direct_handle: tuple[int, int] | None = None
    try:
        direct_handle = open_process_handle(
            direct_child.pid, expected_parent_pid=os.getpid()
        )
        require(direct_handle is not None, "direct child identity was unbound")
        wrong_parent_pid = os.getppid()
        require(
            wrong_parent_pid > 1 and wrong_parent_pid != os.getpid(),
            "direct child self-test lacks a distinct wrong parent",
        )
        wrong_parent_rc = cmd_kill_direct_child(
            argparse.Namespace(
                pid=direct_child.pid,
                expected_parent_pid=wrong_parent_pid,
                wait_ms=100,
            )
        )
        require(wrong_parent_rc == PASS, "wrong-parent cleanup did not fail closed")
        require(
            process_handle_alive(direct_child.pid, direct_handle),
            "wrong-parent cleanup signalled the direct child",
        )
        exact_rc = cmd_kill_direct_child(
            argparse.Namespace(
                pid=direct_child.pid,
                expected_parent_pid=os.getpid(),
                wait_ms=5000,
            )
        )
        require(exact_rc == PASS, "exact direct-child cleanup failed")
        require(
            not process_handle_alive(direct_child.pid, direct_handle),
            "exact direct-child cleanup left its bound lifetime live",
        )
        direct_child.communicate(timeout=10)
    finally:
        try:
            if direct_child.poll() is None:
                if direct_handle is not None:
                    signal_process_handle(
                        direct_child.pid, direct_handle, signal.SIGKILL
                    )
                else:
                    direct_child.kill()
                direct_child.communicate(timeout=10)
        finally:
            if direct_handle is not None:
                os.close(direct_handle[1])
    cases.append(
        {
            "case": "direct_child_cleanup_identity",
            "ok": True,
            "child_pid": direct_child.pid,
        }
    )

    bound_group_root = case_dir("bound_group_stale_identity")
    bound_group_member_file = bound_group_root / "member.pid"
    bound_group_program = (
        "import pathlib,subprocess,sys,time;"
        "p=subprocess.Popen([sys.executable,'-c','import time;time.sleep(60)']);"
        f"pathlib.Path({str(bound_group_member_file)!r}).write_text(str(p.pid));"
        "time.sleep(60)"
    )
    bound_group_child = subprocess.Popen(
        [
            sys.executable,
            "-I",
            "-S",
            str(Path(__file__).resolve()),
            "stopped-exec",
            "--expected-parent-pid",
            str(os.getpid()),
            "--",
            sys.executable,
            "-c",
            bound_group_program,
        ],
        start_new_session=True,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    bound_group_sentinel = subprocess.Popen(
        [sys.executable, "-c", "import time;time.sleep(60)"],
        start_new_session=True,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    bound_group_handle: tuple[int, int] | None = None
    bound_group_member_handle: tuple[int, int] | None = None
    bound_group_sentinel_handle: tuple[int, int] | None = None
    bound_group_member_pid = 0
    try:
        bound_group_sentinel_handle = open_process_handle(
            bound_group_sentinel.pid, expected_parent_pid=os.getpid()
        )
        require(
            bound_group_sentinel_handle is not None,
            "unrelated process-group sentinel was not bindable",
        )
        deadline = time.monotonic() + 5.0
        while time.monotonic() < deadline:
            bound_group_handle = open_process_handle(
                bound_group_child.pid, expected_parent_pid=os.getpid()
            )
            bound_group_facts = proc_stat_facts(bound_group_child.pid)
            if (
                bound_group_handle is not None
                and bound_group_facts is not None
                and bound_group_facts[0] in {"T", "t"}
                and bound_group_facts[1] == bound_group_child.pid
                and bound_group_facts[2] == bound_group_handle[0]
            ):
                break
            if bound_group_handle is not None:
                os.close(bound_group_handle[1])
                bound_group_handle = None
            time.sleep(0.005)
        else:
            raise EvidenceError("bound-group child did not become inert in time")
        kill_bound_process_group(
            bound_group_child.pid,
            bound_group_handle[0] + 1,
            os.getpid(),
        )
        require(
            process_handle_alive(bound_group_child.pid, bound_group_handle),
            "stale start-time cleanup signalled the bound process group",
        )
        require(
            process_handle_alive(
                bound_group_sentinel.pid, bound_group_sentinel_handle
            ),
            "stale start-time cleanup signalled the unrelated sentinel",
        )
        require(
            signal_process_handle(
                bound_group_child.pid, bound_group_handle, signal.SIGCONT
            ),
            "bound-group child disappeared before descendant launch",
        )
        deadline = time.monotonic() + 10.0
        while time.monotonic() < deadline:
            try:
                member_data, _size, _digest = stable_file_facts(
                    bound_group_member_file, max_bytes=64
                )
                candidate_pid = int(member_data.decode("ascii"))
            except (EvidenceError, FileNotFoundError, UnicodeError, ValueError):
                time.sleep(0.005)
                continue
            candidate_handle = open_process_handle(
                candidate_pid, expected_parent_pid=bound_group_child.pid
            )
            candidate_facts = proc_stat_facts(candidate_pid)
            if (
                candidate_handle is not None
                and candidate_facts is not None
                and candidate_facts[0] != "Z"
                and candidate_facts[1] == bound_group_child.pid
                and candidate_facts[2] == candidate_handle[0]
            ):
                bound_group_member_pid = candidate_pid
                bound_group_member_handle = candidate_handle
                break
            if candidate_handle is not None:
                os.close(candidate_handle[1])
            time.sleep(0.005)
        else:
            raise EvidenceError("bound process-group descendant was not bindable")
        require(
            {bound_group_child.pid, bound_group_member_pid}.issubset(
                live_process_group_members(bound_group_child.pid)
            ),
            "bound process-group topology omitted its descendant",
        )
        kill_bound_process_group(
            bound_group_child.pid,
            bound_group_handle[0],
            os.getpid(),
        )
        require(
            not process_handle_alive(bound_group_child.pid, bound_group_handle),
            "exact process-group cleanup left its leader live",
        )
        require(
            not process_handle_alive(
                bound_group_member_pid, bound_group_member_handle
            ),
            "exact process-group cleanup left its descendant live",
        )
        require(
            process_handle_alive(
                bound_group_sentinel.pid, bound_group_sentinel_handle
            ),
            "exact process-group cleanup signalled the unrelated sentinel",
        )
        bound_group_child.communicate(timeout=10)
        deadline = time.monotonic() + 5.0
        while time.monotonic() < deadline:
            reap_adopted_children()
            member_facts = proc_stat_facts(bound_group_member_pid)
            if (
                member_facts is None
                or member_facts[2] != bound_group_member_handle[0]
            ):
                break
            time.sleep(0.005)
        require(
            (member_facts := proc_stat_facts(bound_group_member_pid)) is None
            or member_facts[2] != bound_group_member_handle[0],
            "exact process-group cleanup left its descendant unreaped",
        )
        exact_sentinel_rc = cmd_kill_direct_child(
            argparse.Namespace(
                pid=bound_group_sentinel.pid,
                expected_parent_pid=os.getpid(),
                wait_ms=5000,
            )
        )
        require(exact_sentinel_rc == PASS, "sentinel cleanup failed")
        bound_group_sentinel.communicate(timeout=10)
    finally:
        try:
            if (
                bound_group_member_handle is not None
                and process_handle_alive(
                    bound_group_member_pid, bound_group_member_handle
                )
            ):
                signal_process_handle(
                    bound_group_member_pid,
                    bound_group_member_handle,
                    signal.SIGKILL,
                )
            if bound_group_child.poll() is None:
                if bound_group_handle is not None:
                    signal_process_handle(
                        bound_group_child.pid, bound_group_handle, signal.SIGKILL
                    )
                else:
                    bound_group_child.kill()
                bound_group_child.communicate(timeout=10)
            if bound_group_sentinel.poll() is None:
                if bound_group_sentinel_handle is not None:
                    signal_process_handle(
                        bound_group_sentinel.pid,
                        bound_group_sentinel_handle,
                        signal.SIGKILL,
                    )
                else:
                    bound_group_sentinel.kill()
                bound_group_sentinel.communicate(timeout=10)
            reap_adopted_children()
        finally:
            if bound_group_member_handle is not None:
                os.close(bound_group_member_handle[1])
            if bound_group_sentinel_handle is not None:
                os.close(bound_group_sentinel_handle[1])
            if bound_group_handle is not None:
                os.close(bound_group_handle[1])
    cases.append(
        {
            "case": "bound_group_stale_identity",
            "ok": True,
            "leader_pid": bound_group_child.pid,
            "member_pid": bound_group_member_pid,
            "sentinel_pid": bound_group_sentinel.pid,
        }
    )

    # The complete finalizer-side boundary matrix (bead
    # fln-evidence-runner-bootstrap-btk): every watched signal at every named
    # post-terminal boundary. Before the bundle decision (finalizer entry via
    # spawn_bind/active_wait, and decision_write immediately before the
    # publisher spawns) the signal must win: typed cancellation, an empty
    # claimed decision, and no committed bundle. From the linked decision
    # onward (marker_link holds the decision-to-marker window open,
    # post_decision fires after the durable commit) the signal must lose: the
    # committed bundle survives and validates. helper_failure exercises the
    # cleanup-uncertainty dimension of finalizer entry.
    for probe_signal, probe_exit in (
        (signal.SIGHUP, 129),
        (signal.SIGINT, 130),
        (signal.SIGTERM, 143),
    ):
        cases.append(
            run_shell_finalizer_probe(
                "spawn_bind",
                probe_signal,
                probe_exit,
                expect_committed_bundle=False,
            )
        )
        cases.append(
            run_shell_finalizer_probe(
                "active_wait",
                probe_signal,
                probe_exit,
                expect_committed_bundle=False,
            )
        )
        cases.append(
            run_shell_finalizer_probe(
                "decision_write",
                probe_signal,
                probe_exit,
                expect_committed_bundle=False,
            )
        )
        cases.append(
            run_shell_finalizer_probe(
                "marker_link",
                probe_signal,
                PASS,
                expect_committed_bundle=True,
            )
        )
        cases.append(
            run_shell_finalizer_probe(
                "post_decision",
                probe_signal,
                PASS,
                expect_committed_bundle=True,
            )
        )
    cases.append(
        run_shell_finalizer_probe(
            "helper_failure",
            signal.SIGTERM,
            SETUP_FAILURE,
            expect_committed_bundle=False,
        )
    )

    collision_root = case_dir("artifact_publication_failure")
    collision = collision_root / "not-a-directory"
    write_new(collision, b"collision\n")
    metadata = collision_root / "stage.meta.json"
    rc = run_supervised(
        argv=[sys.executable, "-c", "print('must-not-pass')"],
        cwd=art_dir,
        metadata_path=metadata,
        stdout_path=collision_root / "stage.out",
        stderr_path=collision_root / "stage.err",
        readiness_path=collision_root / "stage.ready.json",
        artifact_root=art_dir,
        capture_bytes=4096,
        output_budget_bytes=65_536,
        timeout_ms=5000,
        grace_ms=500,
        stage_id="artifact_publication_failure",
        planted=True,
        test_fault_point="capture_stdout",
    )
    meta = read_json_object(metadata)
    validate_supervisor_object(
        metadata,
        1,
        meta,
        expected_stage_id="artifact_publication_failure",
    )
    require(rc == SETUP_FAILURE, "artifact publication failure returned success")
    require(
        meta["classification"] == "internal_fault",
        "artifact failure was not internal fault",
    )
    require(
        meta["reason_code"] == "artifact_publication_failure",
        "artifact failure reason lost",
    )
    cases.append(
        {"case": "artifact_publication_failure", "ok": True, "metadata": str(metadata)}
    )

    malformed_root = case_dir("malformed_evidence")
    malformed = malformed_root / "malformed.ndjson"
    write_new(malformed, b'{"schema":"fln.check/2"\n')
    try:
        validate_run(malformed, "fln.check/2", "pass")
    except EvidenceError:
        pass
    else:
        raise EvidenceError("malformed NDJSON was accepted")
    incomplete = malformed_root / "incomplete.ndjson"
    write_new(
        incomplete,
        canonical_json(
            {
                "schema": "fln.check/2",
                "event": "run_start",
                "run_id": "incomplete",
                "bead": "fln-8mj",
                "sequence": 0,
                "monotonic_ns": 1,
                "wall_time_utc": utc_now(),
            }
        ),
    )
    try:
        validate_run(incomplete, "fln.check/2", "pass")
    except EvidenceError:
        pass
    else:
        raise EvidenceError("unterminated run was accepted")
    cases.append(
        {"case": "strict_ndjson_validator", "ok": True, "mutants_killed": 2}
    )

    identity_validation_root = case_dir("environment_identity_matrix_validation")
    identity_run_id = "environment-identity-self-test"

    def identity_hex(index: int) -> str:
        return f"{index:064x}"

    def identity_log(records: Sequence[dict[str, Any]]) -> bytes:
        return (
            b"running 1 test\n"
            + b"".join(
                (
                    json.dumps(
                        record,
                        ensure_ascii=False,
                        separators=(",", ":"),
                    )
                    + "\n"
                ).encode()
                for record in records
            )
            + b"test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured\n"
        )

    def write_identity_fixture(
        label: str,
        records: Sequence[dict[str, Any]],
        *,
        stderr: bytes = b"",
    ) -> tuple[Path, Path]:
        stdout_path = identity_validation_root / f"{label}.out"
        stderr_path = identity_validation_root / f"{label}.err"
        write_new(stdout_path, identity_log(records))
        write_new(stderr_path, stderr)
        return stdout_path, stderr_path

    def identity_validator_call(
        validator: Callable[..., dict[str, Any]],
        stdout_path: Path,
        stderr_path: Path,
    ) -> dict[str, Any]:
        return validator(
            stdout_path,
            stderr_path,
            identity_run_id,
            0,
            artifact_root=identity_validation_root,
            expected_stdout_artifact=stdout_path.name,
            expected_stderr_artifact=stderr_path.name,
        )

    def expect_identity_rejection(
        label: str,
        validator: Callable[..., dict[str, Any]],
        records: Sequence[dict[str, Any]],
        *,
        stderr: bytes = b"",
    ) -> None:
        stdout_path, stderr_path = write_identity_fixture(
            label, records, stderr=stderr
        )
        try:
            identity_validator_call(validator, stdout_path, stderr_path)
        except EvidenceError:
            return
        raise EvidenceError(f"{label} environment-identity mutant was accepted")

    tag_records: list[dict[str, Any]] = []
    for index, ((family, variant), golden) in enumerate(
        DECLARATION_TAG_GOLDENS.items(), 1
    ):
        kind, tag, stream_bytes, stream_hash, digest = golden
        root = identity_hex(100 + index)
        tag_records.append(
            {
                "schema": DECLARATION_TAG_MATRIX_SCHEMA,
                "version": ENVIRONMENT_IDENTITY_VERSION,
                "run_id": identity_run_id,
                "beads": ["fln-amv.12", "fln-amv.14"],
                "scenario": "declaration-tag-matrix",
                "case": f"{family}/{variant}",
                "family": family,
                "variant": variant,
                "kind": kind,
                "canonical_tag": tag,
                "production_tag": tag,
                "tag_source": "explicit_exhaustive_match",
                "stream_bytes": stream_bytes,
                "golden_stream_bytes": stream_bytes,
                "stream_hash": stream_hash,
                "golden_stream_hash": stream_hash,
                "expected_digest": digest,
                "actual_digest": digest,
                "golden_digest": digest,
                "repeated_digest": digest,
                "digest_relation": "equal",
                "repeat_relation": "equal",
                "expected_root": root,
                "actual_root": root,
                "root_relation": "equal",
                "model": "independent-complete-stream-v1",
                "status": "pass",
                "elapsed_us": index,
                "final_state": "verified",
            }
        )
    aggregate_root = identity_hex(500)
    for index, workers in enumerate((1, 8, 32), 1):
        tag_records.append(
            {
                "schema": DECLARATION_TAG_MATRIX_SCHEMA,
                "version": ENVIRONMENT_IDENTITY_VERSION,
                "run_id": identity_run_id,
                "beads": ["fln-amv.12", "fln-amv.14"],
                "scenario": "declaration-tag-thread-matrix",
                "worker_count": workers,
                "distinct_root_count": 1,
                "expected_root": aggregate_root,
                "actual_root": aggregate_root,
                "root_relation": "equal",
                "order_independence": "proven",
                "status": "pass",
                "elapsed_us": index,
                "final_state": "verified",
            }
        )
    tag_records.append(
        {
            "schema": DECLARATION_TAG_MATRIX_SCHEMA,
            "version": ENVIRONMENT_IDENTITY_VERSION,
            "run_id": identity_run_id,
            "beads": ["fln-amv.12", "fln-amv.14"],
            "scenario": "declaration-tag-summary",
            "case_count": 7,
            "unique_digest_count": 7,
            "pairwise_comparisons": 21,
            "expected_pairwise_comparisons": 21,
            "thread_matrix": [1, 8, 32],
            "thread_matrix_roots_distinct": 1,
            "canonical_root": aggregate_root,
            "source_order_defect_root": identity_hex(501),
            "source_order_defect_relation": "differs",
            "omitted_declaration_root": identity_hex(502),
            "omitted_declaration_relation": "differs",
            "named_defects_discriminated": [
                "cast_after_source_reorder",
                "omitted_declaration",
            ],
            "claim_type": "bounded_model",
            "status": "pass",
            "elapsed_us": 10,
            "final_state": "verified",
        }
    )
    tag_stdout, tag_stderr = write_identity_fixture("tag_valid", tag_records)
    require(
        identity_validator_call(
            validate_declaration_tag_matrix, tag_stdout, tag_stderr
        )["records"]
        == 11,
        "valid declaration-tag matrix was not accepted",
    )
    tag_missing_field = json.loads(json.dumps(tag_records))
    del tag_missing_field[0]["production_tag"]
    expect_identity_rejection(
        "tag_missing_field",
        validate_declaration_tag_matrix,
        tag_missing_field,
    )
    tag_wrong_pin = json.loads(json.dumps(tag_records))
    tag_wrong_pin[0]["golden_digest"] = identity_hex(900)
    expect_identity_rejection(
        "tag_wrong_pin",
        validate_declaration_tag_matrix,
        tag_wrong_pin,
    )

    membership_kinds = (
        "definition",
        "theorem",
        "opaque",
        "inductive",
        "recursor",
    )
    membership_cases = {
        "empty": 0,
        "singleton": 1,
        "repeated": 2,
        "ordered": 2,
        "reordered": 2,
        "renamed": 2,
        "declared_large": 4096,
    }
    membership_records: list[dict[str, Any]] = []
    membership_matrix: dict[tuple[str, str], dict[str, Any]] = {}
    identity_index = 1_000
    for kind in membership_kinds:
        for membership_case, member_count in membership_cases.items():
            digest = identity_hex(identity_index)
            root = identity_hex(identity_index + 500)
            identity_index += 1
            row = {
                "schema": DECLARATION_MEMBERSHIP_SCHEMA,
                "version": ENVIRONMENT_IDENTITY_VERSION,
                "run_id": identity_run_id,
                "beads": ["fln-amv.1", "fln-amv.14"],
                "scenario": "declaration-membership-matrix",
                "kind": kind,
                "membership_case": membership_case,
                "member_count": member_count,
                "expected_digest": digest,
                "actual_digest": digest,
                "repeated_digest": digest,
                "digest_relation": "equal",
                "repeat_relation": "equal",
                "expected_root": root,
                "actual_root": root,
                "root_relation": "equal",
                "root_propagation": "exact",
                "model": "independent-canonical-membership-v1",
                "status": "pass",
                "elapsed_us": identity_index,
                "final_state": "verified",
            }
            membership_records.append(row)
            membership_matrix[(kind, membership_case)] = row
    for kind_index, kind in enumerate(membership_kinds, 1):
        ordered = membership_matrix[(kind, "ordered")]
        membership_records.append(
            {
                "schema": DECLARATION_MEMBERSHIP_SCHEMA,
                "version": ENVIRONMENT_IDENTITY_VERSION,
                "run_id": identity_run_id,
                "beads": ["fln-amv.1", "fln-amv.14"],
                "scenario": "declaration-membership-defects",
                "kind": kind,
                "canonical_digest": ordered["actual_digest"],
                "dropped_list_digest": identity_hex(2_000 + kind_index),
                "dropped_list_relation": "differs",
                "omitted_count_digest": identity_hex(2_100 + kind_index),
                "omitted_count_relation": "differs",
                "sorted_members_digest": ordered["actual_digest"],
                "sorted_members_relation": "differs",
                "sorted_members_order_collapse": True,
                "wrong_domain_digest": identity_hex(2_200 + kind_index),
                "wrong_domain_relation": "differs",
                "real_root": ordered["actual_root"],
                "stale_digest_root": identity_hex(2_300 + kind_index),
                "root_propagation_relation": "differs",
                "named_defects_discriminated": [
                    "dropped_list",
                    "omitted_count",
                    "reordered_membership",
                    "wrong_domain",
                    "failed_root_propagation",
                ],
                "boundary_distinctions": 7,
                "status": "pass",
                "final_state": "verified",
            }
        )
    membership_records.append(
        {
            "schema": DECLARATION_MEMBERSHIP_SCHEMA,
            "version": ENVIRONMENT_IDENTITY_VERSION,
            "run_id": identity_run_id,
            "beads": ["fln-amv.1", "fln-amv.14"],
            "scenario": "declaration-membership-summary",
            "kind_count": 5,
            "membership_case_count": 7,
            "matrix_rows": 40,
            "large_member_count": 4096,
            "opaque_solo_digest": membership_matrix[
                ("opaque", "singleton")
            ]["actual_digest"],
            "opaque_grouped_digest": membership_matrix[
                ("opaque", "ordered")
            ]["actual_digest"],
            "opaque_regression_relation": "differs",
            "root_propagation": "exact",
            "claim_type": "bounded_model",
            "status": "pass",
            "elapsed_us": 1,
            "final_state": "verified",
        }
    )
    membership_stdout, membership_stderr = write_identity_fixture(
        "membership_valid", membership_records
    )
    require(
        identity_validator_call(
            validate_declaration_membership,
            membership_stdout,
            membership_stderr,
        )["records"]
        == 41,
        "valid declaration-membership matrix was not accepted",
    )
    membership_false_collapse = json.loads(json.dumps(membership_records))
    opaque_defect = next(
        row
        for row in membership_false_collapse
        if row.get("scenario") == "declaration-membership-defects"
        and row.get("kind") == "opaque"
    )
    opaque_defect["sorted_members_digest"] = membership_matrix[
        ("opaque", "reordered")
    ]["actual_digest"]
    expect_identity_rejection(
        "membership_false_collapse",
        validate_declaration_membership,
        membership_false_collapse,
    )

    merge_tags = {
        "append_ordered": 0,
        "set_union": 1,
        "conflicts_require_review": 2,
    }
    checkpoint_tags = {"journal_suffix": 0, "full_journal": 1}
    provenance_tags = {"understood": 0, "opaque": 1}
    descriptor_records: list[dict[str, Any]] = []
    descriptor_matrix: dict[tuple[str, str, str], dict[str, Any]] = {}
    descriptor_index = 3_000
    for merge, merge_tag in merge_tags.items():
        for checkpoint, checkpoint_tag in checkpoint_tags.items():
            for provenance, provenance_tag in provenance_tags.items():
                digest = identity_hex(descriptor_index)
                root = identity_hex(descriptor_index + 500)
                descriptor_index += 1
                key = (merge, checkpoint, provenance)
                row = {
                    "schema": EXTENSION_DESCRIPTOR_MATRIX_SCHEMA,
                    "version": ENVIRONMENT_IDENTITY_VERSION,
                    "run_id": identity_run_id,
                    "beads": ["fln-amv.2", "fln-amv.14"],
                    "scenario": "extension-descriptor-matrix",
                    "merge": merge,
                    "merge_tag": merge_tag,
                    "checkpoint": checkpoint,
                    "checkpoint_tag": checkpoint_tag,
                    "provenance": provenance,
                    "provenance_tag": provenance_tag,
                    "descriptor_position": "before_journal",
                    "journal_entries": 2,
                    "expected_digest": digest,
                    "actual_digest": digest,
                    "repeated_digest": digest,
                    "digest_relation": "equal",
                    "repeat_relation": "equal",
                    "expected_root": root,
                    "actual_root": root,
                    "root_relation": "equal",
                    "root_propagation": "exact",
                    "model": "independent-descriptor-layout-v1",
                    "status": "pass",
                    "elapsed_us": descriptor_index,
                    "final_state": "verified",
                }
                descriptor_records.append(row)
                descriptor_matrix[key] = row
    for defect_index, (key, row) in enumerate(descriptor_matrix.items(), 1):
        merge, checkpoint, provenance = key
        canonical = row["actual_digest"]
        tag_discriminating = merge != "conflicts_require_review"
        field_discriminating = merge_tags[merge] != checkpoint_tags[checkpoint]
        descriptor_records.append(
            {
                "schema": EXTENSION_DESCRIPTOR_MATRIX_SCHEMA,
                "version": ENVIRONMENT_IDENTITY_VERSION,
                "run_id": identity_run_id,
                "beads": ["fln-amv.2", "fln-amv.14"],
                "scenario": "extension-descriptor-defects",
                "merge": merge,
                "checkpoint": checkpoint,
                "provenance": provenance,
                "canonical_digest": canonical,
                "omit_merge_digest": identity_hex(4_000 + defect_index),
                "omit_merge_relation": "differs",
                "omit_checkpoint_digest": identity_hex(4_100 + defect_index),
                "omit_checkpoint_relation": "differs",
                "omit_provenance_digest": identity_hex(4_200 + defect_index),
                "omit_provenance_relation": "differs",
                "swapped_tag_digest": (
                    identity_hex(4_300 + defect_index)
                    if tag_discriminating
                    else canonical
                ),
                "swapped_tag_relation": (
                    "differs"
                    if tag_discriminating
                    else "equal_by_construction"
                ),
                "swapped_tag_discriminating": tag_discriminating,
                "swapped_field_digest": (
                    identity_hex(4_400 + defect_index)
                    if field_discriminating
                    else canonical
                ),
                "swapped_field_relation": (
                    "differs"
                    if field_discriminating
                    else "equal_by_construction"
                ),
                "swapped_field_discriminating": field_discriminating,
                "debug_text_digest": identity_hex(4_500 + defect_index),
                "debug_text_relation": "differs",
                "after_journal_digest": identity_hex(4_600 + defect_index),
                "after_journal_relation": "differs",
                "named_defects_discriminated": [
                    "omitted_dimension",
                    "swapped_tag",
                    "debug_text",
                    "after_journal",
                ],
                "status": "pass",
                "final_state": "verified",
            }
        )
    descriptor_records.append(
        {
            "schema": EXTENSION_DESCRIPTOR_MATRIX_SCHEMA,
            "version": ENVIRONMENT_IDENTITY_VERSION,
            "run_id": identity_run_id,
            "beads": ["fln-amv.2", "fln-amv.14"],
            "scenario": "extension-descriptor-summary",
            "combination_count": 12,
            "merge_variants": 3,
            "checkpoint_variants": 2,
            "provenance_variants": 2,
            "distinct_delta_digests": 12,
            "distinct_logical_roots": 12,
            "descriptor_position": "before_journal",
            "matrix_rows": 24,
            "root_propagation": "exact",
            "claim_type": "bounded_model",
            "status": "pass",
            "elapsed_us": 1,
            "final_state": "verified",
        }
    )
    descriptor_stdout, descriptor_stderr = write_identity_fixture(
        "descriptor_valid", descriptor_records
    )
    require(
        identity_validator_call(
            validate_extension_descriptor_matrix,
            descriptor_stdout,
            descriptor_stderr,
        )["records"]
        == 25,
        "valid extension-descriptor matrix was not accepted",
    )
    descriptor_false_conditional = json.loads(json.dumps(descriptor_records))
    nondiscriminating = next(
        row
        for row in descriptor_false_conditional
        if row.get("scenario") == "extension-descriptor-defects"
        and row.get("merge") == "conflicts_require_review"
    )
    nondiscriminating["swapped_tag_digest"] = identity_hex(9_000)
    expect_identity_rejection(
        "descriptor_false_conditional",
        validate_extension_descriptor_matrix,
        descriptor_false_conditional,
    )

    environment_state_records = [
        {
            "schema": ENVIRONMENT_STATE_SCHEMA,
            "version": ENVIRONMENT_IDENTITY_VERSION,
            "run_id": identity_run_id,
            "beads": ["fln-amv.5", "fln-amv.7"],
            "scenario": "persistent-journal",
            "status": "pass",
            "entry_count": 69,
            "chunk_capacity": 32,
            "chunk_count": 3,
            "node_count": 4,
            "shared_node_count": 2,
            "fresh_node_count": 2,
            "append_operations": 69,
            "replay_operations": 69,
            "node_allocations": 106,
            "copied_child_slots": 77,
            "copied_entry_slots": 1002,
            "payload_bytes": 552,
            "expected_order_hash": "8ac9a67f1111de29",
            "actual_order_hash": "8ac9a67f1111de29",
            "expected_root": (
                "cffbec6eac072caa55a121f4e21f4bc6"
                "ac9c13bb324470a8f8ff8ba04ab797f9"
            ),
            "actual_root": (
                "cffbec6eac072caa55a121f4e21f4bc6"
                "ac9c13bb324470a8f8ff8ba04ab797f9"
            ),
            "snapshot_root": (
                "8f1976245ae9dce33f3eb0d3febd2bc"
                "32e2b5f1f88710c7aa579b80b0c1705ab"
            ),
            "elapsed_us": 1,
            "final_state": "verified",
        },
        {
            "schema": ENVIRONMENT_STATE_SCHEMA,
            "version": ENVIRONMENT_IDENTITY_VERSION,
            "run_id": identity_run_id,
            "beads": ["fln-amv.7"],
            "scenario": "checkpoint-roundtrip",
            "mode": "journal_suffix",
            "status": "pass",
            "base_id": (
                "a9c5fd7d6f4e70ce4c0a6cd3f90c9355"
                "46bcc9c5ff573f4f9d93997677d632ee"
            ),
            "checkpoint_id": "v1-suffix-5-7567db5a9df19e29",
            "restored_id": (
                "8d00a22b42354950b09dc8f2e927c523"
                "7dc7357cbd2bec7985fff5770b753972"
            ),
            "base_root": (
                "8f1976245ae9dce33f3eb0d3febd2bc"
                "32e2b5f1f88710c7aa579b80b0c1705ab"
            ),
            "checkpoint_base_root": (
                "a9c5fd7d6f4e70ce4c0a6cd3f90c9355"
                "46bcc9c5ff573f4f9d93997677d632ee"
            ),
            "expected_root": (
                "cffbec6eac072caa55a121f4e21f4bc6"
                "ac9c13bb324470a8f8ff8ba04ab797f9"
            ),
            "actual_root": (
                "cffbec6eac072caa55a121f4e21f4bc6"
                "ac9c13bb324470a8f8ff8ba04ab797f9"
            ),
            "base_entries": 64,
            "checkpoint_entries": 5,
            "restored_entries": 69,
            "payload_bytes": 40,
            "prefix_lookup_steps": 2,
            "capture_operations": 5,
            "restore_operations": 5,
            "entry_limit": 1000,
            "payload_byte_limit": 64000,
            "expected_outcome": "restored",
            "actual_outcome": "restored",
            "elapsed_us": 2,
            "final_state": "verified",
        },
        {
            "schema": ENVIRONMENT_STATE_SCHEMA,
            "version": ENVIRONMENT_IDENTITY_VERSION,
            "run_id": identity_run_id,
            "beads": ["fln-amv.7"],
            "scenario": "checkpoint-roundtrip",
            "mode": "full_journal",
            "status": "pass",
            "base_id": None,
            "checkpoint_id": "v1-full-37-38b8cd0e43c2cb09",
            "restored_id": (
                "56b471fc08e0aaf91410cb01467c5a865"
                "23f6cfb0efd037c782c61818c6c988b"
            ),
            "base_root": None,
            "checkpoint_base_root": None,
            "expected_root": (
                "0af8c87b8a15bb34bc78108eadf4f6b0"
                "640051ba9678536bd17645d11263c131"
            ),
            "actual_root": (
                "0af8c87b8a15bb34bc78108eadf4f6b0"
                "640051ba9678536bd17645d11263c131"
            ),
            "base_entries": 0,
            "checkpoint_entries": 37,
            "restored_entries": 37,
            "payload_bytes": 296,
            "prefix_lookup_steps": 0,
            "capture_operations": 37,
            "restore_operations": 37,
            "entry_limit": 1000,
            "payload_byte_limit": 64000,
            "expected_outcome": "restored",
            "actual_outcome": "restored",
            "elapsed_us": 3,
            "final_state": "verified",
        },
        {
            "schema": ENVIRONMENT_STATE_SCHEMA,
            "version": ENVIRONMENT_IDENTITY_VERSION,
            "run_id": identity_run_id,
            "beads": ["fln-amv.7"],
            "scenario": "checkpoint-negative-recovery",
            "mode": "journal_suffix",
            "status": "pass",
            "base_id": (
                "c0f8dd130cf1f9eccd9dd575a0ee9ddd"
                "75654c7afd999ffcfbb1bb557ca2f203"
            ),
            "checkpoint_id": "v1-suffix-5-7567db5a9df19e29",
            "restored_id": (
                "8d00a22b42354950b09dc8f2e927c523"
                "7dc7357cbd2bec7985fff5770b753972"
            ),
            "base_root_before": (
                "525e3fa4730a11ab0cbc6c56d10282c3"
                "80cd0b043751888bb15174fd17df5bbc"
            ),
            "base_root_after": (
                "525e3fa4730a11ab0cbc6c56d10282c3"
                "80cd0b043751888bb15174fd17df5bbc"
            ),
            "expected_root": (
                "cffbec6eac072caa55a121f4e21f4bc6"
                "ac9c13bb324470a8f8ff8ba04ab797f9"
            ),
            "actual_root": (
                "cffbec6eac072caa55a121f4e21f4bc6"
                "ac9c13bb324470a8f8ff8ba04ab797f9"
            ),
            "base_entries": 64,
            "checkpoint_entries": 5,
            "restored_entries": 69,
            "entry_limit": 1000,
            "payload_byte_limit": 64000,
            "expected_outcome": "base_history_mismatch",
            "actual_outcome": "base_history_mismatch",
            "recovery_outcome": "restored",
            "elapsed_us": 4,
            "final_state": "clean_recovery",
        },
    ]
    state_stdout, state_stderr = write_identity_fixture(
        "environment_state_valid", environment_state_records
    )
    require(
        identity_validator_call(
            validate_environment_state,
            state_stdout,
            state_stderr,
        )["records"]
        == 4,
        "valid environment-state evidence was not accepted",
    )
    expect_identity_rejection(
        "environment_state_missing",
        validate_environment_state,
        environment_state_records[:-1],
    )
    state_extra = json.loads(json.dumps(environment_state_records))
    state_extra.append(json.loads(json.dumps(state_extra[-1])))
    expect_identity_rejection(
        "environment_state_extra",
        validate_environment_state,
        state_extra,
    )
    state_duplicate = json.loads(json.dumps(environment_state_records))
    state_duplicate[2] = json.loads(json.dumps(state_duplicate[1]))
    expect_identity_rejection(
        "environment_state_duplicate",
        validate_environment_state,
        state_duplicate,
    )
    state_swapped = json.loads(json.dumps(environment_state_records))
    state_swapped[1], state_swapped[2] = state_swapped[2], state_swapped[1]
    expect_identity_rejection(
        "environment_state_swapped",
        validate_environment_state,
        state_swapped,
    )
    state_wrong_collision = json.loads(json.dumps(environment_state_records))
    state_wrong_collision[3]["checkpoint_id"] = state_wrong_collision[2][
        "checkpoint_id"
    ]
    expect_identity_rejection(
        "environment_state_wrong_collision",
        validate_environment_state,
        state_wrong_collision,
    )
    state_stale = json.loads(json.dumps(environment_state_records))
    state_stale[3]["base_root_after"] = state_stale[1]["base_root"]
    expect_identity_rejection(
        "environment_state_stale",
        validate_environment_state,
        state_stale,
    )
    state_merged = json.loads(json.dumps(environment_state_records))
    state_merged[2]["run_id"] = "another-run"
    expect_identity_rejection(
        "environment_state_merged_stream",
        validate_environment_state,
        state_merged,
    )
    state_incomplete = json.loads(json.dumps(environment_state_records))
    del state_incomplete[3]["final_state"]
    expect_identity_rejection(
        "environment_state_incomplete",
        validate_environment_state,
        state_incomplete,
    )

    def declaration_admission_fixture(
        label: str,
    ) -> list[dict[str, Any]]:
        envelope = {
            "version": 1,
            "run_id": identity_run_id,
            "bead": "franken_lean-j8h",
            "claim_id": (
                "franken_lean-j8h-declaration-admission-resource-bounds"
            ),
            "claim_type": "bounded_model",
            "invariant_id": "FL-INV-07",
            "invariant_relation": "inconclusive-is-not-rejected",
            "gate_id": "W2",
            "gate_relation": "partial-component-evidence",
            "parity_ledger_row": (
                "not_applicable_internal_declaration_admission"
            ),
            "data_grade": "verified",
            "epoch": "lean-v4.32.0",
            "mode": "sound",
            "profile": "e2e",
            "platform": "linux-x86_64",
            "cache_state": "uncontrolled",
            "canonical_input_root": DECLARATION_ADMISSION_INPUT_ROOT,
            "cwd": "/tmp/self-test/crates/fln-env",
            "argv": [DECLARATION_ADMISSION_ARGV],
            "stdout_artifact": f"{label}.out",
            "stderr_artifact": f"{label}.err",
            "timing_used_as_gate": False,
        }

        def detail(
            scenario: str,
            step: str,
            step_index: int,
            declaration: str,
            final_state: str,
        ) -> dict[str, Any]:
            return {
                "schema": DECLARATION_ADMISSION_SCHEMA,
                **envelope,
                "scenario": scenario,
                "step": step,
                "step_index": step_index,
                "declaration": declaration,
                "status": "pass",
                "cleanup_status": "not_applicable",
                "final_state": final_state,
            }

        records: list[dict[str, Any]] = []
        records.append(
            {
                **detail(
                    "admitted-transaction",
                    "admitted",
                    0,
                    "Admitted",
                    "declaration-published-and-base-unchanged",
                ),
                "budget": dict(DECLARATION_ADMISSION_UNBOUNDED_BUDGET),
                "usage": {
                    "level_params": 2,
                    "mutual_rows": 0,
                    "constructor_rows": 0,
                    "recursor_rules": 0,
                    "canonical_bytes": 87,
                    "expressions": 1,
                    "expr_nodes": 1,
                    "expanded_weight": 1,
                    "max_logical_depth": 1,
                },
                "canonical_digest": (
                    "8de3ad5e3cb6525929228ad73fea85aa7"
                    "1b4685d32a4b647599c7e9e31f80291"
                ),
                "limit_name": None,
                "allowed": None,
                "observed": None,
                "structural_unit": None,
                "base_root": DECLARATION_ADMISSION_BASE_ROOT,
                "published_root": (
                    "4b6ce45719dce319af9c2bf24b3c12bf"
                    "012e194b49952173f35a9563690d6abf"
                ),
                "authoritative": True,
                "published": True,
                "cacheable": True,
                "expected_outcome": "admitted",
                "actual_outcome": "admitted",
                "first_divergence": None,
            }
        )
        for offset, expected in enumerate(DECLARATION_ADMISSION_REFUSALS):
            (
                limit_name,
                is_dimension,
                measured_by,
                observed,
                structural_unit,
                progress,
            ) = expected
            budget = dict(DECLARATION_ADMISSION_UNBOUNDED_BUDGET)
            budget[f"max_{limit_name}"] = 0
            records.append(
                {
                    **detail(
                        "limit-refusal",
                        f"refusal-{limit_name}",
                        offset + 1,
                        f"Refused{offset}",
                        "nothing-published-and-base-unchanged",
                    ),
                    "budget": budget,
                    "usage": None,
                    "canonical_digest": None,
                    "limit_name": limit_name,
                    "is_declaration_dimension": is_dimension,
                    "measured_by": measured_by,
                    "allowed": 0,
                    "observed": observed,
                    "structural_unit": structural_unit,
                    "progress": progress,
                    "base_root": DECLARATION_ADMISSION_BASE_ROOT,
                    "published_root": None,
                    "authoritative": False,
                    "published": False,
                    "cacheable": False,
                    "expected_outcome": "inconclusive-resource-exhausted",
                    "actual_outcome": "inconclusive-resource-exhausted",
                    "first_divergence": None,
                }
            )
        for step_index, step, checkpoint in (
            (8, "cancel-before-expression", "before-expression/0"),
            (9, "cancel-before-publication", "before-publication"),
        ):
            records.append(
                {
                    **detail(
                        "cancellation",
                        step,
                        step_index,
                        "Cancelled",
                        "nothing-published-and-base-unchanged",
                    ),
                    "checkpoint": checkpoint,
                    "base_root": DECLARATION_ADMISSION_BASE_ROOT,
                    "published_root": None,
                    "authoritative": False,
                    "published": False,
                    "cacheable": False,
                    "expected_outcome": "inconclusive-cancelled",
                    "actual_outcome": "inconclusive-cancelled",
                    "first_divergence": None,
                }
            )
        admitted_root = records[0]["published_root"]
        records.append(
            {
                **detail(
                    "superseded-plan",
                    "superseded-nonpublication",
                    10,
                    "Stale",
                    "nothing-published-and-target-unchanged",
                ),
                "plan_base_root": DECLARATION_ADMISSION_BASE_ROOT,
                "commit_target_root": admitted_root,
                "base_root": admitted_root,
                "published_root": None,
                "authoritative": False,
                "published": False,
                "cacheable": False,
                "expected_outcome": "inconclusive-authority-incomplete",
                "actual_outcome": "inconclusive-authority-incomplete",
                "first_divergence": "plan-base-differs-from-commit-target",
            }
        )
        for offset, expected in enumerate(DECLARATION_ADMISSION_RECOVERIES):
            limit_name, usage, digest, published_root = expected
            records.append(
                {
                    **detail(
                        "adequate-budget-recovery",
                        f"recovery-{limit_name}",
                        offset + 11,
                        f"Recovered{offset}",
                        "declaration-published-after-earlier-refusal",
                    ),
                    "budget": dict(DECLARATION_ADMISSION_UNBOUNDED_BUDGET),
                    "usage": usage,
                    "canonical_digest": digest,
                    "limit_name": limit_name,
                    "base_root": DECLARATION_ADMISSION_BASE_ROOT,
                    "published_root": published_root,
                    "authoritative": True,
                    "published": True,
                    "cacheable": True,
                    "expected_outcome": "admitted-after-refusal",
                    "actual_outcome": "admitted-after-refusal",
                    "first_divergence": None,
                }
            )
        records.append(
            {
                "schema": DECLARATION_ADMISSION_SUMMARY_SCHEMA,
                **envelope,
                "scenario": "declaration-admission-real-path",
                "steps": 18,
                "admitted_rows": 1,
                "refusal_rows": 7,
                "cancellation_rows": 2,
                "superseded_rows": 1,
                "recovery_rows": 7,
                "declaration_dimension_rows": 5,
                "delegated_limit_rows": 2,
                "status": "pass",
                "cleanup_status": "retained_by_policy",
                "final_state": (
                    "every-budgeted-limit-refused-typed-and-recovered"
                ),
            }
        )
        return records

    admission_valid = declaration_admission_fixture("admission_valid")
    admission_stdout, admission_stderr = write_identity_fixture(
        "admission_valid", admission_valid
    )
    require(
        identity_validator_call(
            validate_declaration_admission,
            admission_stdout,
            admission_stderr,
        )["records"]
        == 19,
        "valid declaration-admission evidence was not accepted",
    )
    admission_mutants: list[
        tuple[str, Callable[[list[dict[str, Any]]], None]]
    ] = [
        ("missing", lambda rows: rows.pop(17)),
        ("extra", lambda rows: rows.append(dict(rows[-1]))),
        ("duplicate", lambda rows: rows.__setitem__(2, dict(rows[1]))),
        (
            "reordered",
            lambda rows: rows.__setitem__(
                slice(1, 3), [dict(rows[2]), dict(rows[1])]
            ),
        ),
        (
            "stale",
            lambda rows: rows[8].__setitem__(
                "canonical_input_root", identity_hex(90_001)
            ),
        ),
        (
            "contradictory",
            lambda rows: rows[1].__setitem__(
                "actual_outcome", "rejected"
            ),
        ),
        (
            "summary_split",
            lambda rows: rows[-1].__setitem__(
                "declaration_dimension_rows", 7
            ),
        ),
    ]
    for mutant, mutate in admission_mutants:
        label = f"admission_{mutant}"
        mutant_records = declaration_admission_fixture(label)
        mutate(mutant_records)
        expect_identity_rejection(
            label,
            validate_declaration_admission,
            mutant_records,
        )
    expect_identity_rejection(
        "tag_stderr_leak",
        validate_declaration_tag_matrix,
        tag_records,
        stderr=canonical_json(tag_records[0]),
    )
    cases.append(
        {
            "case": "environment_identity_matrix_validation",
            "ok": True,
            "validators": 5,
            "mutants_killed": 20,
        }
    )

    collision_validation_root = case_dir("environment_collision_validation")
    collision_run_id = "collision-self-test"
    collision_cwd = str(art_dir)
    collision_argv = (
        "cargo test --locked -q -p fln-env "
        f"{ENVIRONMENT_COLLISION_TEST} -- --exact --nocapture"
    )
    collision_cache_state = "self-test-cache"
    canonical_order = list(range(ENVIRONMENT_COLLISION_CARDINALITY))

    def collision_detail_record(
        threads: int,
        start_us: int,
        stdout_artifact: str,
        stderr_artifact: str,
    ) -> dict[str, Any]:
        worker_orders = [
            environment_collision_insertion_order(
                ENVIRONMENT_COLLISION_CARDINALITY, threads, worker
            )
            for worker in range(threads)
        ]
        environment_root = "b" * 64
        return {
            "schema": ENVIRONMENT_COLLISION_SCHEMA,
            "version": ENVIRONMENT_COLLISION_VERSION,
            "run_id": collision_run_id,
            "bead": "fln-amv.10",
            "claim_id": "fln-amv.10-collision-canonicality",
            "claim_type": "bounded_model",
            "invariant_id": "FL-INV-01",
            "invariant_relation": "supports-local-pmap-slice",
            "gate_id": "PG-5",
            "gate_relation": "partial-component-evidence",
            "parity_ledger_row": "not_applicable_internal_data_structure_determinism",
            "data_grade": "verified",
            "epoch": "lean-v4.32.0",
            "mode": "sound",
            "profile": "e2e",
            "platform": "linux-x86_64",
            "seed": "partition-rotation-v1",
            "cache_state": collision_cache_state,
            "canonical_input_root": f"fln-fixture:{'a' * 64}",
            "scenario": "full-hash-collision-schedule-matrix",
            "schedule_id": f"partitioned-{threads}",
            "status": "pass",
            "cwd": collision_cwd,
            "argv": [collision_argv],
            "stdout_artifact": stdout_artifact,
            "stderr_artifact": stderr_artifact,
            "collision_cardinality": ENVIRONMENT_COLLISION_CARDINALITY,
            "collision_hash": "c" * 16,
            "threads": threads,
            "workers_built": threads,
            "distinct_insertion_orders": threads,
            "representative_insertion_order": worker_orders[0],
            "worker_insertion_orders": worker_orders,
            "expected_enumeration": canonical_order,
            "actual_enumeration": canonical_order,
            "worker_enumerations": [canonical_order for _ in range(threads)],
            "expected_root": environment_root,
            "actual_root": environment_root,
            "worker_roots": [environment_root for _ in range(threads)],
            "enumeration_insert_operations": ENVIRONMENT_COLLISION_CARDINALITY
            * threads,
            "environment_insert_operations": ENVIRONMENT_COLLISION_CARDINALITY
            * threads,
            "environment_duplicate_checks": ENVIRONMENT_COLLISION_CARDINALITY
            * threads,
            "observed_enumeration_nodes": [1 for _ in range(threads)],
            "observed_environment_entries": [
                ENVIRONMENT_COLLISION_CARDINALITY for _ in range(threads)
            ],
            "theoretical_fresh_node_bound_per_insert": 28,
            "theoretical_replaced_node_bound_per_insert": 14,
            "operation_budget": {
                "max_collision_cardinality": ENVIRONMENT_COLLISION_CARDINALITY,
                "thread_matrix": list(ENVIRONMENT_COLLISION_THREADS),
            },
            "bucket_policy": "PKey-Ord",
            "lookup_complexity": "O(bucket)",
            "insert_complexity": "O(log(bucket))-comparisons-plus-O(bucket)-clone-shift",
            "resource_followup": "fln-amv.13",
            "monotonic_start_us": start_us,
            "monotonic_end_us": start_us + 5,
            "duration_us": 5,
            "timing_used_as_gate": False,
            "process_exit": 0,
            "signal": None,
            "first_divergence": None,
            "cleanup_status": "retained_by_policy",
            "final_state": "canonical-enumeration-and-root-verified",
        }

    def collision_records_for(
        stdout_artifact: str, stderr_artifact: str
    ) -> list[dict[str, Any]]:
        return [
            collision_detail_record(
                threads,
                index * 10,
                stdout_artifact,
                stderr_artifact,
            )
            for index, threads in enumerate(ENVIRONMENT_COLLISION_THREADS)
        ]

    def collision_pass_log(records: list[dict[str, Any]]) -> bytes:
        return (
            b"running 1 test\n"
            + b"".join(canonical_json(record) for record in records)
            + b"test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured\n"
        )

    def collision_validate(
        stdout_path: Path,
        stderr_path: Path,
        phase: str,
        observed_exit: int,
        stdout_artifact: str,
        stderr_artifact: str,
    ) -> dict[str, Any]:
        return validate_environment_collision(
            stdout_path,
            stderr_path,
            phase,
            collision_run_id,
            observed_exit,
            artifact_root=collision_validation_root,
            expected_stdout_artifact=stdout_artifact,
            expected_stderr_artifact=stderr_artifact,
            expected_cwd=collision_cwd,
            expected_argv=collision_argv,
            expected_cache_state=collision_cache_state,
        )

    def expect_collision_rejection(
        label: str,
        stdout_path: Path,
        stderr_path: Path,
        phase: str,
        observed_exit: int,
        stdout_artifact: str,
        stderr_artifact: str,
        *,
        expected_message: str | None = None,
    ) -> None:
        try:
            collision_validate(
                stdout_path,
                stderr_path,
                phase,
                observed_exit,
                stdout_artifact,
                stderr_artifact,
            )
        except (EvidenceError, OSError) as error:
            if expected_message is not None:
                require(
                    expected_message in str(error),
                    f"{label} rejected for the wrong reason: {error}",
                )
        else:
            raise EvidenceError(f"{label} was accepted")

    collision_positive_stdout = "collision_positive.out"
    collision_positive_stderr = "collision_positive.err"
    collision_positive_records = collision_records_for(
        collision_positive_stdout, collision_positive_stderr
    )
    collision_positive_bytes = collision_pass_log(collision_positive_records)
    collision_positive = collision_validation_root / collision_positive_stdout
    collision_positive_err = collision_validation_root / collision_positive_stderr
    write_new(collision_positive, collision_positive_bytes)
    write_new(collision_positive_err, b"")
    collision_report = collision_validate(
        collision_positive,
        collision_positive_err,
        "positive",
        0,
        collision_positive_stdout,
        collision_positive_stderr,
    )
    require(
        collision_report["records"] == len(ENVIRONMENT_COLLISION_THREADS),
        "valid collision evidence lost schedule records",
    )
    require(
        hmac.compare_digest(
            collision_report["stdout_sha256"],
            hashlib.sha256(collision_positive_bytes).hexdigest(),
        )
        and hmac.compare_digest(
            collision_report["stderr_sha256"], hashlib.sha256(b"").hexdigest()
        ),
        "valid collision evidence lost its split-stream digests",
    )

    collision_recovery_stdout = "collision_recovery.out"
    collision_recovery_stderr = "collision_recovery.err"
    collision_recovery_records = collision_records_for(
        collision_recovery_stdout, collision_recovery_stderr
    )
    collision_recovery = collision_validation_root / collision_recovery_stdout
    collision_recovery_err = collision_validation_root / collision_recovery_stderr
    write_new(collision_recovery, collision_pass_log(collision_recovery_records))
    write_new(collision_recovery_err, b"warning: benign recovery diagnostic\n")
    collision_recovery_report = collision_validate(
        collision_recovery,
        collision_recovery_err,
        "recovery",
        0,
        collision_recovery_stdout,
        collision_recovery_stderr,
    )
    require(
        collision_recovery_report["phase"] == "recovery",
        "valid collision recovery evidence lost its phase identity",
    )

    collision_tampered_stdout = "collision_tampered.out"
    collision_tampered_stderr = "collision_tampered.err"
    tampered_records = parse_json(
        json.dumps(
            collision_records_for(
                collision_tampered_stdout, collision_tampered_stderr
            )
        ),
        subject="collision self-test copy",
    )
    tampered_records[1]["worker_insertion_orders"][0][0] = 999
    collision_tampered = collision_validation_root / "collision_tampered.out"
    collision_tampered_err = collision_validation_root / "collision_tampered.err"
    write_new(
        collision_tampered,
        collision_pass_log(tampered_records),
    )
    write_new(collision_tampered_err, b"")
    expect_collision_rejection(
        "tampered collision insertion schedule",
        collision_tampered,
        collision_tampered_err,
        "recovery",
        0,
        collision_tampered_stdout,
        collision_tampered_stderr,
        expected_message="worker insertion schedules differ",
    )

    collision_renamed = collision_validation_root / "collision_positive_renamed.out"
    write_new(collision_renamed, collision_positive_bytes)
    expect_collision_rejection(
        "renamed collision stdout",
        collision_renamed,
        collision_positive_err,
        "positive",
        0,
        collision_positive_stdout,
        collision_positive_stderr,
        expected_message="stdout path",
    )
    expect_collision_rejection(
        "swapped collision streams",
        collision_positive_err,
        collision_positive,
        "positive",
        0,
        collision_positive_stderr,
        collision_positive_stdout,
        expected_message="detail rows leaked into stderr",
    )
    expect_collision_rejection(
        "missing collision stderr",
        collision_positive,
        collision_validation_root / "collision_missing.err",
        "positive",
        0,
        collision_positive_stdout,
        "collision_missing.err",
    )

    collision_failure_stdout = "collision_positive_failure.out"
    collision_failure_stderr = "collision_positive_failure.err"
    collision_failure_out = collision_validation_root / collision_failure_stdout
    collision_failure_err = collision_validation_root / collision_failure_stderr
    write_new(
        collision_failure_out,
        collision_pass_log(
            collision_records_for(
                collision_failure_stdout, collision_failure_stderr
            )
        ),
    )
    write_new(
        collision_failure_err,
        b"test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured\n",
    )
    expect_collision_rejection(
        "passing collision stderr with failure material",
        collision_failure_out,
        collision_failure_err,
        "positive",
        0,
        collision_failure_stdout,
        collision_failure_stderr,
        expected_message="stderr contains failure material",
    )

    collision_mutant_stdout = "collision_mutant.out"
    collision_mutant_stderr = "collision_mutant.err"
    collision_mutant = collision_validation_root / collision_mutant_stdout
    collision_mutant_err = collision_validation_root / collision_mutant_stderr
    mutant_stdout_bytes = (
        "running 1 test\n"
        f"{ENVIRONMENT_COLLISION_TEST} --- FAILED\n\n"
        "failures:\n"
        f"    {ENVIRONMENT_COLLISION_TEST}\n\n"
        "test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured\n"
    ).encode()
    mutant_stderr_bytes = (
        "thread 'pmap::tests::environment_collision_e2e_emits_detailed_real_path_evidence' "
        "panicked at crates/fln-env/src/pmap.rs:1:1:\n"
        "assertion `left == right` failed: "
        f"{ENVIRONMENT_COLLISION_MUTANT_MARKER}\n"
        "  left: [95, 94, 93]\n"
        " right: [0, 1, 2]\n"
        "error: test failed, to rerun pass `-p fln-env --lib`\n"
    ).encode()
    write_new(collision_mutant, mutant_stdout_bytes)
    write_new(collision_mutant_err, mutant_stderr_bytes)
    mutant_report = collision_validate(
        collision_mutant,
        collision_mutant_err,
        "mutant",
        101,
        collision_mutant_stdout,
        collision_mutant_stderr,
    )
    require(
        mutant_report["failed_test"] == ENVIRONMENT_COLLISION_TEST,
        "collision mutant validation lost the failed test identity",
    )
    require(
        hmac.compare_digest(
            mutant_report["stdout_sha256"],
            hashlib.sha256(mutant_stdout_bytes).hexdigest(),
        )
        and hmac.compare_digest(
            mutant_report["stderr_sha256"],
            hashlib.sha256(mutant_stderr_bytes).hexdigest(),
        ),
        "collision mutant validation lost its split-stream digests",
    )

    collision_wrong_assertion = collision_validation_root / "collision_wrong_assertion.err"
    write_new(
        collision_wrong_assertion,
        mutant_stderr_bytes.replace(
            ENVIRONMENT_COLLISION_MUTANT_MARKER.encode(), b"threads=1"
        ),
    )
    expect_collision_rejection(
        "wrong same-test collision assertion",
        collision_mutant,
        collision_wrong_assertion,
        "mutant",
        101,
        collision_mutant_stdout,
        "collision_wrong_assertion.err",
        expected_message="intended enumeration assertion marker",
    )

    collision_false_kill_stdout = "collision_false_kill.out"
    collision_false_kill_stderr = "collision_false_kill.err"
    collision_false_kill = collision_validation_root / collision_false_kill_stdout
    collision_false_kill_err = collision_validation_root / collision_false_kill_stderr
    write_new(collision_false_kill, b"running 0 tests\n")
    write_new(collision_false_kill_err, b"error: could not compile `fln-env`\n")
    expect_collision_rejection(
        "unrelated split-stream collision failure",
        collision_false_kill,
        collision_false_kill_err,
        "mutant",
        101,
        collision_false_kill_stdout,
        collision_false_kill_stderr,
        expected_message="named FAILED test result",
    )

    collision_merged_stdout = "collision_mutant_merged.out"
    collision_merged_stderr = "collision_mutant_merged.err"
    collision_merged = collision_validation_root / collision_merged_stdout
    collision_merged_err = collision_validation_root / collision_merged_stderr
    write_new(collision_merged, mutant_stdout_bytes + mutant_stderr_bytes)
    write_new(collision_merged_err, b"")
    expect_collision_rejection(
        "merged collision mutant streams",
        collision_merged,
        collision_merged_err,
        "mutant",
        101,
        collision_merged_stdout,
        collision_merged_stderr,
        expected_message="assertion marker leaked into stdout",
    )
    cases.append(
        {
            "case": "environment_collision_validation",
            "ok": True,
            "positive": str(collision_positive),
            "mutant": str(collision_mutant),
            "mutant_stderr": str(collision_mutant_err),
        }
    )

    resource_validation_root = case_dir(
        "environment_resource_collision_validation"
    )
    resource_run_id = "resource-collision-self-test"
    resource_cwd = str(art_dir)
    resource_argv = (
        "cargo test --locked -q -p fln-env "
        f"{ENVIRONMENT_RESOURCE_COLLISION_TEST} -- --exact --nocapture"
    )
    resource_cache_state = "self-test-cache"
    resource_order = list(range(ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY))

    def resource_detail_record(
        threads: int,
        start_us: int,
        stdout_artifact: str,
        stderr_artifact: str,
    ) -> dict[str, Any]:
        return {
            "schema": ENVIRONMENT_RESOURCE_COLLISION_SCHEMA,
            "version": ENVIRONMENT_RESOURCE_COLLISION_VERSION,
            "run_id": resource_run_id,
            "bead": "fln-amv.13",
            "claim_id": "fln-amv.13-resource-bounded-collisions",
            "claim_type": "bounded_model",
            "invariant_id": "FL-INV-01",
            "invariant_relation": "supports-local-pmap-slice",
            "gate_id": "PG-5",
            "gate_relation": "partial-component-evidence",
            "parity_ledger_row": (
                "not_applicable_internal_data_structure_resource_bound"
            ),
            "data_grade": "verified",
            "epoch": "lean-v4.32.0",
            "mode": "sound",
            "profile": "e2e",
            "platform": "linux-x86_64",
            "seed": "partition-rotation-v1",
            "cache_state": resource_cache_state,
            "canonical_input_root": ENVIRONMENT_RESOURCE_COLLISION_INPUT_ROOT,
            "scenario": "collision-resource-schedule-matrix",
            "schedule_id": f"partitioned-{threads}",
            "status": "pass",
            "cwd": resource_cwd,
            "argv": [resource_argv],
            "stdout_artifact": stdout_artifact,
            "stderr_artifact": stderr_artifact,
            "collision_cardinality": ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY,
            "collision_hash": ENVIRONMENT_RESOURCE_COLLISION_HASH,
            "threads": threads,
            "workers_built": threads,
            "distinct_insertion_orders": threads,
            "representative_insertion_order": (
                environment_collision_insertion_order(
                    ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY, threads, 0
                )
            ),
            "worker_insertion_order_roots": list(
                ENVIRONMENT_RESOURCE_COLLISION_INSERTION_ROOTS[threads]
            ),
            "expected_order": resource_order,
            "actual_order": resource_order,
            "worker_enumeration_roots": [
                ENVIRONMENT_RESOURCE_COLLISION_INPUT_ROOT
            ]
            * threads,
            "expected_root": ENVIRONMENT_RESOURCE_COLLISION_ROOT,
            "actual_root": ENVIRONMENT_RESOURCE_COLLISION_ROOT,
            "worker_roots": [ENVIRONMENT_RESOURCE_COLLISION_ROOT] * threads,
            "expected_recovery_root": ENVIRONMENT_RESOURCE_COLLISION_RECOVERY_ROOT,
            "actual_recovery_root": ENVIRONMENT_RESOURCE_COLLISION_RECOVERY_ROOT,
            "worker_recovery_roots": [
                ENVIRONMENT_RESOURCE_COLLISION_RECOVERY_ROOT
            ]
            * threads,
            "representation_tier": "persistent-avl",
            "secondary_identity": "exact-PKey-Ord-with-Eq-consistency",
            "secondary_hashing": "none",
            "secondary_identity_collision_behavior": (
                "Ord-equal-overwrites;Ord-distinct-path-copies"
            ),
            "promotion_cardinality": 9,
            "demotion_cardinality": 8,
            "comparisons": [9_000] * threads,
            "fresh_map_nodes": [
                ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY
            ]
            * threads,
            "fresh_collision_nodes": [11_000] * threads,
            "cloned_inline_entries": [36] * threads,
            "final_collision_nodes": [
                ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY
            ]
            * threads,
            "snapshot_root_arc_bumps": [1] * threads,
            "snapshot_shared_collision_nodes": [
                ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY
            ]
            * threads,
            "append_shared_collision_nodes": [990] * threads,
            "append_fresh_nodes": [12] * threads,
            "max_lookup_comparisons": [11] * threads,
            "budget": {
                "max_collision_entries": (
                    ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY + 1
                ),
                "max_expanded_weight": (
                    ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY + 1
                ),
                "admission_max_fresh_nodes": [18] * threads,
                "refusal_max_fresh_nodes": [17] * threads,
                "refusal_resource": "FreshNodes",
                "refusal_attempted": [18] * threads,
                "failure_atomic": True,
                "exact_boundary_recovery": True,
            },
            "bounds": {
                "construction_comparisons": 18_000,
                "inline_cloned_entries": 36,
                "append_minimum_shared_nodes": 983,
                "lookup_comparisons": 14,
                "maximum_avl_height": 14,
                "tree_fresh_nodes_per_insert": 17,
                "legacy_vector_copies": 499_500,
            },
            "resources": {
                "expanded_weight": ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY,
                "environment_entries": (
                    ENVIRONMENT_RESOURCE_COLLISION_CARDINALITY
                ),
                "timing_used_as_gate": False,
            },
            "monotonic_start_us": start_us,
            "monotonic_end_us": start_us + 5,
            "duration_us": 5,
            "timing_used_as_gate": False,
            "process_exit": 0,
            "signal": None,
            "first_divergence": None,
            "cleanup_status": "retained_by_policy",
            "final_state": "typed-refusal-followed-by-exact-bound-recovery",
        }

    def resource_records_for(
        stdout_artifact: str, stderr_artifact: str
    ) -> list[dict[str, Any]]:
        return [
            resource_detail_record(
                threads, index * 10, stdout_artifact, stderr_artifact
            )
            for index, threads in enumerate(
                ENVIRONMENT_RESOURCE_COLLISION_THREADS
            )
        ]

    def resource_pass_log(records: list[dict[str, Any]]) -> bytes:
        return (
            b"running 1 test\n"
            + b"".join(canonical_json(record) for record in records)
            + b"test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured\n"
        )

    def resource_validate(
        stdout_path: Path,
        stderr_path: Path,
        phase: str,
        observed_exit: int,
        stdout_artifact: str,
        stderr_artifact: str,
    ) -> dict[str, Any]:
        return validate_environment_resource_collision(
            stdout_path,
            stderr_path,
            phase,
            resource_run_id,
            observed_exit,
            artifact_root=resource_validation_root,
            expected_stdout_artifact=stdout_artifact,
            expected_stderr_artifact=stderr_artifact,
            expected_cwd=resource_cwd,
            expected_argv=resource_argv,
            expected_cache_state=resource_cache_state,
        )

    def expect_resource_rejection(
        label: str,
        stdout_path: Path,
        stderr_path: Path,
        phase: str,
        observed_exit: int,
        stdout_artifact: str,
        stderr_artifact: str,
        *,
        expected_message: str | None = None,
    ) -> None:
        try:
            resource_validate(
                stdout_path,
                stderr_path,
                phase,
                observed_exit,
                stdout_artifact,
                stderr_artifact,
            )
        except (EvidenceError, OSError) as error:
            if expected_message is not None:
                require(
                    expected_message in str(error),
                    f"{label} rejected for the wrong reason: {error}",
                )
        else:
            raise EvidenceError(f"{label} was accepted")

    resource_positive_stdout = "resource_positive.out"
    resource_positive_stderr = "resource_positive.err"
    resource_positive_records = resource_records_for(
        resource_positive_stdout, resource_positive_stderr
    )
    resource_positive_bytes = resource_pass_log(resource_positive_records)
    resource_positive = resource_validation_root / resource_positive_stdout
    resource_positive_err = resource_validation_root / resource_positive_stderr
    write_new(resource_positive, resource_positive_bytes)
    write_new(resource_positive_err, b"")
    resource_report = resource_validate(
        resource_positive,
        resource_positive_err,
        "positive",
        0,
        resource_positive_stdout,
        resource_positive_stderr,
    )
    require(
        resource_report["records"]
        == len(ENVIRONMENT_RESOURCE_COLLISION_THREADS),
        "valid resource-collision evidence lost schedule records",
    )
    require(
        resource_report["canonical_input_root"]
        == ENVIRONMENT_RESOURCE_COLLISION_INPUT_ROOT
        and resource_report["environment_root"]
        == ENVIRONMENT_RESOURCE_COLLISION_ROOT
        and resource_report["recovery_root"]
        == ENVIRONMENT_RESOURCE_COLLISION_RECOVERY_ROOT,
        "valid resource-collision evidence lost its pinned roots",
    )

    resource_recovery_stdout = "resource_recovery.out"
    resource_recovery_stderr = "resource_recovery.err"
    resource_recovery = resource_validation_root / resource_recovery_stdout
    resource_recovery_err = resource_validation_root / resource_recovery_stderr
    write_new(
        resource_recovery,
        resource_pass_log(
            resource_records_for(
                resource_recovery_stdout, resource_recovery_stderr
            )
        ),
    )
    write_new(resource_recovery_err, b"warning: benign recovery diagnostic\n")
    recovery_report = resource_validate(
        resource_recovery,
        resource_recovery_err,
        "recovery",
        0,
        resource_recovery_stdout,
        resource_recovery_stderr,
    )
    require(
        recovery_report["phase"] == "recovery",
        "valid resource-collision recovery lost its phase identity",
    )

    def resource_record_rejection(
        label: str,
        mutation: Callable[[list[dict[str, Any]]], None],
        expected_message: str,
    ) -> None:
        stdout_artifact = f"resource_{label}.out"
        stderr_artifact = f"resource_{label}.err"
        records = parse_json(
            json.dumps(resource_records_for(stdout_artifact, stderr_artifact)),
            subject=f"resource-collision self-test {label}",
        )
        mutation(records)
        stdout_path = resource_validation_root / stdout_artifact
        stderr_path = resource_validation_root / stderr_artifact
        write_new(stdout_path, resource_pass_log(records))
        write_new(stderr_path, b"")
        expect_resource_rejection(
            label,
            stdout_path,
            stderr_path,
            "positive",
            0,
            stdout_artifact,
            stderr_artifact,
            expected_message=expected_message,
        )

    resource_record_rejection(
        "missing_field",
        lambda records: records[0].pop("resources"),
        "field mismatch",
    )
    resource_record_rejection(
        "extra_field",
        lambda records: records[0].__setitem__("unexpected", True),
        "field mismatch",
    )
    resource_record_rejection(
        "stale_input_root",
        lambda records: records[0].__setitem__(
            "canonical_input_root", f"fln-fixture:{'0' * 64}"
        ),
        "canonical_input_root",
    )
    resource_record_rejection(
        "stale_environment_root",
        lambda records: records[0].__setitem__("actual_root", "0" * 64),
        "actual_root",
    )
    resource_record_rejection(
        "wrong_order",
        lambda records: records[1].__setitem__(
            "actual_order", list(reversed(resource_order))
        ),
        "actual order is not canonical",
    )
    resource_record_rejection(
        "duplicate_schedule",
        lambda records: records[1]["worker_insertion_order_roots"].__setitem__(
            1, records[1]["worker_insertion_order_roots"][0]
        ),
        "worker insertion roots differ",
    )
    resource_record_rejection(
        "wrong_threshold",
        lambda records: records[0].__setitem__("promotion_cardinality", 10),
        "promotion_cardinality",
    )
    resource_record_rejection(
        "comparison_over_bound",
        lambda records: records[2]["comparisons"].__setitem__(0, 18_001),
        "comparison bound exceeded",
    )
    resource_record_rejection(
        "allocation_over_bound",
        lambda records: records[2]["append_fresh_nodes"].__setitem__(0, 19),
        "append allocation bound exceeded",
    )
    resource_record_rejection(
        "false_atomicity",
        lambda records: records[0]["budget"].__setitem__(
            "failure_atomic", False
        ),
        "not failure-atomic",
    )
    resource_record_rejection(
        "timing_gate",
        lambda records: records[0].__setitem__("timing_used_as_gate", True),
        "timing was promoted to a gate",
    )

    resource_mutant_stdout = "resource_mutant.out"
    resource_mutant_stderr = "resource_mutant.err"
    resource_mutant = resource_validation_root / resource_mutant_stdout
    resource_mutant_err = resource_validation_root / resource_mutant_stderr
    resource_mutant_stdout_bytes = (
        "running 1 test\n"
        f"{ENVIRONMENT_RESOURCE_COLLISION_TEST} --- FAILED\n\n"
        "failures:\n"
        f"    {ENVIRONMENT_RESOURCE_COLLISION_TEST}\n\n"
        "test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured\n"
    ).encode()
    resource_mutant_stderr_bytes = (
        f"thread '{ENVIRONMENT_RESOURCE_COLLISION_TEST}' "
        "panicked at crates/fln-env/src/pmap.rs:3222:17:\n"
        f"{ENVIRONMENT_RESOURCE_COLLISION_MUTANT_MARKER}\n"
        "error: test failed, to rerun pass `-p fln-env --lib`\n"
    ).encode()
    write_new(resource_mutant, resource_mutant_stdout_bytes)
    write_new(resource_mutant_err, resource_mutant_stderr_bytes)
    resource_mutant_report = resource_validate(
        resource_mutant,
        resource_mutant_err,
        "mutant",
        101,
        resource_mutant_stdout,
        resource_mutant_stderr,
    )
    require(
        resource_mutant_report["failed_test"]
        == ENVIRONMENT_RESOURCE_COLLISION_TEST,
        "resource-collision mutant validation lost the failed test identity",
    )

    resource_wrong_assertion = (
        resource_validation_root / "resource_wrong_assertion.err"
    )
    write_new(
        resource_wrong_assertion,
        resource_mutant_stderr_bytes.replace(b"left: 28", b"left: 27"),
    )
    expect_resource_rejection(
        "wrong resource-collision assertion",
        resource_mutant,
        resource_wrong_assertion,
        "mutant",
        101,
        resource_mutant_stdout,
        "resource_wrong_assertion.err",
        expected_message="inline-threshold assertion marker",
    )

    resource_missing_marker = (
        resource_validation_root / "resource_missing_marker.err"
    )
    write_new(
        resource_missing_marker,
        resource_mutant_stderr_bytes.replace(
            ENVIRONMENT_RESOURCE_COLLISION_MUTANT_MARKER.encode(),
            b"assertion failed without the planted threshold signature",
        ),
    )
    expect_resource_rejection(
        "missing resource-collision mutant marker",
        resource_mutant,
        resource_missing_marker,
        "mutant",
        101,
        resource_mutant_stdout,
        "resource_missing_marker.err",
        expected_message="inline-threshold assertion marker",
    )

    resource_compile_stdout = "resource_compile_failure.out"
    resource_compile_stderr = "resource_compile_failure.err"
    resource_compile = resource_validation_root / resource_compile_stdout
    resource_compile_err = resource_validation_root / resource_compile_stderr
    write_new(resource_compile, b"running 0 tests\n")
    write_new(
        resource_compile_err, b"error: could not compile `fln-env` (lib test)\n"
    )
    expect_resource_rejection(
        "resource-collision compile failure",
        resource_compile,
        resource_compile_err,
        "mutant",
        101,
        resource_compile_stdout,
        resource_compile_stderr,
        expected_message="named FAILED test result",
    )

    resource_merged_stdout = "resource_merged.out"
    resource_merged_stderr = "resource_merged.err"
    resource_merged = resource_validation_root / resource_merged_stdout
    resource_merged_err = resource_validation_root / resource_merged_stderr
    write_new(
        resource_merged,
        resource_mutant_stdout_bytes + resource_mutant_stderr_bytes,
    )
    write_new(resource_merged_err, b"")
    expect_resource_rejection(
        "merged resource-collision streams",
        resource_merged,
        resource_merged_err,
        "mutant",
        101,
        resource_merged_stdout,
        resource_merged_stderr,
        expected_message="assertion marker leaked into stdout",
    )
    expect_resource_rejection(
        "surviving resource-collision mutant",
        resource_positive,
        resource_positive_err,
        "mutant",
        0,
        resource_positive_stdout,
        resource_positive_stderr,
        expected_message="mutant exit 0",
    )
    cases.append(
        {
            "case": "environment_resource_collision_validation",
            "ok": True,
            "positive": str(resource_positive),
            "mutant": str(resource_mutant),
            "recovery": str(resource_recovery),
            "negative_cases": 16,
        }
    )

    admission_validation_root = case_dir("kernel_admission_validation")
    admission_run_id = "kernel-admission-self-test"
    admission_cwd = str(art_dir)
    admission_argv = (
        "cargo test --locked -q -p fln-conformance --test kernel_replay -- --nocapture"
    )
    admission_cache_state = "self-test-cache"
    admission_input_root = f"fln-fixture:{'a' * 64}"
    admission_digest = "d" * 64
    admission_env_root = "e" * 64

    def admission_common(
        stdout_artifact: str, stderr_artifact: str, start_us: int
    ) -> dict[str, Any]:
        return {
            "version": KERNEL_ADMISSION_VERSION,
            "run_id": admission_run_id,
            "bead": "franken_lean-ap6",
            "claim_type": "bounded_model",
            "invariant_relation": "single-authority-admission",
            "determinism_invariant": "FL-INV-01",
            "gate_id": "G1",
            "gate_relation": "partial-component-evidence",
            "parity_ledger_row": "init-prelude-admission-replay",
            "data_grade": "verified",
            "epoch": "lean-v4.32.0",
            "mode": "sound",
            "profile": "e2e",
            "platform": "linux-x86_64",
            "seed": "module-order-kahn-v1",
            "cache_state": admission_cache_state,
            "canonical_input_root": admission_input_root,
            "status": "pass",
            "cwd": admission_cwd,
            "argv": [admission_argv],
            "stdout_artifact": stdout_artifact,
            "stderr_artifact": stderr_artifact,
            "budget_steps": KERNEL_ADMISSION_BUDGET_STEPS,
            "budget_depth": KERNEL_ADMISSION_BUDGET_DEPTH,
            "monotonic_start_us": start_us,
            "monotonic_end_us": start_us + 5,
            "duration_us": 5,
            "timing_used_as_gate": False,
            "process_exit": 0,
            "signal": None,
            "first_divergence": None,
            "cleanup_status": "retained_by_policy",
        }

    def admission_matrix_record(
        phase: str,
        threads: int,
        stdout_artifact: str,
        stderr_artifact: str,
        start_us: int,
    ) -> dict[str, Any]:
        record = admission_common(stdout_artifact, stderr_artifact, start_us)
        record.update(
            {
                "schema": KERNEL_ADMISSION_SCHEMA,
                "claim_id": "franken_lean-ap6-admission-determinism",
                "invariant_id": "FL-INV-02",
                "scenario": "init-prelude-admission-thread-matrix",
                "phase": phase,
                "threads": threads,
                "units_total": 1915,
                "units_checked": 1909,
                "units_cyclic": 4,
                "verdict_stream_digest": admission_digest,
                "final_logical_root": admission_env_root,
                "steps_used_total": 2_694_649,
                "max_depth_seen": 132,
                "artifact_incomplete_witness": KERNEL_ADMISSION_ARTIFACT_WITNESS,
                "final_state": (
                    "byte-identical-across-1-8-32"
                    if phase == "matrix-identity"
                    else "verdict-stream-merged-canonical-order"
                ),
            }
        )
        record.update(KERNEL_ADMISSION_CENSUS)
        return record

    def admission_artifact_record(
        row: tuple[str, str, tuple[str, ...]],
        stdout_artifact: str,
        stderr_artifact: str,
    ) -> dict[str, Any]:
        declaration, safety, missing = row
        record = admission_common(stdout_artifact, stderr_artifact, 0)
        for absent in (
            "status",
            "budget_steps",
            "budget_depth",
            "monotonic_start_us",
            "monotonic_end_us",
            "duration_us",
            "timing_used_as_gate",
            "process_exit",
            "signal",
            "first_divergence",
            "cleanup_status",
        ):
            record.pop(absent, None)
        record.update(
            {
                "schema": KERNEL_ADMISSION_SCHEMA,
                "claim_id": "franken_lean-sgt-artifact-completeness",
                "invariant_id": "FL-INV-07",
                "scenario": "init-prelude-artifact-incomplete-census",
                "phase": "artifact-incomplete-row",
                "declaration": declaration,
                "safety": safety,
                "missing_references": list(missing),
                "witness": KERNEL_ADMISSION_ARTIFACT_WITNESS,
                "outcome": "inconclusive-artifact-incomplete",
                "authority": "none",
                "kernel_checked": False,
                "cacheable": False,
                "environment_admissible": False,
                "evidence_grade": "verified",
            }
        )
        return record

    def admission_fault_record(
        phase: str,
        mutant_id: str | None,
        invariant_id: str,
        actual_outcome: str,
        final_state: str,
        stdout_artifact: str,
        stderr_artifact: str,
        start_us: int,
        *,
        budget_steps: int = KERNEL_ADMISSION_BUDGET_STEPS,
        budget_depth: int = KERNEL_ADMISSION_BUDGET_DEPTH,
        recovery_outcome: str | None = "accepted",
    ) -> dict[str, Any]:
        record = admission_common(stdout_artifact, stderr_artifact, start_us)
        record.update(
            {
                "schema": KERNEL_ADMISSION_FAULT_SCHEMA,
                "claim_id": "franken_lean-ap6-admission-fault-matrix",
                "invariant_id": invariant_id,
                "scenario": "kernel-admission-fault-matrix",
                "phase": phase,
                "mutant_id": mutant_id,
                "target": "self-test-target",
                "expected_outcome": "rejected" if mutant_id else actual_outcome,
                "actual_outcome": actual_outcome,
                "reject_class": "BlockMismatch" if mutant_id else None,
                "message_excerpt": "self-test excerpt",
                "budget_steps": budget_steps,
                "budget_depth": budget_depth,
                "steps_used": 10,
                "max_depth": 1,
                "root_before": "f" * 64,
                "root_after": "f" * 64,
                "atomicity_held": True,
                "recovery_outcome": recovery_outcome,
                "final_state": final_state,
            }
        )
        return record

    def admission_records_for(
        stdout_artifact: str, stderr_artifact: str
    ) -> list[dict[str, Any]]:
        records: list[dict[str, Any]] = []
        clock = 0
        for threads in KERNEL_ADMISSION_THREADS:
            records.append(
                admission_matrix_record(
                    f"matrix-threads-{threads}",
                    threads,
                    stdout_artifact,
                    stderr_artifact,
                    clock,
                )
            )
            clock += 10
        records.append(
            admission_matrix_record(
                "matrix-identity", 1, stdout_artifact, stderr_artifact, clock
            )
        )
        clock += 10
        for row in KERNEL_ADMISSION_ARTIFACT_ROWS:
            records.append(
                admission_artifact_record(row, stdout_artifact, stderr_artifact)
            )
        for mutant in KERNEL_ADMISSION_MUTANTS:
            records.append(
                admission_fault_record(
                    f"mutant:{mutant}",
                    mutant,
                    "FL-INV-02",
                    "rejected",
                    "mutant-killed-typed-rejection",
                    stdout_artifact,
                    stderr_artifact,
                    clock,
                )
            )
            clock += 10
        resource_budgets = {
            "resource_boundary_exact_accept": (127, KERNEL_ADMISSION_BUDGET_DEPTH),
            "resource_exhaustion_steps": (126, KERNEL_ADMISSION_BUDGET_DEPTH),
            "resource_exhaustion_depth": (KERNEL_ADMISSION_BUDGET_STEPS, 2),
            "resource_recovery": (
                KERNEL_ADMISSION_BUDGET_STEPS,
                KERNEL_ADMISSION_BUDGET_DEPTH,
            ),
        }
        for resource_phase, outcome in KERNEL_ADMISSION_RESOURCE_PHASES.items():
            steps, depth = resource_budgets[resource_phase]
            records.append(
                admission_fault_record(
                    resource_phase,
                    None,
                    "FL-INV-07",
                    outcome,
                    f"self-test-{resource_phase}",
                    stdout_artifact,
                    stderr_artifact,
                    clock,
                    budget_steps=steps,
                    budget_depth=depth,
                    recovery_outcome=None,
                )
            )
            clock += 10
        return records

    def admission_pass_log(records: list[dict[str, Any]]) -> bytes:
        return (
            b"running 2 tests\n"
            + b"".join(canonical_json(record) for record in records)
            + b"test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured\n"
        )

    admission_stderr_bytes = (
        b"kernel_replay order: 1915 units over 2204 declarations\n"
        b"kernel_replay census: checked=2198 accepted=2198 inconclusive=0 "
        b"rejected={} unchecked={} artifact_incomplete=6 "
        b"artifact_incomplete_witness="
        + KERNEL_ADMISSION_ARTIFACT_WITNESS.encode("ascii")
        + b" nested_partial_blocks=0 nested_full_blocks=1\n"
    )

    def admission_validate(
        stdout_path: Path,
        stderr_path: Path,
        phase: str,
        observed_exit: int,
        stdout_artifact: str,
        stderr_artifact: str,
        *,
        expected_input_root: str | None = None,
    ) -> dict[str, Any]:
        return validate_kernel_admission(
            stdout_path,
            stderr_path,
            phase,
            admission_run_id,
            observed_exit,
            artifact_root=admission_validation_root,
            expected_stdout_artifact=stdout_artifact,
            expected_stderr_artifact=stderr_artifact,
            expected_cwd=admission_cwd,
            expected_argv=admission_argv,
            expected_cache_state=admission_cache_state,
            expected_input_root=expected_input_root,
        )

    def write_admission_case(
        name: str,
        mutate: Callable[[list[dict[str, Any]]], None] | None = None,
        *,
        stdout_bytes: bytes | None = None,
        stderr_bytes: bytes | None = None,
    ) -> tuple[Path, Path, str, str]:
        stdout_artifact = f"{name}.out"
        stderr_artifact = f"{name}.err"
        records = parse_json(
            json.dumps(admission_records_for(stdout_artifact, stderr_artifact)),
            subject="kernel-admission self-test copy",
        )
        if mutate is not None:
            mutate(records)
        stdout_file = admission_validation_root / stdout_artifact
        stderr_file = admission_validation_root / stderr_artifact
        write_new(
            stdout_file,
            admission_pass_log(records) if stdout_bytes is None else stdout_bytes,
        )
        write_new(
            stderr_file,
            admission_stderr_bytes if stderr_bytes is None else stderr_bytes,
        )
        return stdout_file, stderr_file, stdout_artifact, stderr_artifact

    def expect_admission_rejection(
        label: str,
        name: str,
        mutate: Callable[[list[dict[str, Any]]], None] | None = None,
        *,
        stdout_bytes: bytes | None = None,
        stderr_bytes: bytes | None = None,
        expected_message: str | None = None,
        expected_input_root: str | None = None,
    ) -> None:
        stdout_file, stderr_file, stdout_artifact, stderr_artifact = (
            write_admission_case(
                name, mutate, stdout_bytes=stdout_bytes, stderr_bytes=stderr_bytes
            )
        )
        try:
            admission_validate(
                stdout_file,
                stderr_file,
                "positive",
                0,
                stdout_artifact,
                stderr_artifact,
                expected_input_root=expected_input_root,
            )
        except (EvidenceError, OSError) as error:
            if expected_message is not None:
                require(
                    expected_message in str(error),
                    f"{label} rejected for the wrong reason: {error}",
                )
        else:
            raise EvidenceError(f"{label} was accepted")

    admission_positive_out, admission_positive_err, admission_pos_a, admission_pos_b = (
        write_admission_case("admission_positive")
    )
    admission_report = admission_validate(
        admission_positive_out,
        admission_positive_err,
        "positive",
        0,
        admission_pos_a,
        admission_pos_b,
    )
    require(
        admission_report["matrix_records"] == len(KERNEL_ADMISSION_THREADS) + 1
        and admission_report["fault_records"]
        == len(KERNEL_ADMISSION_MUTANTS) + len(KERNEL_ADMISSION_RESOURCE_PHASES)
        and admission_report["artifact_incomplete_records"]
        == len(KERNEL_ADMISSION_ARTIFACT_ROWS)
        and admission_report["artifact_incomplete_witness"]
        == KERNEL_ADMISSION_ARTIFACT_WITNESS
        and sorted(admission_report["mutants_killed"])
        == sorted(KERNEL_ADMISSION_MUTANTS),
        "valid kernel-admission evidence lost its records",
    )
    admission_recovery_out, admission_recovery_err, admission_rec_a, admission_rec_b = (
        write_admission_case("admission_recovery")
    )
    admission_recovery_report = admission_validate(
        admission_recovery_out,
        admission_recovery_err,
        "recovery",
        0,
        admission_rec_a,
        admission_rec_b,
        expected_input_root=admission_input_root,
    )
    require(
        admission_recovery_report["phase"] == "recovery"
        and admission_recovery_report["canonical_input_root"] == admission_input_root,
        "valid kernel-admission recovery evidence lost its identity",
    )

    expect_admission_rejection(
        "malformed kernel-admission row",
        "admission_malformed",
        stdout_bytes=(
            b"running 2 tests\n"
            + b'{"schema":"' + KERNEL_ADMISSION_SCHEMA.encode() + b'", not-json\n'
            + b"test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured\n"
        ),
    )

    def add_extra_field(records: list[dict[str, Any]]) -> None:
        records[0]["stowaway"] = True

    expect_admission_rejection(
        "extra-field kernel-admission row",
        "admission_extra_field",
        add_extra_field,
        expected_message="extra=['stowaway']",
    )

    def drop_field(records: list[dict[str, Any]]) -> None:
        del records[1]["verdict_stream_digest"]

    expect_admission_rejection(
        "missing-field kernel-admission row",
        "admission_missing_field",
        drop_field,
        expected_message="missing=['verdict_stream_digest']",
    )

    def artifact_rows_of(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
        return [
            record
            for record in records
            if record.get("phase") == "artifact-incomplete-row"
        ]

    # Named artifact-completeness validator mutants (bead
    # franken_lean-artifact-incomplete-private-refs-sgt): each leaves exactly
    # one defect and must be rejected for the intended reason.

    def mark_incomplete_as_checked(records: list[dict[str, Any]]) -> None:
        for record in records:
            if record.get("scenario") == "init-prelude-admission-thread-matrix":
                record["checked"] += record["artifact_incomplete"]
                record["accepted"] += record["artifact_incomplete"]
                record["artifact_incomplete"] = 0

    expect_admission_rejection(
        "artifact-incomplete rows folded into the checked total",
        "admission_mark_incomplete_as_checked",
        mark_incomplete_as_checked,
        expected_message="census checked",
    )

    def collapse_unsafe_with_validated(records: list[dict[str, Any]]) -> None:
        artifact_rows_of(records)[0]["safety"] = "safe"

    expect_admission_rejection(
        "artifact-incomplete safety class collapsed into validated",
        "admission_collapse_unsafe_with_validated",
        collapse_unsafe_with_validated,
        expected_message="safety collapsed",
    )

    def omit_a_missing_reference(records: list[dict[str, Any]]) -> None:
        artifact_rows_of(records)[0]["missing_references"] = []

    expect_admission_rejection(
        "artifact-incomplete row omits its missing reference",
        "admission_omit_missing_reference",
        omit_a_missing_reference,
        expected_message="missing references drifted",
    )

    def accept_stale_reconstruction(records: list[dict[str, Any]]) -> None:
        artifact_rows_of(records)[1]["witness"] = "0" * 64

    expect_admission_rejection(
        "artifact-incomplete row accepts a stale reconstruction witness",
        "admission_accept_stale_reconstruction",
        accept_stale_reconstruction,
        expected_message="witness drifted",
    )

    def cache_inconclusive(records: list[dict[str, Any]]) -> None:
        artifact_rows_of(records)[0]["cacheable"] = True

    expect_admission_rejection(
        "artifact-incomplete row claims cacheability",
        "admission_cache_inconclusive",
        cache_inconclusive,
        expected_message="must be false",
    )

    def diverge_digest(records: list[dict[str, Any]]) -> None:
        records[2]["verdict_stream_digest"] = "0" * 64

    expect_admission_rejection(
        "thread-matrix digest divergence",
        "admission_digest_divergence",
        diverge_digest,
        expected_message="verdict stream diverged",
    )

    def drift_census(records: list[dict[str, Any]]) -> None:
        records[0]["accepted"] = KERNEL_ADMISSION_CENSUS["accepted"] - 1

    expect_admission_rejection(
        "census drift",
        "admission_census_drift",
        drift_census,
        expected_message="census accepted",
    )

    def wrong_mutant(records: list[dict[str, Any]]) -> None:
        row = next(
            record
            for record in records
            if record.get("mutant_id") == "tampered_recursor_rhs"
        )
        row["mutant_id"] = "tampered_recursor_lhs"
        row["phase"] = "mutant:tampered_recursor_lhs"

    expect_admission_rejection(
        "wrong-mutant kernel-admission row",
        "admission_wrong_mutant",
        wrong_mutant,
        expected_message="unknown mutant",
    )

    def surviving_mutant(records: list[dict[str, Any]]) -> None:
        row = next(
            record
            for record in records
            if record.get("mutant_id") == "nonpositive_ctor_field"
        )
        row["actual_outcome"] = "accepted"

    expect_admission_rejection(
        "surviving kernel-admission mutant",
        "admission_surviving_mutant",
        surviving_mutant,
        expected_message="SURVIVED",
    )

    expect_admission_rejection(
        "merged kernel-admission streams (census into stdout)",
        "admission_merged_census",
        stdout_bytes=(
            admission_pass_log(
                admission_records_for(
                    "admission_merged_census.out", "admission_merged_census.err"
                )
            )
            + admission_stderr_bytes
        ),
        expected_message="human census line leaked into stdout",
    )

    admission_leak_rows = admission_records_for(
        "admission_merged_rows.out", "admission_merged_rows.err"
    )
    expect_admission_rejection(
        "merged kernel-admission streams (rows into stderr)",
        "admission_merged_rows",
        stderr_bytes=admission_stderr_bytes
        + canonical_json(admission_leak_rows[0]),
        expected_message="detail rows leaked into stderr",
    )

    def stale_row_input(records: list[dict[str, Any]]) -> None:
        records[3]["canonical_input_root"] = f"fln-fixture:{'b' * 64}"

    expect_admission_rejection(
        "stale-input kernel-admission row",
        "admission_stale_row",
        stale_row_input,
        expected_message="input root changed across rows",
    )
    expect_admission_rejection(
        "stale-input kernel-admission run",
        "admission_stale_run",
        expected_input_root=f"fln-fixture:{'c' * 64}",
        expected_message="is stale",
    )

    def drop_resource_row(records: list[dict[str, Any]]) -> None:
        for index, record in enumerate(records):
            if record.get("phase") == "resource_recovery":
                del records[index]
                return

    expect_admission_rejection(
        "missing kernel-admission resource phase",
        "admission_missing_resource",
        drop_resource_row,
        expected_message="fault rows",
    )

    expect_admission_rejection(
        "kernel-admission stderr with failure material",
        "admission_failure_material",
        stderr_bytes=admission_stderr_bytes
        + b"test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured\n",
        expected_message="stderr contains failure material",
    )

    cases.append(
        {
            "case": "kernel_admission_validation",
            "ok": True,
            "positive": str(admission_positive_out),
            "recovery": str(admission_recovery_out),
        }
    )

    hash_root = case_dir("canonical_hash")
    write_new(hash_root / "a", b"alpha")
    write_new(hash_root / "b", b"beta")
    first_hash = tree_hash(hash_root, ["a", "b"])
    second_hash = tree_hash(hash_root, ["b", "a"])
    require(first_hash == second_hash, "canonical tree hash depends on argument order")
    cases.append({"case": "canonical_hash", "ok": True, "root": first_hash})

    manifest_root = case_dir("write_once_manifest")
    manifest_run_id = "manifest-self-test"
    manifest_meta = manifest_root / "manifest-stage.meta.json"
    manifest_rc = run_supervised(
        argv=[sys.executable, "-c", "print('manifest-stage')"],
        cwd=art_dir,
        metadata_path=manifest_meta,
        stdout_path=manifest_root / "manifest-stage.out",
        stderr_path=manifest_root / "manifest-stage.err",
        readiness_path=manifest_root / "manifest-stage.ready.json",
        artifact_root=manifest_root,
        capture_bytes=4096,
        output_budget_bytes=65_536,
        timeout_ms=5000,
        grace_ms=500,
        stage_id="manifest-stage",
        planted=False,
    )
    require(manifest_rc == PASS, "manifest self-test stage failed")
    manifest_supervisor = read_json_object(manifest_meta)
    manifest_records = [
        {
            "schema": "fln.check/2",
            "event": "run_start",
            "run_id": manifest_run_id,
            "bead": "fln-8mj",
            "scenario": "self_test",
            "sequence": 0,
            "monotonic_ns": 1,
            "wall_time_utc": utc_now(),
            "argv": ["evidence.py", "self-test"],
            "cwd": str(art_dir),
            "claim_ids": ["FLN-EVIDENCE-SELF-TEST"],
            "invariant_ids": ["FL-INV-07"],
            "gate_ids": ["G0-10"],
            "epoch": "lean-v4.32.0",
            "mode": "sound",
            "profile": "evidence-manifest-self-test",
            "platform": platform.platform(),
            "host_facts": {
                "machine": platform.machine(),
                "python": platform.python_version(),
                "release": platform.release(),
                "system": platform.system(),
            },
            "thread_count": 1,
            "seed": "deterministic",
            "cache_state": "not_applicable",
            "input_root": first_hash,
            "budgets": {"timeout_ms": 5000},
            "parity_ledger_row": "not_applicable_evidence_self_test",
            "planted": "",
            "verification_manifest": VERIFICATION_MANIFEST_PATH,
        },
        {
            "schema": "fln.check/2",
            "event": "stage",
            "run_id": manifest_run_id,
            "bead": "fln-8mj",
            "scenario": "self_test",
            "sequence": 1,
            "monotonic_ns": 2,
            "wall_time_utc": utc_now(),
            "stage": "manifest-stage",
            "outcome": "pass",
            "reason_code": "exit_zero",
            "expected": "exit_zero",
            "actual": "pass",
            "wrapper_exit": 0,
            "supervisor": manifest_supervisor,
        },
        {
            "schema": "fln.check/2",
            "event": "run_end",
            "run_id": manifest_run_id,
            "bead": "fln-8mj",
            "scenario": "self_test",
            "sequence": 2,
            "monotonic_ns": 3,
            "wall_time_utc": utc_now(),
            "verdict": "pass",
            "reason_code": "self_test_complete",
            "process_exit": 0,
            "active_stage": "complete",
            "duration_ns": 2,
            "cleanup_status": "retained_by_policy",
            "final_state": first_hash,
            "logical_root": first_hash,
            "receipt_root": "not_applicable_evidence_self_test",
            "first_divergence": "none",
            "evidence_manifest": "manifest.json",
            "bundle_commit": "bundle.complete.json",
            "evidence_state": "pending_bundle_commit",
        },
    ]
    write_new(
        manifest_root / "run.ndjson",
        b"".join(canonical_json(record) for record in manifest_records),
    )
    human_render = render_check_human(manifest_records)
    write_new(manifest_root / CHECK_HUMAN_LOG, human_render)
    validate_check_human(
        manifest_root / "run.ndjson", manifest_root / CHECK_HUMAN_LOG
    )
    human_mutant_root = case_dir("event_render_equivalence")
    human_mutant = human_mutant_root / "human.semantic.mutant.log"
    write_new(human_mutant, human_render + b"forged-extra-event\n")
    try:
        validate_check_human(manifest_root / "run.ndjson", human_mutant)
    except EvidenceError:
        pass
    else:
        raise EvidenceError("human/NDJSON divergence was accepted")
    cases.append(
        {
            "case": "event_render_equivalence",
            "ok": True,
            "mutants_killed": 1,
        }
    )
    run_report = validate_run(manifest_root / "run.ndjson", "fln.check/2", "pass")
    write_new(manifest_root / "run.validation.json", canonical_json(run_report))
    generate_manifest(
        manifest_root,
        manifest_root / "manifest.json",
        manifest_root / "manifest.digest",
        manifest_run_id,
        "fln-8mj",
        "self_test",
        "pass",
        first_hash,
        first_hash,
    )
    try:
        validate_bundle(
            manifest_root,
            manifest_root / "manifest.json",
            manifest_root / "manifest.digest",
            manifest_root / "bundle.complete.json",
        )
    except (EvidenceError, FileNotFoundError):
        pass
    else:
        raise EvidenceError("bundle without a commit marker was accepted")
    relative_manifest_root = Path(os.path.relpath(manifest_root, Path.cwd()))
    try:
        complete_bundle(
            relative_manifest_root,
            relative_manifest_root / "manifest.json",
            relative_manifest_root / "manifest.digest",
            relative_manifest_root / "bundle.complete.json",
            governed_root=hash_root,
            governed_paths=["a", "b"],
            expected_root=first_hash,
            test_fail_after_link=True,
        )
    except EvidenceError as error:
        require(
            "injected failure after atomic link" in str(error),
            "bundle link fault produced the wrong failure",
        )
    else:
        raise EvidenceError("bundle link fault injection unexpectedly returned success")
    require(
        (manifest_root / "bundle.decision").exists()
        and not (manifest_root / "bundle.complete.json").exists(),
        "bundle link fault did not exercise the recovery window",
    )
    # Validation is side-effect-free: on a winning decision whose marker was
    # never linked it must fail typed and must not create the marker itself.
    try:
        validate_bundle(
            manifest_root,
            manifest_root / "manifest.json",
            manifest_root / "manifest.digest",
            manifest_root / "bundle.complete.json",
        )
    except EvidenceError as error:
        require(
            "named adoption operation" in str(error),
            "pre-marker validation produced the wrong failure",
        )
    else:
        raise EvidenceError("pre-marker bundle validation reported commitment")
    require(
        not (manifest_root / "bundle.complete.json").exists(),
        "side-effect-free validation created the bundle marker",
    )
    # Concurrent adoption is idempotent: both adopters must succeed and agree
    # on the single canonical marker recovered from the winning decision.
    adoption_results: list[str] = []

    def race_adopter(label: str) -> None:
        try:
            adopt_bundle(
                manifest_root,
                manifest_root / "manifest.json",
                manifest_root / "manifest.digest",
                manifest_root / "bundle.complete.json",
            )
            adoption_results.append(f"{label}:adopted")
        except EvidenceError as adopt_error:
            adoption_results.append(f"{label}:{adopt_error}")

    first_adopter = threading.Thread(target=race_adopter, args=("first",))
    second_adopter = threading.Thread(target=race_adopter, args=("second",))
    first_adopter.start()
    second_adopter.start()
    first_adopter.join()
    second_adopter.join()
    require(
        sorted(adoption_results) == ["first:adopted", "second:adopted"],
        f"concurrent adoption was not idempotent: {adoption_results}",
    )
    require(
        (manifest_root / "bundle.complete.json").exists(),
        "adoption did not recover the winning decision",
    )
    adopted_marker, _adopted_size, _adopted_digest = stable_file_facts(
        manifest_root / "bundle.complete.json"
    )
    winning_decision, _winning_size, _winning_digest = stable_file_facts(
        manifest_root / "bundle.decision"
    )
    require(
        hmac.compare_digest(adopted_marker, winning_decision),
        "adopted marker disagrees with the winning decision",
    )
    validate_bundle(
        manifest_root,
        manifest_root / "manifest.json",
        manifest_root / "manifest.digest",
        manifest_root / "bundle.complete.json",
    )
    validate_bundle(
        relative_manifest_root,
        relative_manifest_root / "manifest.json",
        relative_manifest_root / "manifest.digest",
        relative_manifest_root / "bundle.complete.json",
    )
    try:
        validate_bundle(
            manifest_root,
            manifest_root / "control" / "manifest.json",
            manifest_root / "control" / "manifest.digest",
            manifest_root / "bundle.complete.json",
        )
    except EvidenceError as error:
        require(
            "must be exactly" in str(error),
            "nested control path produced the wrong failure",
        )
    else:
        raise EvidenceError("nested bundle control paths were accepted")
    try:
        write_new(manifest_root / "bundle.complete.json", b"overwrite\n")
    except FileExistsError:
        pass
    else:
        raise EvidenceError("write-once bundle marker was overwritten")
    cases.append({"case": "write_once_manifest", "ok": True})

    relocated_root = case_dir("relocated_bundle_validation")
    source_manifest = read_json_object(manifest_root / "manifest.json")
    directory_entries = sorted(
        (
            entry
            for entry in source_manifest["artifacts"]
            if entry["role"] == "directory"
        ),
        key=lambda entry: (
            len(Path(entry["path"]).parts),
            entry["path"].encode("utf-8"),
        ),
    )
    for entry in directory_entries:
        (relocated_root / entry["path"]).mkdir()
    for entry in source_manifest["artifacts"]:
        if entry["role"] == "directory":
            continue
        source = manifest_root / entry["path"]
        data, _size, _digest = stable_file_facts(source)
        write_new(relocated_root / entry["path"], data)
    for control_name in (
        "manifest.json",
        "manifest.digest",
        "bundle.decision",
        "bundle.complete.json",
    ):
        data, _size, _digest = stable_file_facts(manifest_root / control_name)
        write_new(relocated_root / control_name, data)
    for identity_name in (
        "run.ndjson",
        "manifest.json",
        "bundle.complete.json",
    ):
        require(
            (manifest_root / identity_name).stat().st_ino
            != (relocated_root / identity_name).stat().st_ino,
            f"relocated bundle reused source inode: {identity_name}",
        )
    validate_bundle(
        relocated_root,
        relocated_root / "manifest.json",
        relocated_root / "manifest.digest",
        relocated_root / "bundle.complete.json",
    )
    cases.append({"case": "relocated_bundle_validation", "ok": True})

    cancellation_root = case_dir("bundle_decision_cancellation")
    cancellation_decision = cancellation_root / "bundle.decision"
    cancellation_marker = cancellation_root / "bundle.complete.json"
    write_new(cancellation_decision, b"")
    try:
        write_signal_committed_atomic_new(
            cancellation_marker,
            b'{"status":"committed"}\n',
            decision_path=cancellation_decision,
        )
    except EvidenceError as error:
        require(
            "cancellation won the bundle decision race" in str(error),
            "bundle cancellation produced the wrong failure",
        )
    else:
        raise EvidenceError("bundle commit ignored the cancellation decision")
    require(
        not cancellation_marker.exists(),
        "cancelled bundle decision still published a commit marker",
    )
    # Cancellation can never be adopted as pass: the named adoption operation
    # must refuse the empty claimed decision and must not create the marker.
    try:
        adopt_bundle(
            cancellation_root,
            cancellation_root / "manifest.json",
            cancellation_root / "manifest.digest",
            cancellation_marker,
        )
    except EvidenceError as error:
        require(
            "adoption refused" in str(error),
            "cancelled-decision adoption produced the wrong failure",
        )
    else:
        raise EvidenceError("cancellation was adopted as a committed bundle")
    require(
        not cancellation_marker.exists(),
        "refused adoption still published a commit marker",
    )
    cases.append({"case": "bundle_decision_cancellation", "ok": True})

    # --- early-envelope partial bundles (bead fln-evidence-runner-bootstrap-btk):
    # a consumer fault between artifact-directory creation and run_start still
    # finalizes a typed durable partial bundle that can never claim, be
    # validated as, or be adopted into completeness.
    partial_root = case_dir("partial_bundle_publication")
    write_new(partial_root / "human.log", b"[probe] early fault\n")
    write_new(partial_root / "ubs-inventory.json", b"{}\n")
    partial_marker_object = publish_partial_bundle(
        partial_root,
        run_id="partial-selftest-1",
        bead="fln-8mj",
        scenario="quality_gate",
        step="vendor_binding",
        reason="early_vendor_binding_failure",
        classification="internal_fault",
        argv=["scripts/check.sh", "--token=supersecret"],
        cwd=str(partial_root),
    )
    require(
        partial_marker_object["status"] == "incomplete",
        "partial marker did not carry the incomplete status",
    )
    partial_fault_data, _partial_fault_size, _partial_fault_digest = (
        stable_file_facts(partial_root / "setup-fault.json")
    )
    require(
        b"supersecret" not in partial_fault_data
        and b"<redacted>" in partial_fault_data,
        "partial setup fault leaked a secret argv value",
    )
    partial_report = validate_partial_bundle(partial_root)
    require(
        partial_report["valid"] is True
        and partial_report["committed"] is False
        and partial_report["classification"] == "internal_fault",
        "partial bundle validation lost its typed shape",
    )
    try:
        publish_partial_bundle(
            partial_root,
            run_id="partial-selftest-1",
            bead="fln-8mj",
            scenario="quality_gate",
            step="vendor_binding",
            reason="early_vendor_binding_failure",
            classification="internal_fault",
            argv=["scripts/check.sh"],
            cwd=str(partial_root),
        )
    except FileExistsError:
        pass
    else:
        raise EvidenceError("partial bundle publication was not write-once")
    try:
        adopt_bundle(
            partial_root,
            partial_root / "manifest.json",
            partial_root / "manifest.digest",
            partial_root / "bundle.complete.json",
        )
    except (EvidenceError, FileNotFoundError):
        pass
    else:
        raise EvidenceError("a partial decision was adopted as complete")
    require(
        not (partial_root / "bundle.complete.json").exists(),
        "refused partial adoption still created the complete marker",
    )
    try:
        validate_bundle(
            partial_root,
            partial_root / "manifest.json",
            partial_root / "manifest.digest",
            partial_root / "bundle.complete.json",
        )
    except (EvidenceError, FileNotFoundError):
        pass
    else:
        raise EvidenceError("a partial bundle validated as complete")
    write_new(partial_root / "late-artifact.txt", b"late\n")
    try:
        validate_partial_bundle(partial_root)
    except EvidenceError as error:
        require(
            "changed after publication" in str(error),
            "post-publication drift produced the wrong failure",
        )
    else:
        raise EvidenceError("post-publication drift was not detected")
    cases.append(
        {
            "case": "partial_bundle_publication",
            "ok": True,
            "artifact": str(partial_root),
        }
    )

    partial_cancel_root = case_dir("partial_bundle_cancellation")
    write_new(partial_cancel_root / "bundle.decision", b"")
    try:
        publish_partial_bundle(
            partial_cancel_root,
            run_id="partial-selftest-2",
            bead="fln-8mj",
            scenario="quality_gate",
            step="initial_hash",
            reason="early_initial_hash_failure",
            classification="internal_fault",
            argv=["scripts/check.sh"],
            cwd=str(partial_cancel_root),
        )
    except EvidenceError as error:
        require(
            "cancellation won the bundle decision race" in str(error),
            "partial cancellation race produced the wrong failure",
        )
    else:
        raise EvidenceError("partial publication ignored a claimed decision")
    require(
        not (partial_cancel_root / "bundle.incomplete.json").exists(),
        "cancelled partial publication still linked its marker",
    )
    cases.append({"case": "partial_bundle_cancellation", "ok": True})

    hash_mutation_root = case_dir("initial_hash_mutation")
    write_new(hash_mutation_root / "governed-a.txt", b"alpha\n")
    write_new(hash_mutation_root / "governed-b.txt", b"beta\n")
    hash_control = subprocess.run(
        [
            sys.executable,
            "-I",
            "-S",
            str(Path(__file__).resolve()),
            "hash-tree",
            "--root",
            str(hash_mutation_root),
            "--path",
            "governed-a.txt",
            "--path",
            "governed-b.txt",
        ],
        capture_output=True,
        timeout=60,
        check=False,
    )
    require(
        hash_control.returncode == 0,
        f"control hash failed: {hash_control.stderr[-200:]!r}",
    )
    mutation_size_before = (hash_mutation_root / "governed-a.txt").stat().st_size
    hash_mutated = subprocess.run(
        [
            sys.executable,
            "-I",
            "-S",
            str(Path(__file__).resolve()),
            "hash-tree",
            "--root",
            str(hash_mutation_root),
            "--path",
            "governed-a.txt",
            "--path",
            "governed-b.txt",
            "--test-mutate-input",
            "governed-a.txt",
        ],
        capture_output=True,
        timeout=60,
        check=False,
    )
    require(
        hash_mutated.returncode != 0
        and b"changed while being read" in hash_mutated.stderr,
        f"planted hash mutation was not detected: {hash_mutated.stderr[-200:]!r}",
    )
    require(
        (hash_mutation_root / "governed-a.txt").stat().st_size
        == mutation_size_before + 1,
        "planted hash mutation did not really mutate the input",
    )
    cases.append({"case": "initial_hash_mutation", "ok": True})

    # --- deliberate early-envelope fault probes against the real consumer
    # (bead fln-evidence-runner-bootstrap-btk): every early step of check.sh
    # from artifact-directory creation through run_start faults against a
    # planted-real obstruction and still finalizes a typed durable partial
    # bundle; an early signal cancels into the same partial form; a reused
    # artifact directory is refused without touching foreign state.
    def run_early_fault_probe(
        test_step: str,
        expected_exit: int,
        expected_classification: str,
        expected_step: str,
        expected_reason: str,
        *,
        signal_number: int | None = None,
    ) -> None:
        repo = Path(__file__).resolve().parent.parent
        check_script = repo / "scripts" / "check.sh"
        probe_root = art_dir / f"early_fault_{test_step}"
        require(
            not probe_root.exists() and not probe_root.is_symlink(),
            f"early fault probe root already exists: {test_step}",
        )
        probe_environment = {
            key: value
            for key, value in os.environ.items()
            if not key.startswith("FLN_CHECK_")
            and not key.startswith("FLN_FINALIZER_")
        }
        probe_environment.update(
            {
                "FLN_CHECK_ART_DIR": str(probe_root),
                "FLN_CHECK_TEST_EARLY_FAULT": test_step,
            }
        )
        child = subprocess.Popen(
            ["bash", str(check_script), "--early-fault-probe"],
            cwd=repo,
            env=probe_environment,
            start_new_session=True,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        try:
            if signal_number is not None:
                hold_path = probe_root / "early.hold"
                hold_deadline = time.monotonic() + 30
                while (
                    not hold_path.exists()
                    and child.poll() is None
                    and time.monotonic() < hold_deadline
                ):
                    time.sleep(0.01)
                require(
                    hold_path.exists(),
                    f"{test_step}: early hold point was never reached",
                )
                child.send_signal(signal_number)
            _early_out, early_err = child.communicate(timeout=120)
        finally:
            if child.poll() is None:
                child.kill()
                child.communicate(timeout=10)
        require(
            child.returncode == expected_exit,
            f"{test_step}: early probe exit {child.returncode}: "
            f"{early_err[-300:]!r}",
        )
        require(
            b"partial early-envelope evidence" in early_err,
            f"{test_step}: partial publication was not reported",
        )
        early_report = validate_partial_bundle(probe_root)
        require(
            early_report["valid"] is True
            and early_report["committed"] is False
            and early_report["classification"] == expected_classification
            and early_report["step"] == expected_step
            and early_report["reason_code"] == expected_reason,
            f"{test_step}: partial bundle lost its typed shape: {early_report}",
        )
        require(
            not (probe_root / "bundle.complete.json").exists(),
            f"{test_step}: an early fault produced a complete bundle marker",
        )
        cases.append(
            {
                "case": f"early_fault_{test_step}",
                "ok": True,
                "artifact": str(probe_root),
            }
        )

    run_early_fault_probe(
        "probe_control",
        SETUP_FAILURE,
        "internal_fault",
        "probe_control",
        "early_probe_control_failure",
    )
    run_early_fault_probe(
        "ubs_inventory",
        SETUP_FAILURE,
        "internal_fault",
        "ubs_inventory",
        "early_ubs_inventory_failure",
    )
    run_early_fault_probe(
        "vendor_binding",
        SETUP_FAILURE,
        "internal_fault",
        "vendor_binding",
        "early_vendor_binding_failure",
    )
    run_early_fault_probe(
        "initial_hash",
        INCONCLUSIVE,
        "inconclusive",
        "initial_hash",
        "governed_input_mutation_during_initial_hash",
    )
    run_early_fault_probe(
        "run_start_emission",
        SETUP_FAILURE,
        "internal_fault",
        "run_start_emission",
        "early_run_start_emission_failure",
    )
    run_early_fault_probe(
        "human_log",
        SETUP_FAILURE,
        "internal_fault",
        "human_log",
        "early_human_log_failure",
    )
    run_early_fault_probe(
        "early_signal_hold",
        143,
        "cancelled",
        "artifact_directory_creation",
        "signal_TERM",
        signal_number=signal.SIGTERM,
    )

    reused_root = case_dir("early_fault_reused_directory")
    write_new(reused_root / "canary.txt", b"canary\n")
    reused_environment = {
        key: value
        for key, value in os.environ.items()
        if not key.startswith("FLN_CHECK_")
        and not key.startswith("FLN_FINALIZER_")
    }
    reused_environment["FLN_CHECK_ART_DIR"] = str(reused_root)
    reused_probe = subprocess.run(
        [
            "bash",
            str(Path(__file__).resolve().parent.parent / "scripts" / "check.sh"),
            "--early-fault-probe",
        ],
        cwd=Path(__file__).resolve().parent.parent,
        env=reused_environment,
        capture_output=True,
        timeout=60,
        check=False,
    )
    require(
        reused_probe.returncode == SETUP_FAILURE
        and b"evidence directory already claimed" in reused_probe.stderr,
        f"reused-directory refusal lost its type: {reused_probe.stderr[-200:]!r}",
    )
    require(
        sorted(path.name for path in reused_root.iterdir()) == ["canary.txt"],
        "reused-directory refusal touched foreign state",
    )
    cases.append({"case": "early_fault_reused_directory", "ok": True})

    # The shell finalizer is armed before the artifact root is claimed. Prove
    # that its ownership state follows the atomic mkdir result rather than the
    # mere existence of the path: a concurrent loser must exit typed without
    # publishing into, truncating, or otherwise changing the winner's root.
    claim_root = art_dir / "concurrent_artifact_directory_claim"
    require(
        not claim_root.exists() and not claim_root.is_symlink(),
        "concurrent artifact-directory claim root was not fresh",
    )
    claim_environment = {
        key: value
        for key, value in os.environ.items()
        if not key.startswith("FLN_CHECK_")
        and not key.startswith("FLN_FINALIZER_")
    }
    claim_environment.update(
        {
            "FLN_CHECK_ART_DIR": str(claim_root),
            "FLN_CHECK_TEST_EARLY_FAULT": "early_signal_hold",
        }
    )
    claim_winner = subprocess.Popen(
        ["bash", str(Path(__file__).resolve().parent.parent / "scripts" / "check.sh"),
         "--early-fault-probe"],
        cwd=Path(__file__).resolve().parent.parent,
        env=claim_environment,
        start_new_session=True,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    try:
        claim_hold = claim_root / "early.hold"
        claim_deadline = time.monotonic() + 30
        while (
            not claim_hold.exists()
            and claim_winner.poll() is None
            and time.monotonic() < claim_deadline
        ):
            time.sleep(0.01)
        require(
            claim_hold.exists(),
            "artifact-directory claim winner never reached its hold point",
        )
        before_loser = sorted(path.name for path in claim_root.iterdir())
        require(
            before_loser == ["early.hold"],
            f"claim winner published unexpected pre-envelope state: {before_loser}",
        )
        hold_data, hold_size, hold_digest = stable_file_facts(claim_hold)
        claim_loser = subprocess.run(
            [
                "bash",
                str(Path(__file__).resolve().parent.parent / "scripts" / "check.sh"),
                "--early-fault-probe",
            ],
            cwd=Path(__file__).resolve().parent.parent,
            env=claim_environment,
            capture_output=True,
            timeout=60,
            check=False,
        )
        require(
            claim_loser.returncode == SETUP_FAILURE
            and b"evidence directory already claimed" in claim_loser.stderr,
            "artifact-directory claim loser lost its typed refusal: "
            f"{claim_loser.stderr[-300:]!r}",
        )
        after_loser = sorted(path.name for path in claim_root.iterdir())
        require(
            after_loser == before_loser,
            "artifact-directory claim loser changed the winner's namespace",
        )
        repeated_data, repeated_size, repeated_digest = stable_file_facts(claim_hold)
        require(
            (repeated_data, repeated_size, repeated_digest)
            == (hold_data, hold_size, hold_digest),
            "artifact-directory claim loser changed the winner's hold artifact",
        )
        claim_winner.send_signal(signal.SIGTERM)
        _claim_out, claim_err = claim_winner.communicate(timeout=120)
    finally:
        if claim_winner.poll() is None:
            claim_winner.kill()
            claim_winner.communicate(timeout=10)
    require(
        claim_winner.returncode == 143,
        f"artifact-directory claim winner exit {claim_winner.returncode}: "
        f"{claim_err[-300:]!r}",
    )
    claim_report = validate_partial_bundle(claim_root)
    require(
        claim_report["valid"] is True
        and claim_report["committed"] is False
        and claim_report["classification"] == "cancelled"
        and claim_report["step"] == "artifact_directory_creation"
        and claim_report["reason_code"] == "signal_TERM",
        f"artifact-directory claim winner lost its bundle: {claim_report}",
    )
    cases.append(
        {
            "case": "concurrent_artifact_directory_claim",
            "ok": True,
            "loser_exit": SETUP_FAILURE,
            "winner_artifact": str(claim_root),
        }
    )

    # --- deliberate consumer-outcome scenarios (bead
    # fln-evidence-runner-bootstrap-btk): the remaining outcome families for
    # the three consumers in complete-bundle form — unexpected failure,
    # post-run_start internal fault, and (for check.sh) concurrent source
    # drift. Lane source drift requires mutating governed inputs, so it is
    # proven against a scratch clone with the guarded during_first_step_drift
    # plant and retained as close evidence rather than run per-gate.
    def run_consumer_fault_case(
        case_name: str,
        argv: list[str],
        environment_overrides: dict[str, str],
        art_dir_env: str,
        art_glob: str | None,
        expected_exit: int,
        schema: str,
        expected_verdict: str,
        expected_reason: str,
        expected_stderr_fragment: bytes | None = None,
    ) -> Path:
        repo = Path(__file__).resolve().parent.parent
        case_root = art_dir / case_name
        environment = {
            key: value
            for key, value in os.environ.items()
            if not key.startswith("FLN_CHECK_")
            and not key.startswith("FLN_FINALIZER_")
            and not key.startswith("FLN_SG_")
            and not key.startswith("FLN_CA_")
            and not key.startswith("FLN_E2E_")
        }
        environment.update(environment_overrides)
        environment[art_dir_env] = str(case_root)
        child = subprocess.run(
            argv,
            cwd=repo,
            env=environment,
            capture_output=True,
            timeout=600,
            check=False,
        )
        require(
            child.returncode == expected_exit,
            f"{case_name}: exit {child.returncode}: {child.stderr[-300:]!r}",
        )
        if expected_stderr_fragment is not None:
            require(
                expected_stderr_fragment in child.stderr,
                f"{case_name}: expected stderr fragment was not emitted: "
                f"{child.stderr[-300:]!r}",
            )
        if art_glob is None:
            bundle_dir = case_root
        else:
            matches = sorted(case_root.glob(art_glob))
            require(
                len(matches) == 1,
                f"{case_name}: expected one bundle dir, found {len(matches)}",
            )
            bundle_dir = matches[0]
        validate_run(
            bundle_dir / "run.ndjson",
            schema,
            expected_verdict,
            live_context=False,
        )
        validate_bundle(
            bundle_dir,
            bundle_dir / "manifest.json",
            bundle_dir / "manifest.digest",
            bundle_dir / "bundle.complete.json",
        )
        terminal = load_ndjson(bundle_dir / "run.ndjson")[-1]
        require(
            terminal.get("reason_code") == expected_reason,
            f"{case_name}: terminal reason {terminal.get('reason_code')!r}, "
            f"expected {expected_reason!r}",
        )
        cases.append(
            {"case": case_name, "ok": True, "artifact": str(bundle_dir)}
        )
        return bundle_dir

    consumer_check_script = str(
        Path(__file__).resolve().parent.parent / "scripts" / "check.sh"
    )
    short_circuit_bundle = run_consumer_fault_case(
        "consumer_check_unexpected_stage",
        ["bash", consumer_check_script],
        {"FLN_CHECK_PLANT_UNEXPECTED": "evidence-self-test"},
        "FLN_CHECK_ART_DIR",
        None,
        SETUP_FAILURE,
        "fln.check/2",
        "internal_fault",
        "evidence-self-test:unexpected_child_exit",
    )

    def clone_short_circuit_mutant(
        name: str, mutate: Callable[[list[dict[str, Any]]], None]
    ) -> Path:
        mutant_root = case_dir(name)
        for source in sorted(
            short_circuit_bundle.rglob("*"),
            key=lambda path: (len(path.relative_to(short_circuit_bundle).parts), str(path)),
        ):
            relative = source.relative_to(short_circuit_bundle)
            target = mutant_root / relative
            if source.is_dir():
                target.mkdir()
            elif source.is_file():
                if relative == Path("run.ndjson"):
                    continue
                data, _size, _digest = stable_file_facts(source)
                write_new(target, data)
            else:
                raise EvidenceError(
                    f"short-circuit fixture contains a special file: {source}"
                )
        records = load_ndjson(short_circuit_bundle / "run.ndjson")
        mutate(records)
        for sequence, record in enumerate(records):
            record["sequence"] = sequence
        write_new(
            mutant_root / "run.ndjson",
            b"".join(canonical_json(record) for record in records),
        )
        return mutant_root / "run.ndjson"

    omitted_not_run = clone_short_circuit_mutant(
        "stage_short_circuit_omitted_not_run",
        lambda records: records.pop(
            next(
                index
                for index, record in enumerate(records)
                if record.get("outcome") == "not_run"
            )
        ),
    )
    wrong_cause = clone_short_circuit_mutant(
        "stage_short_circuit_wrong_cause",
        lambda records: next(
            record for record in records if record.get("outcome") == "not_run"
        ).update(causal_reason="forged-cause"),
    )
    for mutant, expected_fragment in (
        (omitted_not_run, "non-canonical check obligation order"),
        (wrong_cause, "exact failure causality"),
    ):
        try:
            validate_run(
                mutant,
                "fln.check/2",
                "internal_fault",
                live_context=False,
            )
        except EvidenceError as error:
            require(
                expected_fragment in str(error),
                f"short-circuit mutant failed for the wrong reason: {error}",
            )
        else:
            raise EvidenceError(
                f"short-circuit mutant survived: {mutant.parent.name}"
            )
    cases.append(
        {"case": "stage_short_circuit_model", "ok": True, "mutants_killed": 2}
    )
    run_consumer_fault_case(
        "consumer_check_drift",
        ["bash", consumer_check_script, "--early-fault-probe"],
        {"FLN_CHECK_TEST_EARLY_FAULT": "post_run_start_drift"},
        "FLN_CHECK_ART_DIR",
        None,
        INCONCLUSIVE,
        "fln.check/2",
        "inconclusive",
        "final_workspace_changed",
    )
    run_consumer_fault_case(
        "consumer_check_abort",
        ["bash", consumer_check_script, "--early-fault-probe"],
        {"FLN_CHECK_TEST_EARLY_FAULT": "post_run_start_abort"},
        "FLN_CHECK_ART_DIR",
        None,
        SETUP_FAILURE,
        "fln.check/2",
        "internal_fault",
        "unexpected_shell_exit",
    )
    for lane_script_name, lane_env, lane_glob, lane_tag in (
        (
            "structure_gate.sh",
            "FLN_SG_TEST_EARLY_FAULT",
            "structure-gate-*",
            "structure_gate",
        ),
        (
            "closure_audit.sh",
            "FLN_CA_TEST_EARLY_FAULT",
            "closure-audit-*",
            "closure_audit",
        ),
    ):
        lane_script = str(
            Path(__file__).resolve().parent.parent
            / "scripts"
            / "e2e"
            / lane_script_name
        )
        unexpected_bundle = run_consumer_fault_case(
            f"consumer_{lane_tag}_unexpected_step",
            ["bash", lane_script],
            {lane_env: "unexpected_first_step"},
            "FLN_E2E_ART_ROOT",
            lane_glob,
            SETUP_FAILURE,
            "fln.e2e/2",
            "internal_fault",
            "build_guard:unexpected_child_exit",
            (
                b"[structure_gate] post-seal diagnostic probe: "
                b"unexpected_first_step"
                if lane_tag == "structure_gate"
                else None
            ),
        )
        if lane_tag == "structure_gate":
            manifest = read_json_object(unexpected_bundle / "manifest.json")
            human_rows = [
                row
                for row in manifest["artifacts"]
                if row.get("path") == "human.log"
            ]
            require(
                len(human_rows) == 1,
                "consumer_structure_gate_unexpected_step: manifest must bind "
                "human.log exactly once",
            )
            human_data, human_size, human_digest = stable_file_facts(
                unexpected_bundle / "human.log"
            )
            expected_terminal = (
                b"[structure_gate] terminal verdict=internal_fault "
                b"reason=build_guard:unexpected_child_exit process_exit=2\n"
            )
            require(
                human_data.endswith(expected_terminal),
                "consumer_structure_gate_unexpected_step: human.log was not "
                "sealed after its terminal semantic record",
            )
            require(
                b"post-seal diagnostic probe" not in human_data,
                "consumer_structure_gate_unexpected_step: a post-seal "
                "diagnostic mutated human.log",
            )
            require(
                human_rows[0].get("bytes") == human_size
                and human_rows[0].get("sha256") == human_digest,
                "consumer_structure_gate_unexpected_step: manifested human.log "
                "facts differ from the final file",
            )
            cases.append(
                {
                    "case": (
                        "consumer_structure_gate_unexpected_step_human_log_sealed"
                    ),
                    "ok": True,
                    "bytes": human_size,
                    "sha256": human_digest,
                }
            )
        run_consumer_fault_case(
            f"consumer_{lane_tag}_abort",
            ["bash", lane_script],
            {lane_env: "post_run_start_abort"},
            "FLN_E2E_ART_ROOT",
            lane_glob,
            SETUP_FAILURE,
            "fln.e2e/2",
            "internal_fault",
            "unexpected_shell_exit",
        )

    race_root = case_dir("write_collision_race")
    race_path = race_root / "collision-race.txt"
    race_results: list[str] = []

    def race_writer(value: bytes) -> None:
        try:
            write_new(race_path, value)
            race_results.append("published")
        except FileExistsError:
            race_results.append("collision")

    first_writer = threading.Thread(target=race_writer, args=(b"first\n",))
    second_writer = threading.Thread(target=race_writer, args=(b"second\n",))
    first_writer.start()
    second_writer.start()
    first_writer.join()
    second_writer.join()
    require(
        sorted(race_results) == ["collision", "published"],
        "collision race was not exclusive",
    )
    race_data, _race_size, _race_digest = stable_file_facts(race_path)
    require(race_data in {b"first\n", b"second\n"}, "collision race corrupted evidence")
    cases.append({"case": "write_collision_race", "ok": True})

    # --- sealed interpreter environment (bead franken_lean-h40t): prove the
    # negative control first. A real unsealed evidence.py import must execute a
    # PYTHONPATH shadow; the real -I -S supervisor must then refuse that same
    # channel typed before spawning its target, retain names only, and recover.
    interpreter_root = case_dir("sealed_interpreter_validation")
    interpreter_shadow = interpreter_root / "shadow"
    interpreter_shadow.mkdir()
    shadow_marker = interpreter_root / "shadow-imported"
    (interpreter_shadow / "platform.py").write_text(
        "with open("
        + repr(str(shadow_marker))
        + ", 'ab') as marker:\n"
        "    marker.write(b'shadow-imported\\n')\n"
        "raise RuntimeError('planted PYTHONPATH shadow executed')\n"
    )
    interpreter_base_env = {
        "PATH": SEALED_PATH_TAIL,
        "HOME": os.environ.get("HOME", str(Path.home())),
    }
    hostile_python_path = str(interpreter_shadow)
    interpreter_hostile_env = {
        **interpreter_base_env,
        "PYTHONPATH": hostile_python_path,
    }
    negative_control = subprocess.run(  # ubs:ignore — exact current interpreter and checked-in evidence utility prove the planted import channel.
        [sys.executable, str(Path(__file__).resolve()), "--help"],
        capture_output=True,
        env=interpreter_hostile_env,
        timeout=30,
        check=False,
    )
    shadow_before, _shadow_size, _shadow_digest = stable_file_facts(shadow_marker)
    require(
        negative_control.returncode != PASS
        and shadow_before == b"shadow-imported\n",
        "unsealed PYTHONPATH negative control did not execute the planted shadow",
    )
    direct_hash_argv = [
        str(Path(__file__).resolve()),
        "hash-tree",
        "--root",
        str(interpreter_root),
        "--path",
        "shadow",
    ]
    direct_unsealed = subprocess.run(
        [sys.executable, *direct_hash_argv],
        capture_output=True,
        env=interpreter_base_env,
        timeout=30,
        check=False,
    )
    require(
        direct_unsealed.returncode == SETUP_FAILURE
        and b"sealed_interpreter_unsealed_startup" in direct_unsealed.stderr
        and direct_unsealed.stdout == b"",
        "direct evidence command did not refuse unsealed startup typed",
    )
    direct_hostile = subprocess.run(
        [sys.executable, "-I", "-S", *direct_hash_argv],
        capture_output=True,
        env=interpreter_hostile_env,
        timeout=30,
        check=False,
    )
    repeated_shadow, _shadow_size, _shadow_digest = stable_file_facts(shadow_marker)
    require(
        direct_hostile.returncode == SETUP_FAILURE
        and b"sealed_interpreter_hostile_environment" in direct_hostile.stderr
        and direct_hostile.stdout == b""
        and repeated_shadow == shadow_before,
        "direct evidence command did not refuse hostile Python configuration",
    )
    direct_recovery = subprocess.run(
        [sys.executable, "-I", "-S", *direct_hash_argv],
        capture_output=True,
        env=interpreter_base_env,
        timeout=30,
        check=False,
    )
    require(
        direct_recovery.returncode == PASS
        and direct_recovery.stdout.startswith(b"sha256:")
        and len(direct_recovery.stdout.strip()) == len(b"sha256:") + 64,
        f"sealed direct evidence command did not recover: {direct_recovery.stderr!r}",
    )
    trusted_repo = Path(__file__).resolve().parent.parent
    hostile_shell_root = interpreter_root / "hostile-shell-must-not-exist"
    hostile_shell_env = {
        **interpreter_hostile_env,
        "FLN_CHECK_ART_DIR": str(hostile_shell_root),
        "FLN_CHECK_TEST_EARLY_FAULT": "probe_control",
    }
    hostile_shell = subprocess.run(
        ["bash", str(trusted_repo / "scripts" / "check.sh"), "--early-fault-probe"],
        cwd=trusted_repo,
        capture_output=True,
        env=hostile_shell_env,
        timeout=30,
        check=False,
    )
    require(
        hostile_shell.returncode == SETUP_FAILURE
        and b"sealed_interpreter_hostile_environment names=PYTHONPATH"
        in hostile_shell.stderr
        and hostile_python_path.encode() not in hostile_shell.stderr
        and not hostile_shell_root.exists()
        and not hostile_shell_root.is_symlink(),
        "trusted shell did not refuse hostile Python configuration before claiming artifacts",
    )
    generator = trusted_repo / "scripts" / "extract" / "gen_bignum_vectors.py"
    generator_unsealed = subprocess.run(
        [sys.executable, str(generator), "--check"],
        cwd=trusted_repo,
        capture_output=True,
        env=interpreter_base_env,
        timeout=30,
        check=False,
    )
    generator_hostile = subprocess.run(
        [sys.executable, "-I", "-S", str(generator), "--check"],
        cwd=trusted_repo,
        capture_output=True,
        env=interpreter_hostile_env,
        timeout=30,
        check=False,
    )
    generator_recovery = subprocess.run(
        [sys.executable, "-I", "-S", str(generator), "--check"],
        cwd=trusted_repo,
        capture_output=True,
        env=interpreter_base_env,
        timeout=30,
        check=False,
    )
    require(
        generator_unsealed.returncode == SETUP_FAILURE
        and b"sealed_interpreter_unsealed_startup" in generator_unsealed.stderr
        and generator_hostile.returncode == SETUP_FAILURE
        and b"sealed_interpreter_hostile_environment names=PYTHONPATH"
        in generator_hostile.stderr
        and hostile_python_path.encode() not in generator_hostile.stderr
        and generator_recovery.returncode == PASS
        and b"no drift" in generator_recovery.stderr,
        "trusted extraction script did not refuse both startup channels and recover",
    )

    interpreter_case_counter = [0]
    interpreter_target_marker = interpreter_root / "target-executed"

    def run_interpreter_case(
        label: str,
        *,
        environment: Mapping[str, str],
        expected_reason: str,
        expected_class: str,
        expected_exit: int,
    ) -> tuple[dict[str, Any], Path]:
        interpreter_case_counter[0] += 1
        stem = f"{label}-{interpreter_case_counter[0]}"
        metadata = interpreter_root / f"{stem}.meta.json"
        invocation = subprocess.run(  # ubs:ignore — exact isolated interpreter launches the checked-in evidence supervisor with a fixed planted target.
            [
                sys.executable,
                "-I",
                "-S",
                str(Path(__file__).resolve()),
                "run",
                "--cwd",
                str(interpreter_root),
                "--metadata",
                str(metadata),
                "--stdout",
                str(interpreter_root / f"{stem}.out"),
                "--stderr",
                str(interpreter_root / f"{stem}.err"),
                "--readiness",
                str(interpreter_root / f"{stem}.ready.json"),
                "--artifact-root",
                str(interpreter_root),
                "--capture-bytes",
                "4096",
                "--output-budget-bytes",
                "65536",
                "--timeout-ms",
                "30000",
                "--grace-ms",
                "500",
                "--stage-id",
                stem,
                "--",
                sys.executable,
                "-I",
                "-S",
                "-c",
                (
                    "from pathlib import Path;"
                    f"Path({str(interpreter_target_marker)!r}).write_text('target-ran')"
                ),
            ],
            capture_output=True,
            env=dict(environment),
            timeout=60,
            check=False,
        )
        require(
            invocation.returncode == expected_exit,
            f"sealed interpreter case {label}: exit {invocation.returncode}, "
            f"expected {expected_exit}: {invocation.stderr!r}",
        )
        envelope = read_json_object(metadata)
        validate_supervisor_object(
            metadata, 1, envelope, expected_stage_id=stem
        )
        require(
            envelope["classification"] == expected_class
            and envelope["reason_code"] == expected_reason,
            f"sealed interpreter case {label}: {envelope['classification']}/"
            f"{envelope['reason_code']}, expected {expected_class}/{expected_reason}",
        )
        return envelope, metadata

    hostile_interpreter, hostile_metadata = run_interpreter_case(
        "hostile-pythonpath",
        environment=interpreter_hostile_env,
        expected_reason="sealed_interpreter_hostile_environment",
        expected_class="internal_fault",
        expected_exit=SETUP_FAILURE,
    )
    shadow_after, _shadow_size, _shadow_digest = stable_file_facts(shadow_marker)
    hostile_metadata_bytes, _metadata_size, _metadata_digest = stable_file_facts(
        hostile_metadata
    )
    require(
        shadow_after == shadow_before,
        "sealed interpreter imported the planted PYTHONPATH shadow",
    )
    require(
        not interpreter_target_marker.exists()
        and hostile_interpreter["target_exec"]["status"] == "not_released",
        "hostile Python configuration reached target execution",
    )
    require(
        hostile_interpreter["sealed_interpreter"]["overridden_env"]
        == ["PYTHONPATH"],
        "hostile Python configuration name was not retained exactly",
    )
    require(
        hostile_python_path.encode() not in hostile_metadata_bytes,
        "hostile Python configuration value leaked into evidence",
    )

    recovery_interpreter, recovery_metadata = run_interpreter_case(
        "clean-recovery",
        environment=interpreter_base_env,
        expected_reason="exit_zero",
        expected_class="pass",
        expected_exit=PASS,
    )
    require(
        interpreter_target_marker.read_text() == "target-ran"
        and recovery_interpreter["sealed_interpreter"]["overridden_env"] == []
        and recovery_interpreter["sealed_interpreter"]["flags"]
        == {
            "isolated": True,
            "ignore_environment": True,
            "no_site": True,
            "no_user_site": True,
            "safe_path": True,
        },
        "sealed interpreter did not recover with exact -I -S identity",
    )

    def reject_interpreter_mutation(
        label: str,
        source: dict[str, Any],
        metadata: Path,
        mutate: Callable[[dict[str, Any]], None],
    ) -> None:
        candidate = parse_json(
            canonical_json(source),
            subject=f"sealed interpreter mutation {label}",
        )
        if not isinstance(candidate, dict):
            raise EvidenceError("sealed interpreter mutation source is not an object")
        mutate(candidate)
        try:
            validate_supervisor_object(
                metadata,
                1,
                candidate,
                expected_stage_id=candidate["stage_id"],
            )
        except EvidenceError:
            return
        raise EvidenceError(
            f"sealed interpreter validator accepted mutation: {label}"
        )

    interpreter_mutants = (
        (
            "missing-identity",
            recovery_interpreter,
            recovery_metadata,
            lambda candidate: candidate.pop("sealed_interpreter"),
        ),
        (
            "extra-identity-field",
            recovery_interpreter,
            recovery_metadata,
            lambda candidate: candidate["sealed_interpreter"].__setitem__(
                "unexpected", True
            ),
        ),
        (
            "stale-identity",
            recovery_interpreter,
            recovery_metadata,
            lambda candidate: candidate["sealed_interpreter"].__setitem__(
                "version", "0.0.0-stale"
            ),
        ),
        (
            "remove-no-site",
            recovery_interpreter,
            recovery_metadata,
            lambda candidate: candidate["sealed_interpreter"]["flags"].__setitem__(
                "no_site", False
            ),
        ),
        (
            "drop-python-classification",
            hostile_interpreter,
            hostile_metadata,
            lambda candidate: candidate["sealed_interpreter"].__setitem__(
                "overridden_env", []
            ),
        ),
    )
    for mutant_name, source, metadata, mutate in interpreter_mutants:
        reject_interpreter_mutation(mutant_name, source, metadata, mutate)
    cases.append(
        {
            "case": "sealed_interpreter_validation",
            "ok": True,
            "negative_control": "PYTHONPATH platform.py shadow executed unsealed",
            "typed_reason": "sealed_interpreter_hostile_environment",
            "direct_cli_reasons": [
                "sealed_interpreter_unsealed_startup",
                "sealed_interpreter_hostile_environment",
            ],
            "trusted_shell_refusal": "PYTHONPATH refused before artifact claim",
            "trusted_extraction_recovery": "gen_bignum_vectors --check",
            "mutants_killed": [
                name for name, _source, _metadata, _mutate in interpreter_mutants
            ],
        }
    )

    # --- sealed compiler environment (bead fln-evidence-runner-bootstrap-btk):
    # the hostile-environment matrix, no-mock: every case is a REAL
    # `evidence.py run --sealed-cargo` subprocess. Hostile channels must be
    # rejected typed before any repo-controlled compilation; a planted hostile
    # binary must never execute (marker law); the positive lane must prove the
    # pinned identity end to end when the toolchain is installed.
    sealed_root = case_dir("sealed_compiler_validation")
    sealed_repo = Path(__file__).resolve().parent.parent
    sealed_work = sealed_root / "work"
    sealed_work.mkdir()
    for pin_name in ("SUITE.lock", "rust-toolchain.toml"):
        (sealed_work / pin_name).write_bytes((sealed_repo / pin_name).read_bytes())
    sealed_marker = sealed_root / "HOSTILE-EXECUTED"
    sealed_fake = sealed_root / "fake-tool"
    sealed_fake.write_text(f'#!/bin/sh\ntouch "{sealed_marker}"\nexec "$@"\n')
    sealed_fake.chmod(0o755)
    sealed_lock_rows = parse_rust_lock(sealed_work / "SUITE.lock")
    try:
        sealed_toolchain = resolve_sealed_toolchain(sealed_lock_rows)
    except SealedCompilerRejection:
        sealed_toolchain = None
    sealed_case_counter = [0]

    def run_sealed_case(
        label: str,
        *,
        env_overrides: dict[str, str],
        cwd: Path,
        suite_lock: Path,
        expected_reason: str,
        expected_class: str,
        expected_exit: int,
    ) -> dict[str, Any]:
        sealed_case_counter[0] += 1
        stem = f"{label}-{sealed_case_counter[0]}"
        base_env = {
            "PATH": SEALED_PATH_TAIL,
            "HOME": os.environ.get("HOME", str(Path.home())),
        }
        base_env.update(env_overrides)
        invocation = subprocess.run(
            [
                sys.executable,
                "-I",
                "-S",
                str(Path(__file__).resolve()),
                "run",
                "--cwd",
                str(cwd),
                "--metadata",
                str(sealed_root / f"{stem}.meta.json"),
                "--stdout",
                str(sealed_root / f"{stem}.out"),
                "--stderr",
                str(sealed_root / f"{stem}.err"),
                "--readiness",
                str(sealed_root / f"{stem}.ready.json"),
                "--artifact-root",
                str(sealed_root),
                "--capture-bytes",
                "65536",
                "--output-budget-bytes",
                "1048576",
                "--timeout-ms",
                "120000",
                "--grace-ms",
                "2000",
                "--stage-id",
                stem,
                "--sealed-cargo",
                "--suite-lock",
                str(suite_lock),
                "--sealed-build-root",
                str(sealed_root / "build"),
                "--",
                "cargo",
                "-V",
            ],
            capture_output=True,
            env=base_env,
            timeout=180,
            check=False,
        )
        require(
            invocation.returncode == expected_exit,
            f"sealed case {label}: exit {invocation.returncode}, "
            f"expected {expected_exit}: {invocation.stderr!r}",
        )
        envelope = json.loads((sealed_root / f"{stem}.meta.json").read_text())
        validate_supervisor_object(
            sealed_root / f"{stem}.meta.json", 1, envelope, expected_stage_id=stem
        )
        require(
            envelope["classification"] == expected_class
            and envelope["reason_code"] == expected_reason,
            f"sealed case {label}: {envelope['classification']}/"
            f"{envelope['reason_code']}, expected {expected_class}/{expected_reason}",
        )
        return envelope

    hostile_channels = {
        "sealed_reject_rustflags": {"RUSTFLAGS": "--cap-lints allow"},
        "sealed_reject_encoded_rustflags": {"CARGO_ENCODED_RUSTFLAGS": "--cap-lints\x1fallow"},
        "sealed_reject_target_rustflags": {
            "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS": "--cap-lints allow"
        },
        "sealed_reject_fake_rustc": {"RUSTC": str(sealed_fake)},
        "sealed_reject_wrapper": {"RUSTC_WRAPPER": str(sealed_fake)},
        "sealed_reject_workspace_wrapper": {"RUSTC_WORKSPACE_WRAPPER": str(sealed_fake)},
        "sealed_reject_alt_toolchain": {"RUSTUP_TOOLCHAIN": "stable"},
    }
    for sealed_label, overrides in hostile_channels.items():
        run_sealed_case(
            sealed_label,
            env_overrides=overrides,
            cwd=sealed_work,
            suite_lock=sealed_work / "SUITE.lock",
            expected_reason="sealed_compiler_hostile_environment",
            expected_class="internal_fault",
            expected_exit=SETUP_FAILURE,
        )
    require(
        not sealed_marker.exists(),
        "a planted hostile compiler binary was executed by the sealed lane",
    )

    sealed_config_work = sealed_root / "config-work"
    (sealed_config_work / ".cargo").mkdir(parents=True)
    for pin_name in ("SUITE.lock", "rust-toolchain.toml"):
        (sealed_config_work / pin_name).write_bytes(
            (sealed_repo / pin_name).read_bytes()
        )
    (sealed_config_work / ".cargo" / "config.toml").write_text(
        '[build]\nrustflags = ["--cap-lints", "allow"]\n'
    )
    run_sealed_case(
        "sealed_reject_ambient_config",
        env_overrides={},
        cwd=sealed_config_work,
        suite_lock=sealed_config_work / "SUITE.lock",
        expected_reason="sealed_compiler_ambient_config",
        expected_class="internal_fault",
        expected_exit=SETUP_FAILURE,
    )

    sealed_mismatch_work = sealed_root / "mismatch-work"
    sealed_mismatch_work.mkdir()
    (sealed_mismatch_work / "rust-toolchain.toml").write_bytes(
        (sealed_repo / "rust-toolchain.toml").read_bytes()
    )
    doctored = re.sub(
        r"^rust-commit .*$",
        "rust-commit " + "0" * 40,
        (sealed_repo / "SUITE.lock").read_text(),
        flags=re.MULTILINE,
    )
    (sealed_mismatch_work / "SUITE.lock").write_text(doctored)
    run_sealed_case(
        "sealed_identity_mismatch",
        env_overrides={},
        cwd=sealed_mismatch_work,
        suite_lock=sealed_mismatch_work / "SUITE.lock",
        expected_reason=(
            "sealed_compiler_identity_mismatch"
            if sealed_toolchain is not None
            else "sealed_compiler_toolchain_unresolved"
        ),
        expected_class="internal_fault",
        expected_exit=SETUP_FAILURE,
    )

    if sealed_toolchain is not None:
        positive = run_sealed_case(
            "sealed_positive",
            env_overrides={},
            cwd=sealed_work,
            suite_lock=sealed_work / "SUITE.lock",
            expected_reason="exit_zero",
            expected_class="pass",
            expected_exit=PASS,
        )
        sealed_facts = positive["sealed_compiler"]
        require(
            isinstance(sealed_facts, dict)
            and sealed_facts["commit"] == sealed_lock_rows["rust-commit"]  # ubs:ignore — public compiler commit, not a secret.
            and sealed_facts["release"] == sealed_lock_rows["rust-release"]
            and sealed_facts["channel"] == sealed_lock_rows["rust-nightly"]
            and sealed_facts["effective_argv0"] == sealed_facts["cargo_path"],
            "sealed positive envelope does not bind the locked compiler identity",
        )
        # Clean recovery after every rejection: the positive lane runs green
        # again with nothing left behind by the hostile attempts.
        run_sealed_case(
            "sealed_recovery",
            env_overrides={},
            cwd=sealed_work,
            suite_lock=sealed_work / "SUITE.lock",
            expected_reason="exit_zero",
            expected_class="pass",
            expected_exit=PASS,
        )
        cases.append(
            {
                "case": "sealed_compiler_validation",
                "ok": True,
                "toolchain": sealed_facts["toolchain_root"],
                "commit": sealed_facts["commit"],
            }
        )
    else:
        # Typed limitation: the pinned toolchain is not installed on this
        # host, so the positive/recovery lanes are unverifiable here — the
        # rejection matrix above still ran for real. CI hosts install the pin
        # and exercise the full lane.
        cases.append(
            {
                "case": "sealed_compiler_validation",
                "ok": True,
                "limitation": "pinned toolchain absent; rejection matrix only",
            }
        )

    report = {
        "schema": "fln.evidence-self-test/1",
        "verdict": "pass",
        "created_utc": utc_now(),
        "cases": cases,
    }
    write_new(art_dir / "self-test.json", canonical_json(report))
    print(
        f"evidence self-test: PASS ({len(cases)} cases); artifacts: {art_dir}",
        file=sys.stderr,
    )
    return PASS


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="subcommand", required=True)

    emit_parser = subparsers.add_parser("emit", help="append one encoded NDJSON event")
    emit_parser.add_argument("--file", required=True)
    emit_parser.add_argument("--artifact-root", required=True)
    emit_parser.add_argument("--new-log", action="store_true")
    emit_parser.add_argument("--string", nargs=2, action="append")
    emit_parser.add_argument("--integer", nargs=2, action="append")
    emit_parser.add_argument("--boolean", nargs=2, action="append")
    emit_parser.add_argument("--null", action="append")
    emit_parser.add_argument("--json-value", nargs=2, action="append")
    emit_parser.add_argument("--append-string", nargs=2, action="append")
    emit_parser.add_argument("--json-file", nargs=2, action="append")
    emit_parser.set_defaults(func=cmd_emit)

    run_parser = subparsers.add_parser(
        "run", help="run one command under bounded capture"
    )
    run_parser.add_argument("--cwd", required=True)
    run_parser.add_argument("--metadata", required=True)
    run_parser.add_argument("--stdout", required=True)
    run_parser.add_argument("--stderr", required=True)
    run_parser.add_argument("--readiness", required=True)
    run_parser.add_argument("--artifact-root", required=True)
    run_parser.add_argument("--capture-bytes", type=int, required=True)
    run_parser.add_argument("--output-budget-bytes", type=int, required=True)
    run_parser.add_argument(
        "--setup-timeout-ms", type=int, default=MAX_PROCESS_IDENTITY_WAIT_MS
    )
    run_parser.add_argument("--timeout-ms", type=int, required=True)
    run_parser.add_argument("--grace-ms", type=int, required=True)
    run_parser.add_argument("--stage-id", required=True)
    run_parser.add_argument("--planted", action="store_true")
    run_parser.add_argument("--semantic-failure-exit", type=int, action="append")
    run_parser.add_argument("--cancel-after-ms", type=int)
    run_parser.add_argument("--test-terminal-delay-ms", type=int, default=0)
    run_parser.add_argument("--test-terminal-ready")
    run_parser.add_argument(
        "--test-before-stop-delay-ms",
        type=int,
        default=0,
        help=argparse.SUPPRESS,
    )
    run_parser.add_argument(
        "--test-before-release-delay-ms",
        type=int,
        default=0,
        help=argparse.SUPPRESS,
    )
    run_parser.add_argument(
        "--test-gate-mode",
        choices=("normal", "exit_before_stop", "never_stop", "die_after_stop"),
        default="normal",
        help=argparse.SUPPRESS,
    )
    run_parser.add_argument(
        "--test-fault-point",
        choices=tuple(sorted(SUPERVISOR_TEST_FAULT_POINTS)),
        default="none",
        help=argparse.SUPPRESS,
    )
    run_parser.add_argument("--launch-ready")
    run_parser.add_argument("--launch-release")
    run_parser.add_argument(
        "--test-fail-guardian-pidfd-open",
        action="store_true",
        help=argparse.SUPPRESS,
    )
    run_parser.add_argument(
        "--sealed-cargo",
        action="store_true",
        help="seal the compiler environment: reject hostile channels, verify "
        "the SUITE.lock-pinned toolchain identity, isolate CARGO_HOME/target",
    )
    run_parser.add_argument("--suite-lock", help="path to SUITE.lock for sealing")
    run_parser.add_argument(
        "--sealed-build-root", help="per-attempt isolated build-state root"
    )
    run_parser.add_argument("--test-guardian-child-ready", help=argparse.SUPPRESS)
    run_parser.add_argument("command", nargs=argparse.REMAINDER)
    run_parser.set_defaults(func=cmd_run)

    verification_manifest_parser = subparsers.add_parser(
        "validate-verification-manifest",
        help="validate the governed bead coverage and scenario-activation registry",
    )
    verification_manifest_parser.add_argument("--manifest", required=True)
    verification_manifest_parser.add_argument("--beads", required=True)
    verification_manifest_parser.add_argument("--output")
    verification_manifest_parser.set_defaults(
        func=cmd_validate_verification_manifest
    )

    check_human_parser = subparsers.add_parser(
        "render-check-human",
        help="render the canonical human event log from one fln.check/2 stream",
    )
    check_human_parser.add_argument("--file", required=True)
    check_human_parser.add_argument("--output", required=True)
    check_human_parser.add_argument("--artifact-root", required=True)
    check_human_parser.set_defaults(func=cmd_render_check_human)

    guard_parser = subparsers.add_parser(
        "validate-guard", help="validate exact structure-guard NDJSON semantics"
    )
    guard_parser.add_argument("--file", required=True)
    guard_parser.add_argument("--expected-exit", type=int, required=True)
    guard_parser.add_argument("--expected-verdict", required=True)
    guard_parser.add_argument("--expected-root", required=True)
    guard_parser.add_argument("--observed-exit", type=int, required=True)
    guard_parser.add_argument("--artifact-root", required=True)
    guard_parser.add_argument("--finding", action="append")
    guard_parser.add_argument("--output")
    guard_parser.set_defaults(func=cmd_validate_guard)

    collision_parser = subparsers.add_parser(
        "validate-environment-collision",
        help="validate fln-amv.10 collision detail or mutant evidence",
    )
    collision_parser.add_argument("--file", required=True)
    collision_parser.add_argument("--stderr-file", required=True)
    collision_parser.add_argument(
        "--phase", required=True, choices=("positive", "mutant", "recovery")
    )
    collision_parser.add_argument("--expected-run-id", required=True)
    collision_parser.add_argument("--observed-exit", type=int, required=True)
    collision_parser.add_argument("--expected-cwd")
    collision_parser.add_argument("--expected-argv")
    collision_parser.add_argument("--expected-stdout-artifact", required=True)
    collision_parser.add_argument("--expected-stderr-artifact", required=True)
    collision_parser.add_argument("--expected-cache-state")
    collision_parser.add_argument("--artifact-root", required=True)
    collision_parser.add_argument("--output")
    collision_parser.set_defaults(func=cmd_validate_environment_collision)

    resource_collision_parser = subparsers.add_parser(
        "validate-environment-resource-collision",
        help="validate fln-amv.13 collision resource-bound or mutant evidence",
    )
    resource_collision_parser.add_argument("--file", required=True)
    resource_collision_parser.add_argument("--stderr-file", required=True)
    resource_collision_parser.add_argument(
        "--phase", required=True, choices=("positive", "mutant", "recovery")
    )
    resource_collision_parser.add_argument("--expected-run-id", required=True)
    resource_collision_parser.add_argument(
        "--observed-exit", type=int, required=True
    )
    resource_collision_parser.add_argument("--expected-cwd")
    resource_collision_parser.add_argument("--expected-argv")
    resource_collision_parser.add_argument(
        "--expected-stdout-artifact", required=True
    )
    resource_collision_parser.add_argument(
        "--expected-stderr-artifact", required=True
    )
    resource_collision_parser.add_argument("--expected-cache-state")
    resource_collision_parser.add_argument("--artifact-root", required=True)
    resource_collision_parser.add_argument("--output")
    resource_collision_parser.set_defaults(
        func=cmd_validate_environment_resource_collision
    )

    for command, help_text, command_func in (
        (
            "validate-declaration-tag-matrix",
            "strictly validate the fln-amv.12 declaration-tag matrix",
            cmd_validate_declaration_tag_matrix,
        ),
        (
            "validate-declaration-membership",
            "strictly validate the fln-amv.1 declaration-membership matrix",
            cmd_validate_declaration_membership,
        ),
        (
            "validate-extension-descriptor-matrix",
            "strictly validate the fln-amv.2 extension-descriptor matrix",
            cmd_validate_extension_descriptor_matrix,
        ),
        (
            "validate-environment-state",
            "strictly validate the 41s checkpoint/history identity evidence",
            cmd_validate_environment_state,
        ),
        (
            "validate-declaration-admission",
            "strictly validate the j8h declaration-admission evidence",
            cmd_validate_declaration_admission,
        ),
    ):
        identity_parser = subparsers.add_parser(command, help=help_text)
        identity_parser.add_argument("--file", required=True)
        identity_parser.add_argument("--stderr-file", required=True)
        identity_parser.add_argument("--expected-run-id", required=True)
        identity_parser.add_argument("--observed-exit", type=int, required=True)
        identity_parser.add_argument("--expected-stdout-artifact", required=True)
        identity_parser.add_argument("--expected-stderr-artifact", required=True)
        identity_parser.add_argument("--artifact-root", required=True)
        identity_parser.add_argument("--output")
        identity_parser.set_defaults(func=command_func)

    verdict_parser = subparsers.add_parser(
        "validate-verdict-schema",
        help="independently validate Verdict semantic NDJSON and bounded telemetry",
    )
    verdict_parser.add_argument("--semantic", required=True)
    verdict_parser.add_argument("--telemetry", required=True)
    verdict_parser.add_argument("--stdout", required=True)
    verdict_parser.add_argument("--stderr", required=True)
    verdict_parser.add_argument(
        "--phase", required=True, choices=("positive", "failure", "recovery")
    )
    verdict_parser.add_argument("--observed-exit", type=int, required=True)
    verdict_parser.add_argument("--positive-semantic")
    verdict_parser.add_argument("--artifact-root", required=True)
    verdict_parser.add_argument("--output")
    verdict_parser.set_defaults(func=cmd_validate_verdict_schema)

    admission_parser = subparsers.add_parser(
        "validate-kernel-admission",
        help="validate franken_lean-ap6 kernel admission replay evidence",
    )
    admission_parser.add_argument("--file", required=True)
    admission_parser.add_argument("--stderr-file", required=True)
    admission_parser.add_argument(
        "--phase", required=True, choices=("positive", "recovery")
    )
    admission_parser.add_argument("--expected-run-id", required=True)
    admission_parser.add_argument("--observed-exit", type=int, required=True)
    admission_parser.add_argument("--expected-cwd")
    admission_parser.add_argument("--expected-argv")
    admission_parser.add_argument("--expected-stdout-artifact", required=True)
    admission_parser.add_argument("--expected-stderr-artifact", required=True)
    admission_parser.add_argument("--expected-cache-state")
    admission_parser.add_argument("--expected-input-root")
    admission_parser.add_argument("--artifact-root", required=True)
    admission_parser.add_argument("--output")
    admission_parser.set_defaults(func=cmd_validate_kernel_admission)

    run_validation = subparsers.add_parser(
        "validate-run", help="validate a check/E2E run envelope"
    )
    run_validation.add_argument("--file", required=True)
    run_validation.add_argument("--schema", required=True)
    run_validation.add_argument("--expected-verdict", required=True)
    run_validation.add_argument("--expected-active-stage")
    run_validation.add_argument("--expected-planted-stage")
    run_validation.add_argument("--artifact-root", required=True)
    run_validation.add_argument("--output")
    run_validation.add_argument("--offline", action="store_true")
    run_validation.set_defaults(func=cmd_validate_run)

    supervisor_validation = subparsers.add_parser(
        "validate-supervisor",
        help="read-only validation of one bounded supervisor envelope",
    )
    supervisor_validation.add_argument("--file", required=True)
    supervisor_validation.add_argument("--expected-stage-id", required=True)
    supervisor_validation.add_argument("--artifact-root")
    supervisor_validation.add_argument("--output")
    supervisor_validation.set_defaults(func=cmd_validate_supervisor)

    hash_parser = subparsers.add_parser("hash-tree", help="hash canonical input files")
    hash_parser.add_argument("--root", required=True)
    hash_parser.add_argument("--path", action="append", required=True)
    hash_parser.add_argument("--inventory")
    hash_parser.add_argument("--vendor-path")
    hash_parser.add_argument("--output")
    hash_parser.add_argument("--artifact-root")
    hash_parser.add_argument("--test-mutate-input")
    hash_parser.set_defaults(func=cmd_hash_tree)

    vendor_parser = subparsers.add_parser(
        "vendor-binding",
        help="verify and publish the pinned Reference Git-tree binding",
    )
    vendor_parser.add_argument("--root", required=True)
    vendor_parser.add_argument("--vendor-path", required=True)
    vendor_parser.add_argument("--output")
    vendor_parser.add_argument("--artifact-root")
    vendor_parser.set_defaults(func=cmd_vendor_binding)

    unsafe_note_parser = subparsers.add_parser(
        "unsafe-note-clippy-sites",
        help="extract, compare, or mutate the Clippy unsafe-note site census",
    )
    unsafe_note_parser.add_argument(
        "--operation",
        required=True,
        choices=("extract", "compare", "drop-first", "add-observed", "add-stale"),
    )
    unsafe_note_parser.add_argument("--root")
    unsafe_note_parser.add_argument("--report")
    unsafe_note_parser.add_argument("--declared")
    unsafe_note_parser.add_argument("--observed")
    unsafe_note_parser.add_argument("--output")
    unsafe_note_parser.add_argument("--artifact-root")
    unsafe_note_parser.set_defaults(func=cmd_unsafe_note_clippy_sites)

    inventory_parser = subparsers.add_parser(
        "ubs-inventory", help="publish an exact project-authored UBS file inventory"
    )
    inventory_parser.add_argument("--root", required=True)
    inventory_parser.add_argument(
        "--scope", required=True, choices=("changed", "all-tracked")
    )
    inventory_parser.add_argument("--output", required=True)
    inventory_parser.add_argument("--artifact-root", required=True)
    inventory_parser.set_defaults(func=cmd_ubs_inventory)

    inventory_validation = subparsers.add_parser(
        "validate-ubs-inventory",
        help="verify captured UBS file facts against the workspace",
    )
    inventory_validation.add_argument("--root", required=True)
    inventory_validation.add_argument("--inventory", required=True)
    inventory_validation.add_argument(
        "--require-live-scope",
        action="store_true",
        help="also require the current Git-derived scope to equal the captured scope",
    )
    inventory_validation.set_defaults(func=cmd_validate_ubs_inventory)

    inventory_execution = subparsers.add_parser(
        "exec-ubs-inventory", help="exec a command with validated UBS paths appended"
    )
    inventory_execution.add_argument("--root", required=True)
    inventory_execution.add_argument("--inventory", required=True)
    inventory_execution.add_argument("command", nargs=argparse.REMAINDER)
    inventory_execution.set_defaults(func=cmd_exec_ubs_inventory)

    stopped_exec_parser = subparsers.add_parser(
        "stopped-exec", help="stop before exec for parent-side identity binding"
    )
    stopped_exec_parser.add_argument("--expected-parent-pid", type=int, required=True)
    stopped_exec_parser.add_argument(
        "--exec-status-fd", type=int, help=argparse.SUPPRESS
    )
    stopped_exec_parser.add_argument("command", nargs=argparse.REMAINDER)
    stopped_exec_parser.set_defaults(func=cmd_stopped_exec)

    emergency_parser = subparsers.add_parser(
        "emergency-kill", help="validate readiness and SIGKILL its bound child group"
    )
    emergency_parser.add_argument("--readiness", required=True)
    emergency_parser.add_argument("--expected-wrapper-pid", type=int, required=True)
    emergency_parser.add_argument("--expected-stage-id", required=True)
    emergency_parser.set_defaults(func=cmd_emergency_kill)

    process_identity_parser = subparsers.add_parser(
        "process-start-ticks", help="bind one live session leader's Linux identity"
    )
    process_identity_parser.add_argument("--pid", type=int, required=True)
    process_identity_parser.add_argument(
        "--expected-parent-pid", type=int, required=True
    )
    process_identity_parser.add_argument("--wait-ms", type=int, default=0)
    process_identity_parser.add_argument("--session-leader", action="store_true")
    process_identity_parser.add_argument("--stopped", action="store_true")
    process_identity_parser.set_defaults(func=cmd_process_start_ticks)

    launch_release_parser = subparsers.add_parser(
        "release-process-launch",
        help="release one identity-bound guardian launch gate",
    )
    launch_release_parser.add_argument("--ready", required=True)
    launch_release_parser.add_argument("--output", required=True)
    launch_release_parser.add_argument("--artifact-root", required=True)
    launch_release_parser.add_argument("--stage-id", required=True)
    launch_release_parser.add_argument("--pid", type=int, required=True)
    launch_release_parser.add_argument(
        "--expected-start-ticks", type=int, required=True
    )
    launch_release_parser.add_argument(
        "--expected-parent-pid", type=int, required=True
    )
    launch_release_parser.add_argument("--wait-ms", type=int, default=5000)
    launch_release_parser.set_defaults(func=cmd_release_process_launch)

    bound_group_parser = subparsers.add_parser(
        "kill-bound-group", help="SIGKILL one start-time-bound process group"
    )
    bound_group_parser.add_argument("--pid", type=int, required=True)
    bound_group_parser.add_argument(
        "--expected-start-ticks", type=int, required=True
    )
    bound_group_parser.add_argument(
        "--expected-parent-pid", type=int, required=True
    )
    bound_group_parser.set_defaults(func=cmd_kill_bound_group)

    direct_child_parser = subparsers.add_parser(
        "kill-direct-child", help="pidfd-kill one current direct child"
    )
    direct_child_parser.add_argument("--pid", type=int, required=True)
    direct_child_parser.add_argument(
        "--expected-parent-pid", type=int, required=True
    )
    direct_child_parser.add_argument("--wait-ms", type=int, default=5000)
    direct_child_parser.set_defaults(func=cmd_kill_direct_child)

    bound_process_parser = subparsers.add_parser(
        "signal-bound-process", help="signal one start-time-bound process"
    )
    bound_process_parser.add_argument("--pid", type=int, required=True)
    bound_process_parser.add_argument(
        "--expected-start-ticks", type=int, required=True
    )
    bound_process_parser.add_argument(
        "--signal", choices=("HUP", "INT", "TERM"), required=True
    )
    bound_process_parser.set_defaults(func=cmd_signal_bound_process)

    resume_process_parser = subparsers.add_parser(
        "resume-bound-process",
        help="resume one exact stopped direct child after identity binding",
    )
    resume_process_parser.add_argument("--pid", type=int, required=True)
    resume_process_parser.add_argument(
        "--expected-start-ticks", type=int, required=True
    )
    resume_process_parser.add_argument(
        "--expected-parent-pid", type=int, required=True
    )
    resume_process_parser.set_defaults(func=cmd_resume_bound_process)

    empty_group_parser = subparsers.add_parser(
        "assert-process-group-empty",
        help="boundedly observe that a process group has no live members",
    )
    empty_group_parser.add_argument("--pgid", type=int, required=True)
    empty_group_parser.add_argument("--wait-ms", type=int, default=1000)
    empty_group_parser.set_defaults(func=cmd_assert_process_group_empty)

    manifest_parser = subparsers.add_parser(
        "manifest", help="publish an evidence manifest"
    )
    manifest_parser.add_argument("--art-dir", required=True)
    manifest_parser.add_argument("--output", required=True)
    manifest_parser.add_argument("--digest-output", required=True)
    manifest_parser.add_argument("--run-id", required=True)
    manifest_parser.add_argument("--bead", required=True)
    manifest_parser.add_argument("--scenario", required=True)
    manifest_parser.add_argument("--verdict", required=True)
    manifest_parser.add_argument("--input-root", required=True)
    manifest_parser.add_argument("--final-root", required=True)
    manifest_parser.set_defaults(func=cmd_manifest)

    manifest_validation = subparsers.add_parser(
        "validate-manifest",
        help="verify every manifested artifact and terminal binding",
    )
    manifest_validation.add_argument("--art-dir", required=True)
    manifest_validation.add_argument("--manifest", required=True)
    manifest_validation.add_argument("--digest", required=True)
    manifest_validation.add_argument("--offline", action="store_true")
    manifest_validation.set_defaults(func=cmd_validate_manifest)

    complete_parser = subparsers.add_parser(
        "complete-bundle", help="commit a fully validated evidence bundle"
    )
    complete_parser.add_argument("--art-dir", required=True)
    complete_parser.add_argument("--manifest", required=True)
    complete_parser.add_argument("--digest", required=True)
    complete_parser.add_argument("--output", required=True)
    complete_parser.add_argument("--governed-root", required=True)
    complete_parser.add_argument("--governed-path", action="append", required=True)
    complete_parser.add_argument("--expected-root", required=True)
    complete_parser.add_argument("--inventory")
    complete_parser.add_argument("--vendor-path")
    complete_parser.add_argument("--test-fail-after-link", action="store_true")
    complete_parser.add_argument("--test-marker-pause-ready")
    complete_parser.add_argument("--test-marker-pause-release")
    complete_parser.set_defaults(func=cmd_complete_bundle)

    bundle_validation = subparsers.add_parser(
        "validate-bundle", help="verify a committed evidence bundle (read-only)"
    )
    bundle_validation.add_argument("--art-dir", required=True)
    bundle_validation.add_argument("--manifest", required=True)
    bundle_validation.add_argument("--digest", required=True)
    bundle_validation.add_argument("--commit", required=True)
    bundle_validation.add_argument("--artifact-root", required=True)
    bundle_validation.add_argument("--output")
    bundle_validation.set_defaults(func=cmd_validate_bundle)

    partial_publication = subparsers.add_parser(
        "publish-partial-bundle",
        help="publish the typed durable partial bundle for an early fault",
    )
    partial_publication.add_argument("--art-dir", required=True)
    partial_publication.add_argument("--run-id", required=True)
    partial_publication.add_argument("--bead", required=True)
    partial_publication.add_argument("--scenario", required=True)
    partial_publication.add_argument("--step", required=True)
    partial_publication.add_argument("--reason", required=True)
    partial_publication.add_argument(
        "--classification",
        required=True,
        choices=sorted(PARTIAL_BUNDLE_CLASSIFICATIONS),
    )
    partial_publication.add_argument("--argv-json", required=True)
    partial_publication.add_argument("--cwd", required=True)
    partial_publication.set_defaults(func=cmd_publish_partial_bundle)

    partial_validation = subparsers.add_parser(
        "validate-partial-bundle",
        help="verify a published early-fault partial bundle (read-only)",
    )
    partial_validation.add_argument("--art-dir", required=True)
    partial_validation.add_argument("--artifact-root", required=True)
    partial_validation.add_argument("--output")
    partial_validation.set_defaults(func=cmd_validate_partial_bundle)

    bundle_adoption = subparsers.add_parser(
        "adopt-bundle",
        help="recover a winning pre-marker bundle decision, then revalidate",
    )
    bundle_adoption.add_argument("--art-dir", required=True)
    bundle_adoption.add_argument("--manifest", required=True)
    bundle_adoption.add_argument("--digest", required=True)
    bundle_adoption.add_argument("--commit", required=True)
    bundle_adoption.add_argument("--artifact-root", required=True)
    bundle_adoption.add_argument("--output")
    bundle_adoption.set_defaults(func=cmd_adopt_bundle)

    self_test_parser = subparsers.add_parser(
        "self-test", help="exercise capture, cancellation, exhaustion, and validation"
    )
    self_test_parser.add_argument("--art-dir", required=True)
    self_test_parser.set_defaults(func=cmd_self_test)
    return parser


def main() -> int:
    try:
        signal.signal(signal.SIGCHLD, signal.SIG_DFL)
        args = build_parser().parse_args()
        # The supervisor has its own structured rejection path because it owns
        # the metadata envelope needed to prove that no target was released.
        # Every other evidence command still refuses an unsealed interpreter
        # here. Trusted shell launchers structurally supply -I -S before imports;
        # this runtime check is defense in depth for direct CLI use.
        if args.subcommand != "run":
            prepare_sealed_interpreter(os.environ)
        return int(args.func(args))
    except SealedInterpreterRejection as error:
        print(
            f"evidence: {error.reason_token}: {error}",
            file=sys.stderr,
        )
        return SETUP_FAILURE
    except (
        EvidenceError,
        OSError,
        ValueError,
        TypeError,
        KeyError,
        IndexError,
    ) as error:
        print(f"evidence: {error}", file=sys.stderr)
        return SETUP_FAILURE


if __name__ == "__main__":
    raise SystemExit(main())
