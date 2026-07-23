#!/usr/bin/env bash
# kernel_contract_ownership.sh — no-mock ownership-evidence matrix for
# KERNEL_CONTRACT.md (bead franken_lean-79k.1).
#
# This lane deliberately does not use scripts/check.sh or scripts/evidence.py.
# Every fixture is immutable and retained: negative cases are created in their own
# directories, never planted into (or restored over) the authoritative worktree.

set -euo pipefail
set -C
umask 077
export LC_ALL=C
export CARGO_TERM_COLOR=never

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RCH_BRIDGE_ENTERED=false

DEFAULT_MAX_FILE_BYTES=8388608
DEFAULT_MAX_LINE_BYTES=262144
DEFAULT_MAX_RECORDS=100000
DEFAULT_MAX_ID_BYTES=256
DEFAULT_MAX_PARSE_DEPTH=128
DEFAULT_MAX_DIAGNOSTIC_BYTES=4096

sha256_file() {
  sha256sum "$1" | cut -d' ' -f1
}

bytes_file() {
  wc -c < "$1" | tr -d ' '
}

ownership_scenarios() {
  printf '%s\n' \
    duplicate \
    empty \
    malformed \
    missing \
    missing_source \
    noncanonical \
    phantom \
    positive \
    recovery \
    resource_depth_exact \
    resource_depth_one_over \
    resource_depth_zero \
    resource_file_exact \
    resource_file_one_over \
    resource_file_zero \
    resource_id_exact \
    resource_id_one_over \
    resource_id_zero \
    resource_line_exact \
    resource_line_one_over \
    resource_line_zero \
    resource_records_exact \
    resource_records_one_over \
    resource_records_zero \
    stale \
    unreadable
}

validator_selftest_mutants() {
  printf '%s\n' missing extra stale mismatched
}

scenario_has_source_fixture() {
  local lane="$1"
  local scenario="$2"
  if [[ "$scenario" == "resource_depth_one_over" ]]; then
    return 0
  fi
  [[ "$lane" != "rch" ]] || return 1
  case "$scenario" in
    positive|missing|unreadable|malformed|empty|duplicate|noncanonical|stale|phantom|\
      resource_file_zero|resource_file_one_over|\
      resource_line_zero|resource_line_one_over|\
      resource_records_zero|resource_records_one_over|\
      resource_id_zero|resource_id_one_over|\
      resource_depth_zero|recovery)
      return 0
      ;;
    *)
      return 1
      ;;
  esac
}

scenario_has_canonical_manifest() {
  case "$1" in
    missing_source|phantom|positive|recovery|resource_*)
      return 0
      ;;
    *)
      return 1
      ;;
  esac
}

expected_artifact_paths() {
  local lane="$1"
  local scenario
  local mutant
  printf '%s\n' run.ndjson validation.json
  while IFS= read -r scenario; do
    printf 'cases/%s/stdout.log\n' "$scenario"
    printf 'cases/%s/stderr.log\n' "$scenario"
    printf 'cases/%s/result.json\n' "$scenario"
    case "$scenario" in
      missing)
        ;;
      unreadable)
        printf 'cases/%s/root/ci/KERNEL_CONTRACT_OWNERSHIP.jsonl/.retained-directory-fixture\n' \
          "$scenario"
        ;;
      *)
        printf 'cases/%s/root/ci/KERNEL_CONTRACT_OWNERSHIP.jsonl\n' "$scenario"
        ;;
    esac
    if scenario_has_source_fixture "$lane" "$scenario"; then
      printf 'cases/%s/root/.beads/issues.jsonl\n' "$scenario"
    fi
  done < <(ownership_scenarios)
  while IFS= read -r mutant; do
    printf 'selftest-%s.ndjson\n' "$mutant"
    printf 'selftest-%s-validator.stdout\n' "$mutant"
    printf 'selftest-%s-validator.stderr\n' "$mutant"
  done < <(validator_selftest_mutants)
}

emit_parent_directories() {
  local path="$1"
  while [[ "$path" == */* ]]; do
    path="${path%/*}"
    printf '%s\n' "$path"
  done
}

expected_directory_paths() {
  local lane="$1"
  local path
  local scenario
  while IFS= read -r path; do
    emit_parent_directories "$path"
  done < <(expected_artifact_paths "$lane")
  while IFS= read -r scenario; do
    printf 'cases/%s/root\n' "$scenario"
  done < <(ownership_scenarios)
}

max_line_bytes_file() {
  awk '
    {
      bytes = length($0)
      if (bytes > maximum) {
        maximum = bytes
      }
    }
    END { print maximum + 0 }
  ' "$1"
}

manifest_record_count_file() {
  local lines
  lines="$(wc -l < "$1" | tr -d ' ')" || return 1
  if (( lines == 0 )); then
    printf '0\n'
  else
    printf '%s\n' "$((lines - 1))"
  fi
}

manifest_max_id_bytes_file() {
  tail -n +2 "$1" \
    | sed -n 's/^{"id":"\([^"]*\)"}$/\1/p' \
    | awk '{ if (length > maximum) maximum = length } END { print maximum + 0 }'
}

manifest_first_id_bytes_file() {
  sed -n '2s/^{"id":"\([^"]*\)"}$/\1/p' "$1" \
    | awk 'NR == 1 { print length; found = 1 } END { if (!found) print 0 }'
}

prefix_max_line_bytes_file() {
  local path="$1"
  local lines="$2"
  awk -v lines="$lines" '
    NR <= lines && length($0) > maximum {
      maximum = length($0)
    }
    END { print maximum + 0 }
  ' "$path"
}

manifest_prefix_max_id_bytes_file() {
  local path="$1"
  local records="$2"
  sed -n 's/^{"id":"\([^"]*\)"}$/\1/p' "$path" \
    | awk -v records="$records" '
        NR <= records && length($0) > maximum {
          maximum = length($0)
        }
        END { print maximum + 0 }
      '
}

manifest_first_id_over_limit_record() {
  local path="$1"
  local limit="$2"
  sed -n 's/^{"id":"\([^"]*\)"}$/\1/p' "$path" \
    | awk -v limit="$limit" '
        length($0) > limit {
          print NR
          found = 1
          exit
        }
        END {
          if (!found) {
            print 0
          }
        }
      '
}

source_record_count_file() {
  awk 'END { print NR + 0 }' "$1"
}

source_max_id_bytes_file() {
  jq -er '
    if (.id | type) == "string"
    then .id
    else error("source row is missing a string id")
    end
  ' "$1" \
    | awk '{ if (length > maximum) maximum = length } END { print maximum + 0 }'
}

source_first_id_bytes_file() {
  sed -n '1p' "$1" \
    | jq -er '
        if (.id | type) == "string"
        then .id
        else error("source row is missing a string id")
        end
      ' \
    | awk 'NR == 1 { print length; found = 1 } END { if (!found) print 0 }'
}

jsonl_max_parse_depth_file() {
  jq -s '
    def container_depth:
      if type == "object"
      then 1 + ([.[] | container_depth] | max // 0)
      elif type == "array"
      then 1 + ([.[] | container_depth] | max // 0)
      else 0
      end;
    [.[] | container_depth] | max // 0
  ' "$1"
}

strict_validate_run_ndjson() {
  local log_path="$1"
  local expected_records="$2"
  local expected_schema="$3"
  local expected_run_id="$4"
  local expected_bead="$5"
  local expected_lane="$6"
  local expected_commit="$7"
  local expected_tree="$8"
  local expected_manifest_hash="$9"
  local expected_projection_hash="${10}"
  jq -s -e \
    --arg schema "$expected_schema" \
    --arg run_id "$expected_run_id" \
    --arg bead "$expected_bead" \
    --arg lane "$expected_lane" \
    --arg commit "$expected_commit" \
    --arg tree "$expected_tree" \
    --arg expected_manifest_hash "$expected_manifest_hash" \
    --arg expected_projection_hash "$expected_projection_hash" \
    --argjson expected_records "$expected_records" '
      def nonnegative_integer:
        type == "number" and . >= 0 and floor == .;
      def document_usage:
        (keys == [
          "file_bytes","id_bytes","line_bytes","parse_depth","records"
        ])
        and ([.file_bytes,.id_bytes,.line_bytes,.parse_depth,.records]
          | all(.[]; nonnegative_integer));
      def expected_grade:
        if (
          .scenario == "positive"
          or .scenario == "recovery"
          or .scenario == "phantom"
          or (.scenario | endswith("_exact"))
        )
        then (
          if $lane == "rch" or (.scenario | endswith("_exact"))
          then "manifest-only"
          else "source-bound"
          end
        )
        else "none"
        end;
      def expected_source_state:
        if .scenario == "resource_depth_one_over"
        then "present"
        elif (
          .scenario == "missing_source"
          or (.scenario | endswith("_exact"))
          or (
            $lane == "rch"
            and (
              .scenario == "positive"
              or .scenario == "recovery"
              or .scenario == "phantom"
            )
          )
        )
        then "absent"
        elif (
          ($lane == "local" or $lane == "clean")
          and (
            .scenario == "positive"
            or .scenario == "recovery"
            or .scenario == "phantom"
          )
        )
        then "present-verified"
        else "not-attempted"
        end;
      ($lane == "local" or $lane == "clean" or $lane == "rch")
      and ($commit | test("^[0-9a-f]{40}$"))
      and ($tree | test("^[0-9a-f]{40}$"))
      and ($expected_manifest_hash | test("^[0-9a-f]{64}$"))
      and ($expected_projection_hash | test("^[0-9a-f]{64}$"))
      and ($run_id | test(
        "^kernel-contract-ownership-(local|clean|rch)-[0-9]{8}T[0-9]{6}Z-[0-9]+$"
      ))
      and ($run_id | startswith("kernel-contract-ownership-" + $lane + "-"))
      and length == $expected_records
      and (
        ([.[].scenario] | sort) == [
          "duplicate","empty","malformed","missing","missing_source",
          "noncanonical","phantom","positive","recovery",
          "resource_depth_exact","resource_depth_one_over","resource_depth_zero",
          "resource_file_exact","resource_file_one_over","resource_file_zero",
          "resource_id_exact","resource_id_one_over","resource_id_zero",
          "resource_line_exact","resource_line_one_over","resource_line_zero",
          "resource_records_exact","resource_records_one_over",
          "resource_records_zero","stale","unreadable"
        ]
      )
      and all(.[];
        (keys == [
          "actual","bead","build","cleanup_result","command","evidence",
          "expected","final_recovery_state","lane","limits_configured",
          "limits_consumed","result","run_id","scenario","schema","status",
          "stderr","stdout","worker"
        ])
        and .schema == $schema
        and .run_id == $run_id
        and .bead == $bead
        and .lane == $lane
        and .status == "passed"
        and .cleanup_result == "retained_by_policy"
        and .final_recovery_state == "authoritative_inputs_unchanged"
        and .command == [
          "cargo","test","--locked","-q","-p","fln-conformance",
          "--test","kernel_contract","ownership_evidence_process_driver",
          "--","--exact","--nocapture"
        ]
        and (.build | keys == ["commit","rustc_commit","target","tree"])
        and .build.commit == $commit
        and .build.tree == $tree
        and (.build.rustc_commit | test("^[0-9a-f]{40}$"))
        and (.build.target | type == "string" and length > 0)
        and (.worker | keys == ["identity","remote_required"])
        and (.worker.identity | type == "string" and length > 0)
        and .worker.remote_required == ($lane == "rch")
        and (.evidence | keys == [
          "grade","manifest_hash","path","projection_hash",
          "provenance_source","sha256"
        ])
        and .evidence.path == (
          "cases/" + .scenario
          + "/root/ci/KERNEL_CONTRACT_OWNERSHIP.jsonl"
        )
        and .evidence.provenance_source == ".beads/issues.jsonl"
        and (
          .evidence.sha256 == "missing"
          or .evidence.sha256 == "nonregular"
          or (.evidence.sha256 | test("^[0-9a-f]{64}$"))
        )
        and (.limits_configured | keys == [
          "max_diagnostic_bytes","max_file_bytes","max_id_bytes",
          "max_line_bytes","max_parse_depth","max_records"
        ])
        and ([
          .limits_configured.max_diagnostic_bytes,
          .limits_configured.max_file_bytes,
          .limits_configured.max_id_bytes,
          .limits_configured.max_line_bytes,
          .limits_configured.max_parse_depth,
          .limits_configured.max_records
        ] | all(.[]; nonnegative_integer))
        and .limits_configured.max_diagnostic_bytes == 4096
        and (.limits_consumed | keys == [
          "manifest","required_owners","source","source_state"
        ])
        and (.limits_consumed.manifest | document_usage)
        and (.limits_consumed.source | document_usage)
        and .limits_consumed.source_state == expected_source_state
        and .limits_consumed.required_owners == 1
        and (.actual | keys == ["classification","exit_code"])
        and (.actual.exit_code | type == "number" and floor == .)
        and (.expected | keys == ["classification","exit"])
        and .expected.classification == ({
          positive:"ok",
          recovery:"ok",
          missing:"missing",
          missing_source:"missing",
          unreadable:"unreadable",
          malformed:"malformed",
          empty:"empty",
          duplicate:"duplicate-id",
          noncanonical:"noncanonical",
          stale:"stale-binding",
          phantom:"phantom-owner",
          resource_file_exact:"ok",
          resource_file_zero:"resource-exhausted/file-bytes",
          resource_file_one_over:"resource-exhausted/file-bytes",
          resource_line_exact:"ok",
          resource_line_zero:"resource-exhausted/line-bytes",
          resource_line_one_over:"resource-exhausted/line-bytes",
          resource_records_exact:"ok",
          resource_records_zero:"resource-exhausted/records",
          resource_records_one_over:"resource-exhausted/records",
          resource_id_exact:"ok",
          resource_id_zero:"resource-exhausted/id-bytes",
          resource_id_one_over:"resource-exhausted/id-bytes",
          resource_depth_exact:"ok",
          resource_depth_zero:"resource-exhausted/parse-depth",
          resource_depth_one_over:"resource-exhausted/parse-depth"
        }[.scenario])
        and .expected.exit == (
          if (
            .scenario == "positive"
            or .scenario == "recovery"
            or (.scenario | endswith("_exact"))
          )
          then "zero" else "nonzero" end
        )
        and .actual.classification == .expected.classification
        and (
          (.expected.exit == "zero" and .actual.exit_code == 0)
          or (.expected.exit == "nonzero" and .actual.exit_code != 0)
        )
        and (.stdout | keys == ["bytes","path","sha256"])
        and (.stderr | keys == ["bytes","path","sha256"])
        and (.result | keys == ["bytes","path","sha256"])
        and .stdout.path == ("cases/" + .scenario + "/stdout.log")
        and .stderr.path == ("cases/" + .scenario + "/stderr.log")
        and .result.path == ("cases/" + .scenario + "/result.json")
        and (.stdout.sha256 | test("^[0-9a-f]{64}$"))
        and (.stderr.sha256 | test("^[0-9a-f]{64}$"))
        and (.result.sha256 | test("^[0-9a-f]{64}$"))
        and (.stdout.bytes | nonnegative_integer)
        and (.stderr.bytes | nonnegative_integer)
        and (.result.bytes | nonnegative_integer)
        and .result.bytes > 0
        and .stdout.bytes <= 262144
        and .stderr.bytes <= 262144
        and .result.bytes <= 262144
        and (
          if .scenario == "resource_file_zero"
          then .limits_consumed.manifest.file_bytes
            > .limits_configured.max_file_bytes
          elif .scenario == "resource_file_exact"
          then .limits_consumed.manifest.file_bytes
            == .limits_configured.max_file_bytes
          elif .scenario == "resource_file_one_over"
          then .limits_consumed.manifest.file_bytes
            == (.limits_configured.max_file_bytes + 1)
          elif .scenario == "resource_line_zero"
          then .limits_consumed.manifest.line_bytes
            > .limits_configured.max_line_bytes
          elif .scenario == "resource_line_exact"
          then .limits_consumed.manifest.line_bytes
            == .limits_configured.max_line_bytes
          elif .scenario == "resource_line_one_over"
          then .limits_consumed.manifest.line_bytes
            == (.limits_configured.max_line_bytes + 1)
          elif .scenario == "resource_records_zero"
          then .limits_consumed.manifest.records
            > .limits_configured.max_records
          elif .scenario == "resource_records_exact"
          then .limits_consumed.manifest.records
            == .limits_configured.max_records
          elif .scenario == "resource_records_one_over"
          then .limits_consumed.manifest.records
            == (.limits_configured.max_records + 1)
          elif .scenario == "resource_id_zero"
          then .limits_consumed.manifest.id_bytes
            > .limits_configured.max_id_bytes
          elif .scenario == "resource_id_exact"
          then .limits_consumed.manifest.id_bytes
            == .limits_configured.max_id_bytes
          elif .scenario == "resource_id_one_over"
          then .limits_consumed.manifest.id_bytes
            == (.limits_configured.max_id_bytes + 1)
          elif .scenario == "resource_depth_zero"
          then .limits_consumed.manifest.parse_depth
            > .limits_configured.max_parse_depth
          elif .scenario == "resource_depth_exact"
          then .limits_consumed.manifest.parse_depth
            == .limits_configured.max_parse_depth
          elif .scenario == "resource_depth_one_over"
          then .limits_consumed.source.parse_depth
            == (.limits_configured.max_parse_depth + 1)
          else (
            .limits_consumed.manifest.file_bytes
              <= .limits_configured.max_file_bytes
            and .limits_consumed.manifest.line_bytes
              <= .limits_configured.max_line_bytes
            and .limits_consumed.manifest.records
              <= .limits_configured.max_records
            and .limits_consumed.manifest.id_bytes
              <= .limits_configured.max_id_bytes
            and .limits_consumed.manifest.parse_depth
              <= .limits_configured.max_parse_depth
            and .limits_consumed.source.file_bytes
              <= .limits_configured.max_file_bytes
            and .limits_consumed.source.line_bytes
              <= .limits_configured.max_line_bytes
            and .limits_consumed.source.records
              <= .limits_configured.max_records
            and .limits_consumed.source.id_bytes
              <= .limits_configured.max_id_bytes
            and .limits_consumed.source.parse_depth
              <= .limits_configured.max_parse_depth
          )
          end
        )
        and .evidence.grade == expected_grade
        and (
          if expected_grade == "none"
          then (
            .evidence.manifest_hash == ""
            and .evidence.projection_hash == ""
          )
          elif expected_grade == "source-bound"
          then (
            .evidence.manifest_hash == $expected_manifest_hash
            and .evidence.projection_hash == $expected_projection_hash
            and .limits_consumed.source_state == "present-verified"
          )
          else (
            .evidence.manifest_hash == $expected_manifest_hash
            and .evidence.projection_hash == $expected_projection_hash
            and .limits_consumed.source_state == "absent"
          )
          end
        )
      )
    ' "$log_path" >/dev/null
}

strict_validate_artifact_links() {
  local bundle_dir="$1"
  local log_path="$2"
  local lane="$3"
  local result_schema="$4"
  local expected_manifest_hash="$5"
  local expected_projection_hash="$6"
  local authoritative_manifest_sha="$7"
  local authoritative_source_sha="$8"
  local scenario
  local rel
  local expected_class
  local recorded_limits
  local recorded_usage
  local expected_grade
  local expected_source_state
  local result_file
  local manifest_path
  local source_path
  local manifest_bytes
  local source_bytes
  local manifest_line_bytes
  local manifest_header_line_bytes
  local manifest_records
  local manifest_max_id_bytes
  local source_line_bytes
  local source_records
  local source_max_id_bytes
  local source_parse_depth
  local expected_manifest_file_bytes
  local expected_manifest_line_bytes
  local expected_manifest_records
  local expected_manifest_id_bytes
  local expected_manifest_parse_depth
  local expected_source_file_bytes
  local expected_source_line_bytes
  local expected_source_records
  local expected_source_id_bytes
  local expected_source_parse_depth
  local expected_max_file_bytes
  local expected_max_line_bytes
  local expected_max_records
  local expected_max_id_bytes
  local expected_max_parse_depth
  local id_failure_record
  local linked_artifact_rows
  local case_rows
  local evidence_rows

  linked_artifact_rows="$(
    jq -r '.stdout, .stderr, .result | [.path,.sha256,(.bytes|tostring)] | @tsv' \
      "$log_path"
  )" || return 1
  while IFS=$'\t' read -r rel expected_sha expected_bytes; do
    [[ "$rel" != /* && "$rel" != *".."* ]] || return 1
    local artifact="$bundle_dir/$rel"
    [[ -f "$artifact" && ! -L "$artifact" ]] || return 1
    [[ "$(sha256_file "$artifact")" == "$expected_sha" ]] || return 1
    [[ "$(bytes_file "$artifact")" == "$expected_bytes" ]] || return 1
  done <<< "$linked_artifact_rows"

  case_rows="$(
    jq -r '
      [.scenario,.result.path,.actual.classification,
       (.limits_configured|tojson),(.limits_consumed|tojson)] | @tsv
    ' "$log_path"
  )" || return 1
  while IFS=$'\t' read -r \
      scenario rel expected_class recorded_limits recorded_usage; do
    result_file="$bundle_dir/$rel"
    case "$scenario" in
      positive|recovery|phantom)
        if [[ "$lane" == "rch" ]]; then
          expected_grade="manifest-only"
          expected_source_state="absent"
        else
          expected_grade="source-bound"
          expected_source_state="present-verified"
        fi
        ;;
      *_exact)
        expected_grade="manifest-only"
        expected_source_state="absent"
        ;;
      missing_source)
        expected_grade="none"
        expected_source_state="absent"
        ;;
      resource_depth_one_over)
        expected_grade="none"
        expected_source_state="present"
        ;;
      *)
        expected_grade="none"
        expected_source_state="not-attempted"
        ;;
    esac
    manifest_path="$bundle_dir/cases/$scenario/root/ci/KERNEL_CONTRACT_OWNERSHIP.jsonl"
    source_path="$bundle_dir/cases/$scenario/root/.beads/issues.jsonl"
    manifest_bytes=0
    source_bytes=0
    manifest_line_bytes=0
    manifest_header_line_bytes=0
    manifest_records=0
    manifest_max_id_bytes=0
    source_line_bytes=0
    source_records=0
    source_max_id_bytes=0
    source_parse_depth=0
    if [[ -f "$manifest_path" && ! -L "$manifest_path" ]]; then
      manifest_bytes="$(bytes_file "$manifest_path")" || return 1
      manifest_line_bytes="$(max_line_bytes_file "$manifest_path")" || return 1
      manifest_header_line_bytes="$(
        prefix_max_line_bytes_file "$manifest_path" 1
      )" || return 1
      manifest_records="$(manifest_record_count_file "$manifest_path")" || return 1
      manifest_max_id_bytes="$(
        manifest_max_id_bytes_file "$manifest_path"
      )" || return 1
    fi
    if [[ -f "$source_path" && ! -L "$source_path" ]]; then
      source_bytes="$(bytes_file "$source_path")" || return 1
      source_line_bytes="$(max_line_bytes_file "$source_path")" || return 1
      source_records="$(source_record_count_file "$source_path")" || return 1
      source_max_id_bytes="$(source_max_id_bytes_file "$source_path")" || return 1
      source_parse_depth="$(jsonl_max_parse_depth_file "$source_path")" || return 1
    fi

    expected_manifest_file_bytes=0
    expected_manifest_line_bytes=0
    expected_manifest_records=0
    expected_manifest_id_bytes=0
    expected_manifest_parse_depth=0
    expected_source_file_bytes=0
    expected_source_line_bytes=0
    expected_source_records=0
    expected_source_id_bytes=0
    expected_source_parse_depth=0
    expected_max_file_bytes="$DEFAULT_MAX_FILE_BYTES"
    expected_max_line_bytes="$DEFAULT_MAX_LINE_BYTES"
    expected_max_records="$DEFAULT_MAX_RECORDS"
    expected_max_id_bytes="$DEFAULT_MAX_ID_BYTES"
    expected_max_parse_depth="$DEFAULT_MAX_PARSE_DEPTH"

    case "$scenario" in
      positive|recovery|phantom|missing_source|stale|resource_*_exact|\
        resource_depth_one_over)
        expected_manifest_file_bytes="$manifest_bytes"
        expected_manifest_line_bytes="$manifest_line_bytes"
        expected_manifest_records="$manifest_records"
        expected_manifest_id_bytes="$manifest_max_id_bytes"
        expected_manifest_parse_depth=1
        ;;
      duplicate)
        expected_manifest_file_bytes="$manifest_bytes"
        expected_manifest_line_bytes="$manifest_line_bytes"
        expected_manifest_records=2
        expected_manifest_id_bytes="$manifest_max_id_bytes"
        expected_manifest_parse_depth=1
        ;;
      noncanonical)
        expected_manifest_file_bytes="$manifest_bytes"
        expected_manifest_line_bytes="$manifest_line_bytes"
        expected_manifest_records=1
        expected_manifest_id_bytes="$(
          manifest_first_id_bytes_file \
            "$bundle_dir/cases/positive/root/ci/KERNEL_CONTRACT_OWNERSHIP.jsonl"
        )" || return 1
        expected_manifest_parse_depth=1
        ;;
      malformed)
        expected_manifest_file_bytes="$manifest_bytes"
        expected_manifest_line_bytes="$manifest_line_bytes"
        expected_manifest_parse_depth=1
        ;;
      resource_file_zero|resource_file_one_over)
        expected_manifest_file_bytes="$manifest_bytes"
        ;;
      resource_line_zero|resource_line_one_over)
        expected_manifest_file_bytes="$manifest_bytes"
        expected_manifest_line_bytes="$manifest_header_line_bytes"
        ;;
      resource_records_zero)
        expected_manifest_file_bytes="$manifest_bytes"
        expected_manifest_line_bytes="$(
          prefix_max_line_bytes_file "$manifest_path" 2
        )" || return 1
        expected_manifest_records=1
        expected_manifest_parse_depth=1
        ;;
      resource_records_one_over)
        expected_manifest_file_bytes="$manifest_bytes"
        expected_manifest_line_bytes="$manifest_line_bytes"
        expected_manifest_records="$manifest_records"
        expected_manifest_id_bytes="$(
          manifest_prefix_max_id_bytes_file \
            "$manifest_path" "$((manifest_records - 1))"
        )" || return 1
        expected_manifest_parse_depth=1
        ;;
      resource_id_zero|resource_id_one_over)
        if [[ "$scenario" == "resource_id_zero" ]]; then
          expected_max_id_bytes=0
        else
          expected_max_id_bytes="$((manifest_max_id_bytes - 1))"
        fi
        id_failure_record="$(
          manifest_first_id_over_limit_record \
            "$manifest_path" "$expected_max_id_bytes"
        )" || return 1
        (( id_failure_record > 0 )) || return 1
        expected_manifest_file_bytes="$manifest_bytes"
        expected_manifest_line_bytes="$(
          prefix_max_line_bytes_file \
            "$manifest_path" "$((id_failure_record + 1))"
        )" || return 1
        expected_manifest_records="$id_failure_record"
        expected_manifest_id_bytes="$((expected_max_id_bytes + 1))"
        expected_manifest_parse_depth=1
        ;;
      resource_depth_zero)
        expected_manifest_file_bytes="$manifest_bytes"
        expected_manifest_line_bytes="$manifest_header_line_bytes"
        expected_manifest_parse_depth=1
        ;;
      empty|missing|unreadable)
        ;;
      *)
        return 1
        ;;
    esac

    case "$scenario" in
      positive|recovery|phantom)
        if [[ "$lane" != "rch" ]]; then
          expected_source_file_bytes="$source_bytes"
          expected_source_line_bytes="$source_line_bytes"
          expected_source_records="$source_records"
          expected_source_id_bytes="$source_max_id_bytes"
          expected_source_parse_depth="$source_parse_depth"
        fi
        ;;
      resource_depth_one_over)
        expected_source_file_bytes="$source_bytes"
        expected_source_line_bytes="$(
          prefix_max_line_bytes_file "$source_path" 1
        )" || return 1
        expected_source_records=1
        expected_source_id_bytes="$(
          source_first_id_bytes_file "$source_path"
        )" || return 1
        expected_source_parse_depth=2
        ;;
    esac

    case "$scenario" in
      resource_file_zero) expected_max_file_bytes=0 ;;
      resource_file_exact) expected_max_file_bytes="$manifest_bytes" ;;
      resource_file_one_over)
        expected_max_file_bytes="$((manifest_bytes - 1))"
        ;;
      resource_line_zero) expected_max_line_bytes=0 ;;
      resource_line_exact)
        expected_max_line_bytes="$manifest_header_line_bytes"
        ;;
      resource_line_one_over)
        expected_max_line_bytes="$((manifest_header_line_bytes - 1))"
        ;;
      resource_records_zero) expected_max_records=0 ;;
      resource_records_exact) expected_max_records="$manifest_records" ;;
      resource_records_one_over)
        expected_max_records="$((manifest_records - 1))"
        ;;
      resource_id_exact) expected_max_id_bytes="$manifest_max_id_bytes" ;;
      resource_depth_zero) expected_max_parse_depth=0 ;;
      resource_depth_exact|resource_depth_one_over)
        expected_max_parse_depth=1
        ;;
    esac

    jq -e \
      --arg schema "$result_schema" \
      --arg expected_class "$expected_class" \
      --arg expected_grade "$expected_grade" \
      --arg expected_source_state "$expected_source_state" \
      --arg expected_manifest_hash "$expected_manifest_hash" \
      --arg expected_projection_hash "$expected_projection_hash" \
      --arg expected_manifest_path "ci/KERNEL_CONTRACT_OWNERSHIP.jsonl" \
      --arg expected_source_path ".beads/issues.jsonl" \
      --argjson recorded_limits "$recorded_limits" \
      --argjson recorded_usage "$recorded_usage" \
      --argjson expected_manifest_file_bytes "$expected_manifest_file_bytes" \
      --argjson expected_manifest_line_bytes "$expected_manifest_line_bytes" \
      --argjson expected_manifest_records "$expected_manifest_records" \
      --argjson expected_manifest_id_bytes "$expected_manifest_id_bytes" \
      --argjson expected_manifest_parse_depth "$expected_manifest_parse_depth" \
      --argjson expected_source_file_bytes "$expected_source_file_bytes" \
      --argjson expected_source_line_bytes "$expected_source_line_bytes" \
      --argjson expected_source_records "$expected_source_records" \
      --argjson expected_source_id_bytes "$expected_source_id_bytes" \
      --argjson expected_source_parse_depth "$expected_source_parse_depth" \
      --argjson expected_max_file_bytes "$expected_max_file_bytes" \
      --argjson expected_max_line_bytes "$expected_max_line_bytes" \
      --argjson expected_max_records "$expected_max_records" \
      --argjson expected_max_id_bytes "$expected_max_id_bytes" \
      --argjson expected_max_parse_depth "$expected_max_parse_depth" \
      --argjson expected_max_diagnostic_bytes "$DEFAULT_MAX_DIAGNOSTIC_BYTES" '
        keys == [
          "classification","diagnostic","evidence_grade","limits",
          "manifest_hash","manifest_path","projection_hash","schema",
          "source_path","usage"
        ]
        and .schema == $schema
        and .classification == $expected_class
        and .limits == $recorded_limits
        and .usage == $recorded_usage
        and .limits == {
          max_file_bytes:$expected_max_file_bytes,
          max_line_bytes:$expected_max_line_bytes,
          max_records:$expected_max_records,
          max_id_bytes:$expected_max_id_bytes,
          max_parse_depth:$expected_max_parse_depth,
          max_diagnostic_bytes:$expected_max_diagnostic_bytes
        }
        and .usage == {
          manifest:{
            file_bytes:$expected_manifest_file_bytes,
            line_bytes:$expected_manifest_line_bytes,
            records:$expected_manifest_records,
            id_bytes:$expected_manifest_id_bytes,
            parse_depth:$expected_manifest_parse_depth
          },
          source:{
            file_bytes:$expected_source_file_bytes,
            line_bytes:$expected_source_line_bytes,
            records:$expected_source_records,
            id_bytes:$expected_source_id_bytes,
            parse_depth:$expected_source_parse_depth
          },
          source_state:$expected_source_state,
          required_owners:1
        }
        and (.diagnostic | type == "string")
        and ((.diagnostic | utf8bytelength) <= .limits.max_diagnostic_bytes)
        and .evidence_grade == $expected_grade
        and .manifest_path == $expected_manifest_path
        and .source_path == $expected_source_path
        and (
          if $expected_grade == "none"
          then (
            .manifest_hash == ""
            and .projection_hash == ""
          )
          else (
            .manifest_hash == $expected_manifest_hash
            and .projection_hash == $expected_projection_hash
            and (
              if $expected_grade == "source-bound"
              then .usage.source_state == "present-verified"
              else .usage.source_state == "absent"
              end
            )
          )
          end
        )
      ' "$result_file" >/dev/null || return 1

    if [[ "$expected_grade" == "source-bound" ]]; then
      local source_artifact="$bundle_dir/cases/$scenario/root/.beads/issues.jsonl"
      [[ "$authoritative_source_sha" =~ ^[0-9a-f]{64}$ ]] || return 1
      [[ -f "$source_artifact" && ! -L "$source_artifact" ]] || return 1
      [[ "$(sha256_file "$source_artifact")" == "$authoritative_source_sha" ]] \
        || return 1
    fi
    if [[ "$expected_grade" != "none" ]]; then
      local manifest_artifact="$bundle_dir/cases/$scenario/root/ci/KERNEL_CONTRACT_OWNERSHIP.jsonl"
      [[ -f "$manifest_artifact" && ! -L "$manifest_artifact" ]] || return 1
      [[ "$(sha256_file "$manifest_artifact")" == "$authoritative_manifest_sha" ]] \
        || return 1
    fi
  done <<< "$case_rows"

  while IFS= read -r scenario; do
    if scenario_has_source_fixture "$lane" "$scenario"; then
      local retained_source="$bundle_dir/cases/$scenario/root/.beads/issues.jsonl"
      [[ -f "$retained_source" && ! -L "$retained_source" ]] || return 1
      if [[ "$scenario" != "resource_depth_one_over" ]]; then
        [[ "$authoritative_source_sha" =~ ^[0-9a-f]{64}$ ]] || return 1
        [[ "$(sha256_file "$retained_source")" == "$authoritative_source_sha" ]] \
          || return 1
      fi
    fi
    if scenario_has_canonical_manifest "$scenario"; then
      local retained_manifest="$bundle_dir/cases/$scenario/root/ci/KERNEL_CONTRACT_OWNERSHIP.jsonl"
      [[ -f "$retained_manifest" && ! -L "$retained_manifest" ]] || return 1
      [[ "$(sha256_file "$retained_manifest")" == "$authoritative_manifest_sha" ]] \
        || return 1
    fi
  done < <(ownership_scenarios)

  evidence_rows="$(
    jq -r '[.evidence.path,.evidence.sha256] | @tsv' "$log_path"
  )" || return 1
  while IFS=$'\t' read -r rel state; do
    [[ "$rel" != /* && "$rel" != *".."* ]] || return 1
    local evidence="$bundle_dir/$rel"
    case "$state" in
      missing)
        [[ ! -e "$evidence" && ! -L "$evidence" ]] || return 1
        ;;
      nonregular)
        [[ -d "$evidence" && ! -L "$evidence" ]] || return 1
        ;;
      *)
        [[ "$state" =~ ^[0-9a-f]{64}$ ]] || return 1
        [[ -f "$evidence" && ! -L "$evidence" ]] || return 1
        [[ "$(sha256_file "$evidence")" == "$state" ]] || return 1
        ;;
    esac
  done <<< "$evidence_rows"
}

validate_retained_manifest_semantics() {
  local bundle_dir="$1"
  local lane="$2"
  local expected_manifest_hash="$3"
  local expected_projection_hash="$4"
  local positive_result="$bundle_dir/cases/positive/result.json"
  local positive_root="$bundle_dir/cases/positive/root"
  local limits_tsv
  local max_file
  local max_line
  local max_records
  local max_id
  local max_depth
  local max_diagnostic
  local expected_owner_records
  local expected_source_state
  local probe_output
  local probe_rows
  local probe_json

  [[ -f "$positive_result" && ! -L "$positive_result" ]] || return 1
  limits_tsv="$(
    jq -er '
      [
        .limits.max_file_bytes,
        .limits.max_line_bytes,
        .limits.max_records,
        .limits.max_id_bytes,
        .limits.max_parse_depth,
        .limits.max_diagnostic_bytes,
        .usage.manifest.records
      ] | map(tostring) | @tsv
    ' "$positive_result"
  )" || return 1
  IFS=$'\t' read -r \
    max_file max_line max_records max_id max_depth max_diagnostic \
    expected_owner_records <<< "$limits_tsv" || return 1
  if [[ "$lane" == "rch" ]]; then
    expected_source_state="absent"
  else
    expected_source_state="present-verified"
  fi

  probe_output="$(
    cd "$ROOT"
    env \
      "FLN_OWNERSHIP_E2E_ROOT=$positive_root" \
      "FLN_OWNERSHIP_E2E_REQUIRED_OWNER=franken_lean-79k.1" \
      "FLN_OWNERSHIP_E2E_POLICY=manifest-only" \
      "FLN_OWNERSHIP_EXPECTED_MANIFEST_HASH=$expected_manifest_hash" \
      "FLN_OWNERSHIP_EXPECTED_PROJECTION_HASH=$expected_projection_hash" \
      "FLN_OWNERSHIP_MAX_FILE_BYTES=$max_file" \
      "FLN_OWNERSHIP_MAX_LINE_BYTES=$max_line" \
      "FLN_OWNERSHIP_MAX_RECORDS=$max_records" \
      "FLN_OWNERSHIP_MAX_ID_BYTES=$max_id" \
      "FLN_OWNERSHIP_MAX_PARSE_DEPTH=$max_depth" \
      "FLN_OWNERSHIP_MAX_DIAGNOSTIC_BYTES=$max_diagnostic" \
      cargo test --locked -q -p fln-conformance --test kernel_contract \
        ownership_evidence_semantic_probe -- --exact --nocapture
  )" || return 1
  probe_rows="$(
    printf '%s\n' "$probe_output" \
      | sed -n 's/^.*FLN_OWNERSHIP_PROBE //p'
  )" || return 1
  [[ -n "$probe_rows" ]] || return 1
  [[ "$(printf '%s\n' "$probe_rows" | wc -l | tr -d ' ')" == "1" ]] \
    || return 1
  probe_json="$probe_rows"
  jq -e \
    --arg expected_manifest_hash "$expected_manifest_hash" \
    --arg expected_projection_hash "$expected_projection_hash" \
    --arg expected_source_state "$expected_source_state" \
    --argjson expected_owner_records "$expected_owner_records" '
      keys == [
        "manifest_hash","projection_hash","record_count","schema","source_state"
      ]
      and .schema == "fln.kernel-contract-ownership-probe/1"
      and .manifest_hash == $expected_manifest_hash
      and .projection_hash == $expected_projection_hash
      and .record_count == $expected_owner_records
      and .source_state == $expected_source_state
    ' <<< "$probe_json" >/dev/null
}

validate_existing_bundle() {
  local requested_dir="$1"
  local validation_mode="${2:-complete}"
  local externally_expected_commit="${3:-}"
  local externally_expected_tree="${4:-}"
  case "$validation_mode" in
    complete|components) ;;
    *) return 1 ;;
  esac
  [[ -d "$requested_dir" && ! -L "$requested_dir" ]] \
    || { echo "bundle is missing, non-directory, or a symlink" >&2; return 1; }
  local bundle_dir
  bundle_dir="$(cd "$requested_dir" && pwd -P)"
  local bundle="$bundle_dir/bundle.complete.json"
  local manifest="$bundle_dir/artifact-manifest.ndjson"
  local run_log="$bundle_dir/run.ndjson"
  local validation="$bundle_dir/validation.json"

  local symlink_probe
  local special_probe
  symlink_probe="$(find "$bundle_dir" -type l -print -quit)" || return 1
  special_probe="$(find "$bundle_dir" ! -type d ! -type f -print -quit)" || return 1
  [[ -z "$symlink_probe" ]] \
    || { echo "bundle contains a symlink" >&2; return 1; }
  [[ -z "$special_probe" ]] \
    || { echo "bundle contains an unmanifested special file" >&2; return 1; }
  local required_files=("$manifest" "$run_log" "$validation")
  if [[ "$validation_mode" == "complete" ]]; then
    required_files+=("$bundle")
  else
    [[ ! -e "$bundle" && ! -L "$bundle" ]] || return 1
  fi
  for required in "${required_files[@]}"; do
    [[ -f "$required" && ! -L "$required" ]] \
      || { echo "bundle required file is missing: $required" >&2; return 1; }
  done

  local run_id
  local expected_files
  if [[ "$validation_mode" == "complete" ]]; then
    jq -e '
      keys == [
        "artifact_manifest","artifact_manifest_sha256","cleanup_result",
        "files","run_id","run_sha256","schema","validation_sha256","verdict"
      ]
      and .schema == "fln.evidence-bundle.kernel-contract-ownership/1"
      and .artifact_manifest == "artifact-manifest.ndjson"
      and .verdict == "pass"
      and .cleanup_result == "retained_by_policy"
      and (.files | type == "number" and . >= 0 and floor == .)
      and (.run_id | type == "string" and length > 0)
      and (.artifact_manifest_sha256 | test("^[0-9a-f]{64}$"))
      and (.run_sha256 | test("^[0-9a-f]{64}$"))
      and (.validation_sha256 | test("^[0-9a-f]{64}$"))
    ' "$bundle" >/dev/null || return 1
    run_id="$(jq -r '.run_id' "$bundle")" || return 1
    expected_files="$(jq -r '.files' "$bundle")" || return 1
    [[ "$(jq -r '.artifact_manifest_sha256' "$bundle")" \
        == "$(sha256_file "$manifest")" ]] || return 1
    [[ "$(jq -r '.run_sha256' "$bundle")" == "$(sha256_file "$run_log")" ]] \
      || return 1
    [[ "$(jq -r '.validation_sha256' "$bundle")" \
        == "$(sha256_file "$validation")" ]] || return 1
  else
    run_id="$(jq -er '.run_id' "$validation")" || return 1
    expected_files="$(wc -l < "$manifest" | tr -d ' ')" || return 1
  fi

  jq -s -e --argjson expected_files "$expected_files" '
    length == $expected_files
    and all(.[];
      .schema == "fln.evidence-manifest.kernel-contract-ownership/1"
      and (keys == ["bytes","path","schema","sha256"])
      and (.path | type == "string" and length > 0)
      and (.sha256 | test("^[0-9a-f]{64}$"))
      and (.bytes | type == "number" and . >= 0 and floor == .)
    )
  ' "$manifest" >/dev/null || return 1

  local lane
  local commit
  local tree
  local expected_manifest_hash
  local expected_projection_hash
  lane="$(
    jq -sr '
      if length > 0 and ([.[].lane] | unique | length) == 1
      then .[0].lane else empty end
    ' "$run_log"
  )" || return 1
  commit="$(
    jq -sr '
      if length > 0 and ([.[].build.commit] | unique | length) == 1
      then .[0].build.commit else empty end
    ' "$run_log"
  )" || return 1
  tree="$(
    jq -sr '
      if length > 0 and ([.[].build.tree] | unique | length) == 1
      then .[0].build.tree else empty end
    ' "$run_log"
  )" || return 1
  if [[ "$lane" == "rch" ]]; then
    [[ "$externally_expected_commit" =~ ^[0-9a-f]{40}$ \
        && "$externally_expected_tree" =~ ^[0-9a-f]{40}$ \
        && "$commit" == "$externally_expected_commit" \
        && "$tree" == "$externally_expected_tree" ]] \
      || {
        echo "rch bundle lacks matching external commit/tree expectations" >&2
        return 1
      }
  elif [[ -n "$externally_expected_commit" \
          || -n "$externally_expected_tree" ]]; then
    [[ "$commit" == "$externally_expected_commit" \
        && "$tree" == "$externally_expected_tree" ]] \
      || return 1
  fi
  expected_manifest_hash="$(
    jq -sr '
      [.[] | select(.scenario == "positive")]
      | if length == 1 then .[0].evidence.manifest_hash else empty end
    ' "$run_log"
  )" || return 1
  expected_projection_hash="$(
    jq -sr '
      [.[] | select(.scenario == "positive")]
      | if length == 1 then .[0].evidence.projection_hash else empty end
    ' "$run_log"
  )" || return 1

  local listed_paths
  local actual_paths
  local expected_paths
  local manifest_rows
  local actual_directories
  local expected_directories
  listed_paths="$(jq -r '.path' "$manifest")" || return 1
  actual_paths="$(
    find "$bundle_dir" -type f \
      ! -path "$manifest" \
      ! -path "$bundle" \
      -printf '%P\n' | LC_ALL=C sort
  )" || return 1
  expected_paths="$(
    expected_artifact_paths "$lane" | LC_ALL=C sort
  )" || return 1
  actual_directories="$(
    find "$bundle_dir" -mindepth 1 -type d -printf '%P\n' | LC_ALL=C sort
  )" || return 1
  expected_directories="$(
    expected_directory_paths "$lane" | LC_ALL=C sort -u
  )" || return 1
  [[ "$listed_paths" == "$expected_paths" ]] || return 1
  [[ "$actual_paths" == "$expected_paths" ]] || return 1
  [[ "$actual_directories" == "$expected_directories" ]] || return 1

  manifest_rows="$(
    jq -r '[.path,.sha256,(.bytes|tostring)] | @tsv' "$manifest"
  )" || return 1
  while IFS=$'\t' read -r rel expected_sha expected_bytes; do
    [[ "$rel" != /* && "$rel" != *".."* ]] || return 1
    local artifact="$bundle_dir/$rel"
    [[ -f "$artifact" && ! -L "$artifact" ]] || return 1
    [[ "$(sha256_file "$artifact")" == "$expected_sha" ]] || return 1
    [[ "$(bytes_file "$artifact")" == "$expected_bytes" ]] || return 1
  done <<< "$manifest_rows"

  local expected_records
  expected_records="$(jq -r '.records' "$validation")" || return 1
  local authoritative_manifest_artifact
  local authoritative_manifest_sha
  local authoritative_source_sha
  authoritative_manifest_artifact="$bundle_dir/cases/positive/root/ci/KERNEL_CONTRACT_OWNERSHIP.jsonl"
  [[ -f "$authoritative_manifest_artifact" \
      && ! -L "$authoritative_manifest_artifact" ]] || return 1
  authoritative_manifest_sha="$(sha256_file "$authoritative_manifest_artifact")"
  local header_projection_hash
  header_projection_hash="$(
    sed -n \
      '1s/.*"projection_hash":"\([0-9a-f]\{64\}\)"}$/\1/p' \
      "$authoritative_manifest_artifact"
  )" || return 1
  [[ "$header_projection_hash" == "$expected_projection_hash" ]] || return 1
  authoritative_source_sha="$(
    jq -er '.authoritative_source_sha256.before' "$validation"
  )" || return 1
  jq -e \
    --arg run_id "$run_id" \
    --arg run_sha "$(sha256_file "$run_log")" \
    --arg lane "$lane" \
    --arg authoritative_manifest_sha "$authoritative_manifest_sha" \
    --argjson expected_records "$expected_records" '
      .schema == "fln.validation.kernel-contract-ownership/1"
      and (keys == [
        "authoritative_manifest_sha256","authoritative_source_sha256",
        "cleanup_result","failures","records","run_id","run_sha256",
        "schema","verdict"
      ])
      and .run_id == $run_id
      and .verdict == "pass"
      and .failures == 0
      and .records == 26
      and .records == $expected_records
      and .run_sha256 == $run_sha
      and (.authoritative_manifest_sha256
        | keys == ["after","before"])
      and (.authoritative_source_sha256
        | keys == ["after","before"])
      and .authoritative_manifest_sha256.before
        == .authoritative_manifest_sha256.after
      and .authoritative_manifest_sha256.before
        == $authoritative_manifest_sha
      and .authoritative_source_sha256.before
        == .authoritative_source_sha256.after
      and (
        .authoritative_source_sha256.before == "missing"
        or (.authoritative_source_sha256.before
          | test("^[0-9a-f]{64}$"))
      )
      and (
        $lane == "rch"
        or (.authoritative_source_sha256.before
          | test("^[0-9a-f]{64}$"))
      )
      and .cleanup_result == "retained_by_policy"
    ' "$validation" >/dev/null || return 1

  [[ "$expected_records" == "26" ]] || return 1
  strict_validate_run_ndjson \
    "$run_log" \
    "$expected_records" \
    "fln.e2e.kernel-contract-ownership/1" \
    "$run_id" \
    "franken_lean-79k.1" \
    "$lane" \
    "$commit" \
    "$tree" \
    "$expected_manifest_hash" \
    "$expected_projection_hash" || return 1
  strict_validate_artifact_links \
    "$bundle_dir" \
    "$run_log" \
    "$lane" \
    "fln.kernel-contract-ownership-result/1" \
    "$expected_manifest_hash" \
    "$expected_projection_hash" \
    "$authoritative_manifest_sha" \
    "$authoritative_source_sha" || return 1
  if [[ "$validation_mode" == "complete" ]]; then
    validate_retained_manifest_semantics \
      "$bundle_dir" \
      "$lane" \
      "$expected_manifest_hash" \
      "$expected_projection_hash" || return 1
  fi

  local mutant
  while IFS= read -r mutant; do
    if strict_validate_run_ndjson \
        "$bundle_dir/selftest-$mutant.ndjson" \
        "$expected_records" \
        "fln.e2e.kernel-contract-ownership/1" \
        "$run_id" \
        "franken_lean-79k.1" \
        "$lane" \
        "$commit" \
        "$tree" \
        "$expected_manifest_hash" \
        "$expected_projection_hash" >/dev/null 2>&1; then
      return 1
    fi
  done < <(validator_selftest_mutants)
}

# RCH intentionally admits compilation commands only. Its strict-remote lane uses
# this script as Cargo's runner for one already-built integration-test binary; the
# runner argument is checked, then discarded, and the real matrix invokes the
# named process-driver test itself. Unsetting the runner prevents recursive Cargo
# invocations from re-entering this bridge.
if [[ "${1:-}" == "--cargo-runner-rch" ]]; then
  runner_binary="${2:-}"
  runner_name="${runner_binary##*/}"
  runner_dir=""
  runner_target_dir=""
  if [[ -n "$runner_binary" && -f "$runner_binary" \
        && ! -L "$runner_binary" && -x "$runner_binary" ]]; then
    runner_dir="$(cd "$(dirname "$runner_binary")" && pwd -P)"
  fi
  if [[ -n "${CARGO_TARGET_DIR:-}" ]]; then
    case "$CARGO_TARGET_DIR" in
      /*) runner_target_path="$CARGO_TARGET_DIR" ;;
      *) runner_target_path="$ROOT/$CARGO_TARGET_DIR" ;;
    esac
    if [[ -d "$runner_target_path" && ! -L "$runner_target_path" ]]; then
      runner_target_dir="$(cd "$runner_target_path" && pwd -P)"
    fi
  fi
  [[ "${FLN_OWNERSHIP_RCH_RUNNER:-}" == "1" \
      && $# -eq 4 \
      && "${3:-}" == "ownership_evidence_process_driver" \
      && "${4:-}" == "--exact" \
      && "$runner_name" =~ ^kernel_contract-[0-9a-f]+$ \
      && -n "$runner_target_dir" \
      && "$runner_dir" == "$runner_target_dir/debug/deps" ]] \
    || {
      echo "kernel_contract_ownership: invalid RCH Cargo-runner invocation" >&2
      exit 2
    }

  # Force every nested Cargo probe back onto the actual host target with a
  # direct `env` runner. This target-specific environment override wins over
  # repository, ancestor, and CARGO_HOME runner configuration and prevents the
  # bridge from recursively re-entering itself.
  runner_host="$(rustc -vV | sed -n 's/^host: //p')"
  direct_runner="$(command -v env)"
  [[ "$runner_host" =~ ^[A-Za-z0-9_.-]+$ \
      && -n "$direct_runner" && -x "$direct_runner" ]] \
    || {
      echo "kernel_contract_ownership: cannot establish direct Cargo runner" >&2
      exit 2
    }
  runner_env="CARGO_TARGET_${runner_host^^}_RUNNER"
  runner_env="${runner_env//-/_}"
  export CARGO_BUILD_TARGET="$runner_host"
  export "$runner_env=$direct_runner"
  export RCH_CARGO_WRAPPER_BYPASS=1
  unset CARGO_BUILD_RUNNER
  RCH_BRIDGE_ENTERED=true
  set -- --lane rch
fi

if [[ "${1:-}" == "--validate-bundle" ]]; then
  [[ $# -eq 2 || $# -eq 4 ]] \
    || {
      echo "usage: $0 --validate-bundle DIR [EXPECTED_COMMIT EXPECTED_TREE]" >&2
      exit 2
    }
  if ! validate_existing_bundle \
      "$2" complete "${3:-}" "${4:-}"; then
    echo "kernel_contract_ownership: bundle validation failed" >&2
    exit 1
  fi
  printf 'validated_bundle=%s\n' "$(cd "$2" && pwd -P)"
  exit 0
fi

LANE="local"
while (( $# > 0 )); do
  case "$1" in
    --lane)
      [[ $# -ge 2 ]] || {
        echo "kernel_contract_ownership: --lane requires a value" >&2
        exit 2
      }
      LANE="$2"
      shift 2
      ;;
    *)
      echo "kernel_contract_ownership: unknown argument: $1" >&2
      exit 2
      ;;
  esac
done
case "$LANE" in
  local|clean|rch) ;;
  *)
    echo "kernel_contract_ownership: lane must be local, clean, or rch" >&2
    exit 2
    ;;
esac
if [[ "$LANE" == "rch" && "$RCH_BRIDGE_ENTERED" != "true" ]]; then
  echo "kernel_contract_ownership: rch lane requires the Cargo-runner bridge" >&2
  exit 2
fi

BEAD="franken_lean-79k.1"
SCHEMA="fln.e2e.kernel-contract-ownership/1"
RESULT_SCHEMA="fln.kernel-contract-ownership-result/1"
MANIFEST_REL="ci/KERNEL_CONTRACT_OWNERSHIP.jsonl"
SOURCE_REL=".beads/issues.jsonl"
AUTHORITATIVE_MANIFEST="$ROOT/$MANIFEST_REL"
AUTHORITATIVE_SOURCE="$ROOT/$SOURCE_REL"
if [[ -n "${FLN_E2E_ART_ROOT:-}" ]]; then
  ART_ROOT="$FLN_E2E_ART_ROOT"
elif [[ -n "${CARGO_TARGET_DIR:-}" ]]; then
  ART_ROOT="$CARGO_TARGET_DIR/e2e"
else
  ART_ROOT="$ROOT/target/e2e"
fi
case "$ART_ROOT" in
  /*) ;;
  *) ART_ROOT="$ROOT/$ART_ROOT" ;;
esac
RUN_ID="kernel-contract-ownership-${LANE}-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="$ART_ROOT/$RUN_ID"
CASES_DIR="$ART_DIR/cases"
RUN_LOG="$ART_DIR/run.ndjson"
VALIDATION="$ART_DIR/validation.json"
ARTIFACT_MANIFEST="$ART_DIR/artifact-manifest.ndjson"
BUNDLE="$ART_DIR/bundle.complete.json"
BUNDLE_PENDING="$ART_DIR/bundle.complete.pending.json"
MAX_STREAM_BYTES=262144
MAX_DIAGNOSTIC_BYTES="$DEFAULT_MAX_DIAGNOSTIC_BYTES"

mkdir -p "$ART_ROOT"
mkdir "$ART_DIR"
mkdir "$CASES_DIR"

note() {
  printf '[kernel_contract_ownership] %s\n' "$*" >&2
}

fail() {
  note "FAIL: $*"
  return 1
}

regular_file_hash_or_state() {
  local path="$1"
  if [[ -L "$path" ]]; then
    printf 'symlink\n'
  elif [[ -f "$path" ]]; then
    sha256_file "$path"
  elif [[ -e "$path" ]]; then
    printf 'nonregular\n'
  else
    printf 'missing\n'
  fi
}

BASELINE_MANIFEST_SHA="$(regular_file_hash_or_state "$AUTHORITATIVE_MANIFEST")"
[[ "$BASELINE_MANIFEST_SHA" =~ ^[0-9a-f]{64}$ ]] \
  || { note "tracked ownership manifest is missing or nonregular"; exit 1; }

BASELINE_SOURCE_SHA="$(regular_file_hash_or_state "$AUTHORITATIVE_SOURCE")"
if [[ "$LANE" == "rch" ]]; then
  [[ "$BASELINE_SOURCE_SHA" == "missing" \
      || "$BASELINE_SOURCE_SHA" =~ ^[0-9a-f]{64}$ ]] \
    || { note "remote ownership source is present but nonregular"; exit 1; }
else
  [[ "$BASELINE_SOURCE_SHA" =~ ^[0-9a-f]{64}$ ]] \
    || { note "source-bound lane requires regular $SOURCE_REL"; exit 1; }
fi

BASELINE_PROJECTION_HASH="$(
  sed -n '1s/.*"projection_hash":"\([0-9a-f]\{64\}\)".*/\1/p' \
    "$AUTHORITATIVE_MANIFEST"
)"
[[ ${#BASELINE_PROJECTION_HASH} -eq 64 ]] \
  || { note "manifest projection hash is not canonical"; exit 1; }

EXPECTED_MANIFEST_HASH="${FLN_OWNERSHIP_EXPECTED_MANIFEST_HASH:-}"
EXPECTED_PROJECTION_HASH="${FLN_OWNERSHIP_EXPECTED_PROJECTION_HASH:-}"
if [[ "$LANE" == "rch" ]]; then
  [[ "$EXPECTED_MANIFEST_HASH" =~ ^[0-9a-f]{64}$ \
      && "$EXPECTED_PROJECTION_HASH" =~ ^[0-9a-f]{64}$ ]] \
    || {
      note "rch lane requires source-bound expected manifest and projection hashes"
      exit 2
    }
  [[ "$EXPECTED_PROJECTION_HASH" == "$BASELINE_PROJECTION_HASH" ]] \
    || {
      note "rch expected projection does not match the transferred manifest"
      exit 1
    }
fi

EXPECTED_COMMIT="${FLN_OWNERSHIP_EXPECTED_COMMIT:-}"
if [[ "$LANE" == "rch" ]]; then
  [[ "$EXPECTED_COMMIT" =~ ^[0-9a-f]{40}$ ]] \
    || { note "rch lane requires FLN_OWNERSHIP_EXPECTED_COMMIT"; exit 2; }
  EXPECTED_TREE="${FLN_OWNERSHIP_EXPECTED_TREE:-}"
  [[ "$EXPECTED_TREE" =~ ^[0-9a-f]{40}$ ]] \
    || { note "rch lane requires FLN_OWNERSHIP_EXPECTED_TREE"; exit 2; }
  if OBSERVED_TOPLEVEL="$(
      git -C "$ROOT" rev-parse --show-toplevel 2>/dev/null
    )" \
      && [[ "$(cd "$OBSERVED_TOPLEVEL" && pwd -P)" == "$ROOT" ]] \
      && OBSERVED_COMMIT="$(git -C "$ROOT" rev-parse HEAD 2>/dev/null)"; then
    OBSERVED_TREE="$(git -C "$ROOT" rev-parse 'HEAD^{tree}')" \
      || { note "rch lane could not resolve the worker tree"; exit 1; }
    [[ "$OBSERVED_COMMIT" == "$EXPECTED_COMMIT" \
        && "$OBSERVED_TREE" == "$EXPECTED_TREE" ]] \
      || {
        note "rch worker commit/tree does not match the source-bound expectation"
        exit 1
      }
    git -C "$ROOT" diff --quiet "$EXPECTED_COMMIT" -- \
      . ':(exclude).beads/issues.jsonl' \
      || { note "rch worker has tracked source drift"; exit 1; }
    git -C "$ROOT" diff --cached --quiet "$EXPECTED_COMMIT" -- \
      . ':(exclude).beads/issues.jsonl' \
      || { note "rch worker has staged source drift"; exit 1; }
    REMOTE_UNTRACKED="$(
      git -C "$ROOT" ls-files --others --exclude-standard
    )" || { note "rch lane could not inspect untracked worker inputs"; exit 1; }
    [[ -z "$REMOTE_UNTRACKED" ]] \
      || { note "rch worker has untracked source drift"; exit 1; }
    COMMIT="$OBSERVED_COMMIT"
    TREE="$OBSERVED_TREE"
  else
    [[ "${FLN_OWNERSHIP_RCH_ARCHIVE_BASE_ONLY:-}" == "1" \
        && ! -e "$ROOT/.git" && ! -L "$ROOT/.git" ]] \
      || {
        note "rch worker lacks verifiable Git or clean base-only archive identity"
        exit 1
      }
    ART_ROOT_PHYSICAL="$(cd "$ART_ROOT" && pwd -P)" \
      || { note "rch lane could not resolve its retained artifact root"; exit 1; }
    case "$ART_ROOT_PHYSICAL/" in
      "$ROOT"/*)
        note "rch archive identity store must be outside the extracted source root"
        exit 1
        ;;
    esac
    ARCHIVE_IDENTITY_GIT_DIR="$ART_ROOT/archive-source-tree-$RUN_ID.git"
    [[ ! -e "$ARCHIVE_IDENTITY_GIT_DIR" \
        && ! -L "$ARCHIVE_IDENTITY_GIT_DIR" ]] \
      || {
        note "rch archive identity store already exists"
        exit 1
      }
    git init --bare -q "$ARCHIVE_IDENTITY_GIT_DIR" \
      || { note "rch lane could not initialize its retained identity store"; exit 1; }
    GIT_DIR="$ARCHIVE_IDENTITY_GIT_DIR" \
      GIT_WORK_TREE="$ROOT" \
      git -C "$ROOT" -c core.autocrlf=false -c core.filemode=true \
        add -f -A -- . \
        ':(top,exclude,glob).rch-*' \
        ':(top,exclude,glob).rch-*/**' \
      || { note "rch lane could not index the extracted source tree"; exit 1; }
    RAW_PATHS="$ARCHIVE_IDENTITY_GIT_DIR/raw-regular-paths.txt"
    RAW_EXPECTED="$ARCHIVE_IDENTITY_GIT_DIR/raw-expected-hashes.txt"
    RAW_OBSERVED="$ARCHIVE_IDENTITY_GIT_DIR/raw-observed-hashes.txt"
    : > "$RAW_PATHS"
    : > "$RAW_EXPECTED"
    while IFS= read -r -d '' index_entry; do
      [[ "$index_entry" == *$'\t'* ]] \
        || { note "rch source index contains a malformed entry"; exit 1; }
      index_metadata="${index_entry%%$'\t'*}"
      indexed_path="${index_entry#*$'\t'}"
      [[ "$indexed_path" != *$'\n'* && "$indexed_path" != *$'\r'* ]] \
        || { note "rch source index contains an unsupported path"; exit 1; }
      read -r indexed_mode indexed_hash indexed_stage indexed_extra \
        <<< "$index_metadata"
      [[ "$indexed_mode" =~ ^(100644|100755|120000)$ \
          && "$indexed_hash" =~ ^[0-9a-f]{40}$ \
          && "$indexed_stage" == "0" \
          && -z "$indexed_extra" ]] \
        || { note "rch source index contains unsupported metadata"; exit 1; }
      case "$indexed_mode" in
        100644|100755)
          [[ -f "$ROOT/$indexed_path" && ! -L "$ROOT/$indexed_path" ]] \
            || { note "rch indexed regular file changed type"; exit 1; }
          printf '%s\n' "$indexed_path" >> "$RAW_PATHS"
          printf '%s\n' "$indexed_hash" >> "$RAW_EXPECTED"
          ;;
        120000)
          [[ -L "$ROOT/$indexed_path" ]] \
            || { note "rch indexed symlink changed type"; exit 1; }
          indexed_link=""
          IFS= read -r -d '' indexed_link \
            < <(readlink -z -- "$ROOT/$indexed_path") \
            || { note "rch lane could not read an indexed symlink"; exit 1; }
          [[ "$indexed_link" != *$'\n'* && "$indexed_link" != *$'\r'* ]] \
            || { note "rch source index contains an unsupported symlink"; exit 1; }
          observed_link_hash="$(
            printf '%s' "$indexed_link" | git hash-object --no-filters --stdin
          )" || { note "rch lane could not hash an indexed symlink"; exit 1; }
          [[ "$observed_link_hash" == "$indexed_hash" ]] \
            || { note "rch indexed symlink bytes do not match"; exit 1; }
          ;;
      esac
    done < <(
      GIT_DIR="$ARCHIVE_IDENTITY_GIT_DIR" \
        GIT_WORK_TREE="$ROOT" \
        git -C "$ROOT" ls-files -s -z
    )
    (
      cd "$ROOT"
      git hash-object --no-filters --stdin-paths \
        < "$RAW_PATHS" > "$RAW_OBSERVED"
    ) || { note "rch lane could not hash raw extracted source bytes"; exit 1; }
    cmp -s "$RAW_EXPECTED" "$RAW_OBSERVED" \
      || {
        note "rch extracted source bytes differ after Git attribute conversion"
        exit 1
      }
    OBSERVED_TREE="$(
      GIT_DIR="$ARCHIVE_IDENTITY_GIT_DIR" \
        GIT_WORK_TREE="$ROOT" \
        git -C "$ROOT" write-tree
    )" || { note "rch lane could not hash the extracted source tree"; exit 1; }
    [[ "$OBSERVED_TREE" == "$EXPECTED_TREE" ]] \
      || {
        note "rch extracted source tree does not match expectation"
        exit 1
      }
    # The retained bare object store is an independently inspectable snapshot
    # of the exact extracted archive bytes and modes; the caller-bound commit is
    # separately corroborated by the RCH daemon's clean-overlay receipt.
    COMMIT="$EXPECTED_COMMIT"
    TREE="$OBSERVED_TREE"
    note "retained archive identity store: $ARCHIVE_IDENTITY_GIT_DIR"
  fi
else
  COMMIT="$(git -C "$ROOT" rev-parse HEAD)"
  TREE="$(git -C "$ROOT" rev-parse 'HEAD^{tree}')"
fi
if [[ "$LANE" == "clean" ]]; then
  [[ "$EXPECTED_COMMIT" =~ ^[0-9a-f]{40}$ && "$COMMIT" == "$EXPECTED_COMMIT" ]] \
    || { note "clean lane is not bound to its expected commit"; exit 1; }
  CLEAN_RELEVANT_STATUS="$(git -C "$ROOT" status --porcelain)"
  [[ -z "$CLEAN_RELEVANT_STATUS" ]] \
    || { note "clean lane has working-tree drift"; exit 1; }
fi
RUSTC_COMMIT="$(rustc -vV | sed -n 's/^commit-hash: //p')"
TARGET_TRIPLE="$(rustc -vV | sed -n 's/^host: //p')"
WORKER_ID="${RCH_WORKER_ID:-$(hostname)}"
REMOTE_REQUIRED=false
if [[ "$LANE" == "rch" ]]; then
  REMOTE_REQUIRED=true
  ORCHESTRATOR_HOST="${FLN_OWNERSHIP_ORCHESTRATOR_HOST:-}"
  [[ -n "$ORCHESTRATOR_HOST" && "$WORKER_ID" != "$ORCHESTRATOR_HOST" ]] \
    || {
      note "rch lane did not prove execution on a distinct remote host"
      exit 1
    }
fi

make_root() {
  local scenario="$1"
  local fixture_root="$CASES_DIR/$scenario/root"
  mkdir "$CASES_DIR/$scenario"
  mkdir "$fixture_root"
  printf '%s\n' "$fixture_root"
}

make_ci_dir() {
  mkdir "$1/ci"
}

copy_manifest() {
  make_ci_dir "$1"
  cp "$AUTHORITATIVE_MANIFEST" "$1/$MANIFEST_REL"
}

copy_source() {
  local fixture_root="$1"
  mkdir "$fixture_root/.beads"
  cp "$AUTHORITATIVE_SOURCE" "$fixture_root/$SOURCE_REL"
}

copy_source_for_source_lane() {
  [[ "$LANE" == "rch" ]] || copy_source "$1"
}

write_case_record() {
  local scenario="$1"
  local fixture_root="$2"
  local expected_class="$3"
  local expected_exit="$4"
  local actual_class="$5"
  local actual_exit="$6"
  local status="$7"
  local result_json="$8"
  local stdout_rel="cases/$scenario/stdout.log"
  local stderr_rel="cases/$scenario/stderr.log"
  local result_rel="cases/$scenario/result.json"
  local stdout_path="$ART_DIR/$stdout_rel"
  local stderr_path="$ART_DIR/$stderr_rel"
  local result_path="$ART_DIR/$result_rel"
  [[ "$fixture_root" == "$CASES_DIR/$scenario/root" ]] \
    || { note "scenario root escaped its immutable case directory"; return 1; }
  local evidence_rel="cases/$scenario/root/$MANIFEST_REL"
  local evidence_path="$ART_DIR/$evidence_rel"
  local evidence_sha
  local result_sha
  local result_bytes
  evidence_sha="$(regular_file_hash_or_state "$evidence_path")"
  result_sha="$(regular_file_hash_or_state "$result_path")"
  result_bytes=0
  if [[ -f "$result_path" && ! -L "$result_path" ]]; then
    result_bytes="$(bytes_file "$result_path")"
  fi

  jq -cn \
    --arg schema "$SCHEMA" \
    --arg run_id "$RUN_ID" \
    --arg bead "$BEAD" \
    --arg scenario "$scenario" \
    --arg lane "$LANE" \
    --arg status "$status" \
    --arg evidence_path "$evidence_rel" \
    --arg evidence_sha "$evidence_sha" \
    --arg expected_class "$expected_class" \
    --arg expected_exit "$expected_exit" \
    --arg actual_class "$actual_class" \
    --argjson actual_exit "$actual_exit" \
    --arg commit "$COMMIT" \
    --arg tree "$TREE" \
    --arg rustc_commit "$RUSTC_COMMIT" \
    --arg target "$TARGET_TRIPLE" \
    --arg worker "$WORKER_ID" \
    --argjson remote_required "$REMOTE_REQUIRED" \
    --arg stdout_path "$stdout_rel" \
    --arg stdout_sha "$(sha256_file "$stdout_path")" \
    --argjson stdout_bytes "$(bytes_file "$stdout_path")" \
    --arg stderr_path "$stderr_rel" \
    --arg stderr_sha "$(sha256_file "$stderr_path")" \
    --argjson stderr_bytes "$(bytes_file "$stderr_path")" \
    --arg result_path "$result_rel" \
    --arg result_sha "$result_sha" \
    --argjson result_bytes "$result_bytes" \
    --argjson result "$result_json" \
    '{
      schema:$schema,
      run_id:$run_id,
      bead:$bead,
      scenario:$scenario,
      lane:$lane,
      status:$status,
      evidence:{
        path:$evidence_path,
        sha256:$evidence_sha,
        provenance_source:".beads/issues.jsonl",
        grade:($result.evidence_grade // "none"),
        projection_hash:($result.projection_hash // ""),
        manifest_hash:($result.manifest_hash // "")
      },
      limits_configured:($result.limits // {
        max_file_bytes:0,
        max_line_bytes:0,
        max_records:0,
        max_id_bytes:0,
        max_parse_depth:0,
        max_diagnostic_bytes:0
      }),
      limits_consumed:($result.usage // {
        manifest:{
          file_bytes:0,
          line_bytes:0,
          records:0,
          id_bytes:0,
          parse_depth:0
        },
        source:{
          file_bytes:0,
          line_bytes:0,
          records:0,
          id_bytes:0,
          parse_depth:0
        },
        source_state:"not-attempted",
        required_owners:0
      }),
      command:[
        "cargo","test","--locked","-q","-p","fln-conformance",
        "--test","kernel_contract","ownership_evidence_process_driver",
        "--","--exact","--nocapture"
      ],
      build:{
        commit:$commit,
        rustc_commit:$rustc_commit,
        target:$target,
        tree:$tree
      },
      worker:{identity:$worker,remote_required:$remote_required},
      expected:{classification:$expected_class,exit:$expected_exit},
      actual:{classification:$actual_class,exit_code:$actual_exit},
      stdout:{path:$stdout_path,sha256:$stdout_sha,bytes:$stdout_bytes},
      stderr:{path:$stderr_path,sha256:$stderr_sha,bytes:$stderr_bytes},
      result:{path:$result_path,sha256:$result_sha,bytes:$result_bytes},
      cleanup_result:"retained_by_policy",
      final_recovery_state:"authoritative_inputs_unchanged"
    }' >> "$RUN_LOG"
}

FAILURES=0

run_case() {
  local scenario="$1"
  local fixture_root="$2"
  local required_owner="$3"
  local expected_class="$4"
  local expected_exit="$5"
  local policy="$6"
  local max_file="${7:-$DEFAULT_MAX_FILE_BYTES}"
  local max_line="${8:-$DEFAULT_MAX_LINE_BYTES}"
  local max_records="${9:-$DEFAULT_MAX_RECORDS}"
  local max_id="${10:-$DEFAULT_MAX_ID_BYTES}"
  local max_depth="${11:-$DEFAULT_MAX_PARSE_DEPTH}"
  local case_dir="$CASES_DIR/$scenario"
  local stdout_path="$case_dir/stdout.log"
  local stderr_path="$case_dir/stderr.log"
  local result_path="$case_dir/result.json"
  local env_args=(
    "FLN_OWNERSHIP_E2E_ROOT=$fixture_root"
    "FLN_OWNERSHIP_E2E_REQUIRED_OWNER=$required_owner"
    "FLN_OWNERSHIP_E2E_RESULT=$result_path"
    "FLN_OWNERSHIP_E2E_POLICY=$policy"
    "FLN_OWNERSHIP_MAX_FILE_BYTES=$max_file"
    "FLN_OWNERSHIP_MAX_LINE_BYTES=$max_line"
    "FLN_OWNERSHIP_MAX_RECORDS=$max_records"
    "FLN_OWNERSHIP_MAX_ID_BYTES=$max_id"
    "FLN_OWNERSHIP_MAX_PARSE_DEPTH=$max_depth"
    "FLN_OWNERSHIP_MAX_DIAGNOSTIC_BYTES=$MAX_DIAGNOSTIC_BYTES"
  )

  if [[ "$policy" == "manifest-only" ]]; then
    env_args+=(
      "FLN_OWNERSHIP_EXPECTED_MANIFEST_HASH=$EXPECTED_MANIFEST_HASH"
      "FLN_OWNERSHIP_EXPECTED_PROJECTION_HASH=$EXPECTED_PROJECTION_HASH"
    )
  fi

  note "$scenario: expected $expected_class/$expected_exit"
  set +e
  (
    cd "$ROOT"
    env "${env_args[@]}" \
      cargo test --locked -q -p fln-conformance --test kernel_contract \
        ownership_evidence_process_driver -- --exact --nocapture
  ) > "$stdout_path" 2> "$stderr_path"
  local command_rc=$?
  set -e

  local result_json
  local actual_class="harness-failure"
  if [[ -f "$result_path" && ! -L "$result_path" ]] \
    && result_json="$(jq -ce --arg schema "$RESULT_SCHEMA" \
      'select(.schema == $schema)' "$result_path" 2>/dev/null)"; then
    actual_class="$(jq -r '.classification' <<<"$result_json")"
  else
    result_json='{}'
  fi

  local streams_bounded=true
  if (( $(bytes_file "$stdout_path") > MAX_STREAM_BYTES )); then
    streams_bounded=false
  fi
  if (( $(bytes_file "$stderr_path") > MAX_STREAM_BYTES )); then
    streams_bounded=false
  fi

  local exit_matches=false
  if [[ "$expected_exit" == "zero" && "$command_rc" -eq 0 ]]; then
    exit_matches=true
  elif [[ "$expected_exit" == "nonzero" && "$command_rc" -ne 0 ]]; then
    exit_matches=true
  fi

  local status="failed"
  if [[ "$actual_class" == "$expected_class" \
        && "$exit_matches" == true \
        && "$streams_bounded" == true ]]; then
    status="passed"
  else
    FAILURES=$((FAILURES + 1))
  fi

  write_case_record "$scenario" "$fixture_root" "$expected_class" \
    "$expected_exit" "$actual_class" "$command_rc" "$status" "$result_json"
}

# Canonical positive.
positive_root="$(make_root positive)"
copy_manifest "$positive_root"
positive_policy="require-source"
if [[ "$LANE" == "rch" ]]; then
  positive_policy="manifest-only"
else
  copy_source "$positive_root"
fi
run_case positive "$positive_root" "franken_lean-79k.1" ok zero "$positive_policy"

positive_result="$CASES_DIR/positive/result.json"
[[ -f "$positive_result" && ! -L "$positive_result" ]] \
  || { note "positive preflight did not publish its binding result"; exit 1; }
observed_manifest_hash="$(jq -er '.manifest_hash' "$positive_result")"
observed_projection_hash="$(jq -er '.projection_hash' "$positive_result")"
[[ "$observed_manifest_hash" =~ ^[0-9a-f]{64}$ \
    && "$observed_projection_hash" =~ ^[0-9a-f]{64}$ ]] \
  || { note "positive preflight published a noncanonical binding"; exit 1; }
[[ "$observed_projection_hash" == "$BASELINE_PROJECTION_HASH" ]] \
  || { note "positive preflight projection disagrees with the manifest"; exit 1; }
if [[ "$LANE" == "rch" ]]; then
  [[ "$observed_manifest_hash" == "$EXPECTED_MANIFEST_HASH" \
      && "$observed_projection_hash" == "$EXPECTED_PROJECTION_HASH" ]] \
    || { note "remote positive binding disagrees with source-bound expectations"; exit 1; }
else
  EXPECTED_MANIFEST_HASH="$observed_manifest_hash"
  EXPECTED_PROJECTION_HASH="$observed_projection_hash"
fi

# Missing manifest.
missing_root="$(make_root missing)"
if [[ "$LANE" != "rch" ]]; then
  copy_source "$missing_root"
fi
run_case missing "$missing_root" "franken_lean-79k.1" missing nonzero require-source

# Present manifest but missing source under the strict source-required policy.
missing_source_root="$(make_root missing_source)"
copy_manifest "$missing_source_root"
run_case missing_source "$missing_source_root" "franken_lean-79k.1" \
  missing nonzero require-source

# Deterministically unreadable/nonregular manifest (works even as root).
unreadable_root="$(make_root unreadable)"
make_ci_dir "$unreadable_root"
mkdir "$unreadable_root/$MANIFEST_REL"
printf 'nonregular evidence fixture retained\n' \
  > "$unreadable_root/$MANIFEST_REL/.retained-directory-fixture"
copy_source_for_source_lane "$unreadable_root"
run_case unreadable "$unreadable_root" "franken_lean-79k.1" \
  unreadable nonzero require-source

malformed_root="$(make_root malformed)"
make_ci_dir "$malformed_root"
printf '{"schema": definitely-not-json}\n' > "$malformed_root/$MANIFEST_REL"
copy_source_for_source_lane "$malformed_root"
run_case malformed "$malformed_root" "franken_lean-79k.1" \
  malformed nonzero require-source

empty_root="$(make_root empty)"
make_ci_dir "$empty_root"
: > "$empty_root/$MANIFEST_REL"
copy_source_for_source_lane "$empty_root"
run_case empty "$empty_root" "franken_lean-79k.1" \
  empty nonzero require-source

duplicate_root="$(make_root duplicate)"
make_ci_dir "$duplicate_root"
{
  sed -n '1p' "$AUTHORITATIVE_MANIFEST"
  sed -n '2p' "$AUTHORITATIVE_MANIFEST"
  sed -n '2p' "$AUTHORITATIVE_MANIFEST"
} > "$duplicate_root/$MANIFEST_REL"
copy_source_for_source_lane "$duplicate_root"
run_case duplicate "$duplicate_root" "franken_lean-79k.1" \
  duplicate-id nonzero require-source

noncanonical_root="$(make_root noncanonical)"
make_ci_dir "$noncanonical_root"
{
  sed -n '1p' "$AUTHORITATIVE_MANIFEST"
  printf ' '
  sed -n '2p' "$AUTHORITATIVE_MANIFEST"
} > "$noncanonical_root/$MANIFEST_REL"
copy_source_for_source_lane "$noncanonical_root"
run_case noncanonical "$noncanonical_root" "franken_lean-79k.1" \
  noncanonical nonzero require-source

stale_root="$(make_root stale)"
make_ci_dir "$stale_root"
STALE_HASH="0${BASELINE_PROJECTION_HASH:1}"
[[ "$STALE_HASH" != "$BASELINE_PROJECTION_HASH" ]] \
  || STALE_HASH="1${BASELINE_PROJECTION_HASH:1}"
sed "1s/$BASELINE_PROJECTION_HASH/$STALE_HASH/" \
  "$AUTHORITATIVE_MANIFEST" > "$stale_root/$MANIFEST_REL"
copy_source_for_source_lane "$stale_root"
run_case stale "$stale_root" "franken_lean-79k.1" \
  stale-binding nonzero require-source

phantom_root="$(make_root phantom)"
copy_manifest "$phantom_root"
if [[ "$LANE" != "rch" ]]; then
  copy_source "$phantom_root"
fi
phantom_policy="$positive_policy"
run_case phantom "$phantom_root" "franken_lean-no-such-owner-ZZZ" \
  phantom-owner nonzero "$phantom_policy"

# Zero, exact, and one-over boundaries for every explicit parser/loader resource.
manifest_bytes="$(bytes_file "$AUTHORITATIVE_MANIFEST")"
header_bytes="$(sed -n '1p' "$AUTHORITATIVE_MANIFEST" | wc -c | tr -d ' ')"
max_id_bytes="$(
  tail -n +2 "$AUTHORITATIVE_MANIFEST" \
    | sed -n 's/^{"id":"\([^"]*\)"}$/\1/p' \
    | awk '{ if (length > max) max = length } END { print max + 0 }'
)"
record_count="$(( $(wc -l < "$AUTHORITATIVE_MANIFEST") - 1 ))"

resource_file_zero_root="$(make_root resource_file_zero)"
copy_manifest "$resource_file_zero_root"
copy_source_for_source_lane "$resource_file_zero_root"
run_case resource_file_zero "$resource_file_zero_root" "franken_lean-79k.1" \
  resource-exhausted/file-bytes nonzero require-source 0

resource_file_exact_root="$(make_root resource_file_exact)"
copy_manifest "$resource_file_exact_root"
run_case resource_file_exact "$resource_file_exact_root" "franken_lean-79k.1" \
  ok zero manifest-only "$manifest_bytes"

resource_file_one_over_root="$(make_root resource_file_one_over)"
copy_manifest "$resource_file_one_over_root"
copy_source_for_source_lane "$resource_file_one_over_root"
run_case resource_file_one_over "$resource_file_one_over_root" "franken_lean-79k.1" \
  resource-exhausted/file-bytes nonzero require-source \
  "$((manifest_bytes - 1))"

resource_line_zero_root="$(make_root resource_line_zero)"
copy_manifest "$resource_line_zero_root"
copy_source_for_source_lane "$resource_line_zero_root"
run_case resource_line_zero "$resource_line_zero_root" "franken_lean-79k.1" \
  resource-exhausted/line-bytes nonzero require-source "" 0

resource_line_exact_root="$(make_root resource_line_exact)"
copy_manifest "$resource_line_exact_root"
run_case resource_line_exact "$resource_line_exact_root" "franken_lean-79k.1" \
  ok zero manifest-only "" "$((header_bytes - 1))"

resource_line_one_over_root="$(make_root resource_line_one_over)"
copy_manifest "$resource_line_one_over_root"
copy_source_for_source_lane "$resource_line_one_over_root"
run_case resource_line_one_over "$resource_line_one_over_root" "franken_lean-79k.1" \
  resource-exhausted/line-bytes nonzero require-source \
  "" "$((header_bytes - 2))"

resource_records_zero_root="$(make_root resource_records_zero)"
copy_manifest "$resource_records_zero_root"
copy_source_for_source_lane "$resource_records_zero_root"
run_case resource_records_zero "$resource_records_zero_root" "franken_lean-79k.1" \
  resource-exhausted/records nonzero require-source "" "" 0

resource_records_exact_root="$(make_root resource_records_exact)"
copy_manifest "$resource_records_exact_root"
run_case resource_records_exact "$resource_records_exact_root" "franken_lean-79k.1" \
  ok zero manifest-only "" "" "$record_count"

resource_records_one_over_root="$(make_root resource_records_one_over)"
copy_manifest "$resource_records_one_over_root"
copy_source_for_source_lane "$resource_records_one_over_root"
run_case resource_records_one_over "$resource_records_one_over_root" "franken_lean-79k.1" \
  resource-exhausted/records nonzero require-source \
  "" "" "$((record_count - 1))"

resource_id_zero_root="$(make_root resource_id_zero)"
copy_manifest "$resource_id_zero_root"
copy_source_for_source_lane "$resource_id_zero_root"
run_case resource_id_zero "$resource_id_zero_root" "franken_lean-79k.1" \
  resource-exhausted/id-bytes nonzero require-source "" "" "" 0

resource_id_exact_root="$(make_root resource_id_exact)"
copy_manifest "$resource_id_exact_root"
run_case resource_id_exact "$resource_id_exact_root" "franken_lean-79k.1" \
  ok zero manifest-only "" "" "" "$max_id_bytes"

resource_id_one_over_root="$(make_root resource_id_one_over)"
copy_manifest "$resource_id_one_over_root"
copy_source_for_source_lane "$resource_id_one_over_root"
run_case resource_id_one_over "$resource_id_one_over_root" "franken_lean-79k.1" \
  resource-exhausted/id-bytes nonzero require-source \
  "" "" "" "$((max_id_bytes - 1))"

resource_depth_zero_root="$(make_root resource_depth_zero)"
copy_manifest "$resource_depth_zero_root"
copy_source_for_source_lane "$resource_depth_zero_root"
run_case resource_depth_zero "$resource_depth_zero_root" "franken_lean-79k.1" \
  resource-exhausted/parse-depth nonzero require-source \
  "" "" "" "" 0

resource_depth_exact_root="$(make_root resource_depth_exact)"
copy_manifest "$resource_depth_exact_root"
run_case resource_depth_exact "$resource_depth_exact_root" "franken_lean-79k.1" \
  ok zero manifest-only "" "" "" "" 1

resource_depth_one_over_root="$(make_root resource_depth_one_over)"
copy_manifest "$resource_depth_one_over_root"
mkdir "$resource_depth_one_over_root/.beads"
{
  sed -n '2s/}$/,"nested":{}}/p' "$AUTHORITATIVE_MANIFEST"
  tail -n +3 "$AUTHORITATIVE_MANIFEST"
} > "$resource_depth_one_over_root/$SOURCE_REL"
run_case resource_depth_one_over "$resource_depth_one_over_root" \
  "franken_lean-79k.1" resource-exhausted/parse-depth nonzero \
  require-source "" "" "" "" 1

# Recovery uses a fresh immutable copy of the exact canonical bytes; no negative
# fixture is overwritten or deleted.
recovery_root="$(make_root recovery)"
copy_manifest "$recovery_root"
if [[ "$LANE" != "rch" ]]; then
  copy_source "$recovery_root"
fi
run_case recovery "$recovery_root" "franken_lean-79k.1" \
  ok zero "$positive_policy"

BASELINE_MANIFEST_SHA_AFTER="$(
  regular_file_hash_or_state "$AUTHORITATIVE_MANIFEST"
)"
BASELINE_SOURCE_SHA_AFTER="$(
  regular_file_hash_or_state "$AUTHORITATIVE_SOURCE"
)"
if [[ "$BASELINE_MANIFEST_SHA" != "$BASELINE_MANIFEST_SHA_AFTER" \
      || "$BASELINE_SOURCE_SHA" != "$BASELINE_SOURCE_SHA_AFTER" ]]; then
  FAILURES=$((FAILURES + 1))
  note "authoritative ownership inputs changed during the immutable matrix"
fi

validate_ndjson() {
  local log_path="$1"
  local expected_records="$2"
  strict_validate_run_ndjson \
    "$log_path" \
    "$expected_records" \
    "$SCHEMA" \
    "$RUN_ID" \
    "$BEAD" \
    "$LANE" \
    "$COMMIT" \
    "$TREE" \
    "$EXPECTED_MANIFEST_HASH" \
    "$EXPECTED_PROJECTION_HASH"
}

EXPECTED_RECORDS=26
if ! validate_ndjson "$RUN_LOG" "$EXPECTED_RECORDS"; then
  FAILURES=$((FAILURES + 1))
  note "strict NDJSON validation failed"
fi

validate_artifact_links() {
  local log_path="$1"
  strict_validate_artifact_links \
    "$ART_DIR" \
    "$log_path" \
    "$LANE" \
    "$RESULT_SCHEMA" \
    "$EXPECTED_MANIFEST_HASH" \
    "$EXPECTED_PROJECTION_HASH" \
    "$BASELINE_MANIFEST_SHA" \
    "$BASELINE_SOURCE_SHA"
}

if ! validate_artifact_links "$RUN_LOG"; then
  FAILURES=$((FAILURES + 1))
  note "stdout/stderr artifact linkage failed"
fi

# Validator negative self-tests: mutate one row in an otherwise complete matrix,
# so rejection cannot be explained by a missing 25-row suffix.
jq -c 'if input_line_number == 1 then del(.worker) else . end' "$RUN_LOG" \
  > "$ART_DIR/selftest-missing.ndjson"
jq -c 'if input_line_number == 1 then .unexpected = true else . end' "$RUN_LOG" \
  > "$ART_DIR/selftest-extra.ndjson"
jq -c \
  'if input_line_number == 1
   then .schema = "fln.e2e.kernel-contract-ownership/0"
   else . end' \
  "$RUN_LOG" > "$ART_DIR/selftest-stale.ndjson"
jq -c \
  'if input_line_number == 1
   then .actual.classification = "mismatched"
   else . end' \
  "$RUN_LOG" > "$ART_DIR/selftest-mismatched.ndjson"

while IFS= read -r mutant; do
  if validate_ndjson "$ART_DIR/selftest-$mutant.ndjson" "$EXPECTED_RECORDS" \
      > "$ART_DIR/selftest-$mutant-validator.stdout" \
      2> "$ART_DIR/selftest-$mutant-validator.stderr"; then
    FAILURES=$((FAILURES + 1))
    note "strict validator accepted $mutant-field mutant"
  fi
done < <(validator_selftest_mutants)

jq -cn \
  --arg schema "fln.validation.kernel-contract-ownership/1" \
  --arg run_id "$RUN_ID" \
  --arg verdict "$([[ "$FAILURES" -eq 0 ]] && printf pass || printf fail)" \
  --arg run_sha "$(sha256_file "$RUN_LOG")" \
  --arg baseline_manifest_before "$BASELINE_MANIFEST_SHA" \
  --arg baseline_manifest_after "$BASELINE_MANIFEST_SHA_AFTER" \
  --arg baseline_source_before "$BASELINE_SOURCE_SHA" \
  --arg baseline_source_after "$BASELINE_SOURCE_SHA_AFTER" \
  --argjson records "$EXPECTED_RECORDS" \
  --argjson failures "$FAILURES" \
  '{
    schema:$schema,
    run_id:$run_id,
    verdict:$verdict,
    records:$records,
    failures:$failures,
    run_sha256:$run_sha,
    authoritative_manifest_sha256:{
      before:$baseline_manifest_before,
      after:$baseline_manifest_after
    },
    authoritative_source_sha256:{
      before:$baseline_source_before,
      after:$baseline_source_after
    },
    cleanup_result:"retained_by_policy"
  }' > "$VALIDATION"

# Manifest every retained file except the manifest and completion marker themselves.
: > "$ARTIFACT_MANIFEST"
if ! (
  find "$ART_DIR" -type f \
    ! -path "$ARTIFACT_MANIFEST" \
    ! -path "$BUNDLE" \
    -printf '%P\n' | LC_ALL=C sort
  ) | while IFS= read -r rel; do
    jq -cn \
      --arg schema "fln.evidence-manifest.kernel-contract-ownership/1" \
      --arg path "$rel" \
      --arg sha "$(sha256_file "$ART_DIR/$rel")" \
      --argjson bytes "$(bytes_file "$ART_DIR/$rel")" \
      '{schema:$schema,path:$path,sha256:$sha,bytes:$bytes}' \
      >> "$ARTIFACT_MANIFEST" || exit 1
  done; then
  note "artifact enumeration failed"
  exit 1
fi

validate_artifact_manifest() {
  local manifest="$1"
  jq -s -e '
    length > 0
    and all(.[];
      .schema == "fln.evidence-manifest.kernel-contract-ownership/1"
      and (keys == ["bytes","path","schema","sha256"])
      and (.path | type == "string" and length > 0)
      and (.sha256 | test("^[0-9a-f]{64}$"))
      and (.bytes | type == "number" and . >= 0 and floor == .)
    )
  ' "$manifest" >/dev/null || return 1

  local listed_paths
  local actual_paths
  local expected_paths
  local manifest_rows
  listed_paths="$(
    jq -r '.path' "$manifest"
  )" || return 1
  actual_paths="$(
    find "$ART_DIR" -type f \
      ! -path "$ARTIFACT_MANIFEST" \
      ! -path "$BUNDLE" \
      -printf '%P\n' | LC_ALL=C sort
  )" || return 1
  expected_paths="$(
    expected_artifact_paths "$LANE" | LC_ALL=C sort
  )" || return 1
  [[ "$listed_paths" == "$expected_paths" ]] || return 1
  [[ "$actual_paths" == "$expected_paths" ]] || return 1

  manifest_rows="$(
    jq -r '
      select(
        .schema == "fln.evidence-manifest.kernel-contract-ownership/1"
        and (keys == ["bytes","path","schema","sha256"])
      )
      | [.path,.sha256,(.bytes|tostring)] | @tsv
    ' "$manifest"
  )" || return 1
  while IFS=$'\t' read -r rel expected_sha expected_bytes; do
    [[ "$rel" != /* && "$rel" != *".."* ]] || return 1
    local artifact="$ART_DIR/$rel"
    [[ -f "$artifact" && ! -L "$artifact" ]] || return 1
    [[ "$(sha256_file "$artifact")" == "$expected_sha" ]] || return 1
    [[ "$(bytes_file "$artifact")" == "$expected_bytes" ]] || return 1
  done <<< "$manifest_rows"
}

if ! validate_artifact_manifest "$ARTIFACT_MANIFEST"; then
  FAILURES=$((FAILURES + 1))
  note "independent artifact-manifest validation failed"
fi

if (( FAILURES == 0 )) \
    && ! validate_existing_bundle \
      "$ART_DIR" components "$COMMIT" "$TREE"; then
  FAILURES=$((FAILURES + 1))
  note "independent read-only component validation failed"
fi

if (( FAILURES == 0 )) \
    && ! validate_retained_manifest_semantics \
      "$ART_DIR" \
      "$LANE" \
      "$EXPECTED_MANIFEST_HASH" \
      "$EXPECTED_PROJECTION_HASH"; then
  FAILURES=$((FAILURES + 1))
  note "retained ownership semantic validation failed"
fi

if (( FAILURES != 0 )); then
  jq -cn \
    --arg schema "fln.evidence-bundle-validation-failure.kernel-contract-ownership/1" \
    --arg run_id "$RUN_ID" \
    --arg manifest_sha "$(sha256_file "$ARTIFACT_MANIFEST")" \
    --arg run_sha "$(sha256_file "$RUN_LOG")" \
    --arg validation_sha "$(sha256_file "$VALIDATION")" \
    --argjson failures "$FAILURES" \
    '{
      schema:$schema,
      run_id:$run_id,
      artifact_manifest_sha256:$manifest_sha,
      run_sha256:$run_sha,
      validation_sha256:$validation_sha,
      failures:$failures,
      verdict:"fail",
      reason:"independent_read_only_validation_failed",
      cleanup_result:"retained_by_policy"
    }' > "$ART_DIR/bundle.validation-failed.json"
  note "retained failed evidence set without a completion marker: $ART_DIR"
  note "$FAILURES validation failure(s)"
  exit 1
fi

BUNDLE_ARTIFACT_MANIFEST_SHA="$(
  sha256_file "$ARTIFACT_MANIFEST"
)" || { note "could not hash artifact manifest"; exit 1; }
BUNDLE_RUN_SHA="$(
  sha256_file "$RUN_LOG"
)" || { note "could not hash run log"; exit 1; }
BUNDLE_VALIDATION_SHA="$(
  sha256_file "$VALIDATION"
)" || { note "could not hash validation record"; exit 1; }
BUNDLE_FILE_COUNT="$(
  wc -l < "$ARTIFACT_MANIFEST" | tr -d ' '
)" || { note "could not count artifact manifest records"; exit 1; }
[[ "$BUNDLE_ARTIFACT_MANIFEST_SHA" =~ ^[0-9a-f]{64}$ \
    && "$BUNDLE_RUN_SHA" =~ ^[0-9a-f]{64}$ \
    && "$BUNDLE_VALIDATION_SHA" =~ ^[0-9a-f]{64}$ \
    && "$BUNDLE_FILE_COUNT" =~ ^[0-9]+$ \
    && "$BUNDLE_FILE_COUNT" -gt 0 ]] \
  || { note "completion-marker inputs are not canonical"; exit 1; }

BUNDLE_PAYLOAD="$(
  jq -cn \
  --arg schema "fln.evidence-bundle.kernel-contract-ownership/1" \
  --arg run_id "$RUN_ID" \
  --arg artifact_manifest_sha "$BUNDLE_ARTIFACT_MANIFEST_SHA" \
  --arg run_sha "$BUNDLE_RUN_SHA" \
  --arg validation_sha "$BUNDLE_VALIDATION_SHA" \
  --argjson files "$BUNDLE_FILE_COUNT" \
  '{
    schema:$schema,
    run_id:$run_id,
    verdict:"pass",
    artifact_manifest:"artifact-manifest.ndjson",
    artifact_manifest_sha256:$artifact_manifest_sha,
    run_sha256:$run_sha,
    validation_sha256:$validation_sha,
    files:$files,
    cleanup_result:"retained_by_policy"
  }'
)" || { note "completion-marker construction failed"; exit 1; }

printf '%s\n' "$BUNDLE_PAYLOAD" > "$BUNDLE_PENDING" \
  || { note "completion-marker pending write failed"; exit 1; }

if ! jq -e \
    --arg run_id "$RUN_ID" \
    --arg manifest_sha "$BUNDLE_ARTIFACT_MANIFEST_SHA" \
    --arg run_sha "$BUNDLE_RUN_SHA" \
    --arg validation_sha "$BUNDLE_VALIDATION_SHA" \
    --argjson files "$BUNDLE_FILE_COUNT" '
      keys == [
        "artifact_manifest","artifact_manifest_sha256","cleanup_result",
        "files","run_id","run_sha256","schema","validation_sha256","verdict"
      ]
      and .schema == "fln.evidence-bundle.kernel-contract-ownership/1"
      and .run_id == $run_id
      and .artifact_manifest == "artifact-manifest.ndjson"
      and .artifact_manifest_sha256 == $manifest_sha
      and .run_sha256 == $run_sha
      and .validation_sha256 == $validation_sha
      and (.artifact_manifest_sha256 | test("^[0-9a-f]{64}$"))
      and (.run_sha256 | test("^[0-9a-f]{64}$"))
      and (.validation_sha256 | test("^[0-9a-f]{64}$"))
      and .files == $files
      and (.files | type == "number" and . > 0 and floor == .)
      and .verdict == "pass"
      and .cleanup_result == "retained_by_policy"
    ' "$BUNDLE_PENDING" >/dev/null; then
  note "completion-marker payload validation failed"
  exit 1
fi
mv -n -- "$BUNDLE_PENDING" "$BUNDLE"
[[ -f "$BUNDLE" && ! -L "$BUNDLE" && ! -e "$BUNDLE_PENDING" ]] \
  || { note "completion-marker publication failed"; exit 1; }

FINAL_BUNDLE_SHA="$(sha256_file "$BUNDLE")" \
  || { note "could not hash published completion marker"; exit 1; }
[[ "$FINAL_BUNDLE_SHA" =~ ^[0-9a-f]{64}$ ]] \
  || { note "published completion-marker hash is not canonical"; exit 1; }

note "retained bundle: $ART_DIR"
note "bundle sha256: $FINAL_BUNDLE_SHA"
note "PASS: $EXPECTED_RECORDS immutable scenarios and independent bundle validation"
