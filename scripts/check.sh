#!/usr/bin/env bash
# Run the repository checks; CI runs this script on each push and pull request.
# Each check fails the script on a mismatch. Audits and finite checks are compared with the
# recorded outputs in validation/ and research/, so a change in any of them must be recorded.
# The exhaustive prefix-lemma check (scripts/check_prefix_lemma.py, about a minute) is not run
# here: Lean proves the lemma in general (prefix_pairs_distinct).
set -euo pipefail
cd "$(dirname "$0")/.."

actual=$(mktemp "${TMPDIR:-/tmp}/check.XXXXXX")
trap 'rm -f "$actual"' EXIT

# Compare a command's output with a recorded file.
expect() {
  local recorded=$1
  shift
  "$@" > "$actual" 2>&1
  if ! diff -u "$recorded" "$actual"; then
    echo "error: output of '$*' differs from $recorded" >&2
    exit 1
  fi
  echo "ok: $* matches $recorded"
}

python3 scripts/palomar/check-lean-sources.py
ruby scripts/palomar/validate-formalization.rb formalization.yaml

# Default targets: ShortGCD, Challenge and Solution. Challenge's `sorry` warnings are expected.
lake build

expect validation/axioms.txt lake env lean validation/Axioms.lean
expect research/register-axioms.txt lake env lean research/RegisterProgram.lean
expect research/prefix-policy-axioms.txt lake env lean research/PrefixPolicies.lean

expect validation/replay.json python3 scripts/check_certificates.py
expect research/register-validation.json python3 research/check_register_program.py
expect research/register-validation.json python3 -O research/check_register_program.py
expect research/rebuilding-validation.json python3 research/rebuilding_program.py
expect research/rebuilding-validation.json python3 -O research/rebuilding_program.py

# The examples record wall-clock seconds, which are dropped before comparing.
python3 remainder_only_certificate.py | sed -E 's/, "seconds": [0-9.]+//' > "$actual"
if ! diff -u <(sed -E 's/, "seconds": [0-9.]+//' validation/examples.jsonl) "$actual"; then
  echo "error: remainder_only_certificate.py output differs from validation/examples.jsonl" >&2
  exit 1
fi
echo "ok: remainder_only_certificate.py matches validation/examples.jsonl"
