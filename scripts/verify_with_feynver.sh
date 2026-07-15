#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "usage: $0 path/to/circuit.qasm [output-dir]" >&2
  exit 1
fi

src="$1"
out="${2:-/private/tmp/tzap-feynver-one}"
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
mkdir -p "$out"

name="$(basename "$src" .qasm)"
opt_qasm="$out/$name.superopt-phasefold-fixpoint.qasm"
orig_qc="$out/$name.orig.qc"
opt_qc="$out/$name.superopt-phasefold-fixpoint.qc"
mut_qc="$out/$name.mutated-extra-x.qc"

feynver="${FEYNVER:-$HOME/git/feynman/dist-newstyle/build/aarch64-osx/ghc-9.14.1/Feynman-0.1.0.0/x/feynver/build/feynver/feynver}"
converter="$repo_root/scripts/qasm_to_qc.py"

"$repo_root/target/release/tzap" "$src" \
  --passes SuperOpt, PhaseFoldRand \
  --fixpoint \
  -o "$opt_qasm"

python3 "$converter" "$src" "$orig_qc"
python3 "$converter" "$opt_qasm" "$opt_qc"

in_gates=$(awk 'BEGIN{c=0} /^[[:space:]]*($|OPENQASM|include|qreg|creg|\/\/)/{next} {c++} END{print c}' "$src")
out_gates=$(awk 'BEGIN{c=0} /^[[:space:]]*($|OPENQASM|include|qreg|creg|\/\/)/{next} {c++} END{print c}' "$opt_qasm")
in_t=$(awk 'BEGIN{c=0} /^[[:space:]]*(t|tdg)[[:space:]]+/{c++} END{print c}' "$src")
out_t=$(awk 'BEGIN{c=0} /^[[:space:]]*(t|tdg)[[:space:]]+/{c++} END{print c}' "$opt_qasm")

echo "counts: gates $in_gates -> $out_gates, T $in_t -> $out_t"

echo -n "feynver: "
"$feynver" -ignore-global-phase "$orig_qc" "$opt_qc"

cp "$opt_qc" "$mut_qc"
python3 - "$mut_qc" <<'PY'
import sys

path = sys.argv[1]
text = open(path).read()
if "\nEND\n" in text:
    text = text.replace("\nEND\n", "\nX q0\nEND\n", 1)
elif text.endswith("END\n"):
    text = text[:-4] + "X q0\nEND\n"
else:
    raise SystemExit("could not find END")
open(path, "w").write(text)
PY

echo -n "negative control: "
"$feynver" -ignore-global-phase "$orig_qc" "$mut_qc"

echo "files written to $out"
