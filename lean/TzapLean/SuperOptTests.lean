import TzapLean.SuperOptProof

/-!
# `SuperOpt`: tests

The behavioural half of `src/super_opt/tests.rs`. Rust's remaining tests cover machinery this
port does not have — the on-disk cache, the matrix-store arena, incremental mode, the
subcircuit/rewrite reports — or assert `circuits_equiv`, which here is a theorem for every
input (`superOptGates_correct`).

The exact-matrix checks come first: they are what a floating-point implementation would get
subtly wrong, and what the cyclotomic representation exists to get right.

The pass tests share **one** table. Each `#guard` is evaluated independently, so a table
built inside each would be rebuilt each time; `passFailures` therefore builds it once and
runs every case against it. When a case fails, `#eval passFailures` names it.
-/

namespace TzapLean

open Gate

/-! ## Exact matrices -/

/-- Two gate lists with the same exact matrix, up to one of the eight Clifford+T phases. -/
def eqUpToPhase (k : Nat) (gs hs : List Gate) : Bool :=
  match ExactMat.matrixOf k gs, ExactMat.matrixOf k hs with
  | some A, some B => (ExactMat.phaseMatch A.normalize B.normalize).isSome
  | _, _ => false

/-! `x` and `−x` are the same operator; `s` and `sdg` are not. A representation that rounded,
or that canonicalized phase by dividing, could get either of these wrong. -/

-- `phase_equivalence_ignores_global_phase`: `z·x·z = -x`.
#guard eqUpToPhase 1 [x 0] [z 0, x 0, z 0]
#guard !eqUpToPhase 1 [s 0] [sdg 0]
-- `identity_matches_omega_identity`, `hh_is_identity`.
#guard eqUpToPhase 1 [] [h 0, h 0]
#guard eqUpToPhase 1 [] [x 0, x 0]
#guard eqUpToPhase 1 [] [s 0, s 0, s 0, s 0]
-- `ccx_and_ccz_have_different_keys`.
#guard !eqUpToPhase 3 [ccx 0 1 2] [ccz 0 1 2]
-- Control and target are not interchangeable.
#guard !eqUpToPhase 2 [cnot 0 1] [cnot 1 0]
-- Textbook identities, as matrix facts.
#guard eqUpToPhase 2 [h 1, cnot 0 1, h 1] [cz 0 1]
#guard eqUpToPhase 1 [t 0, t 0, t 0, t 0] [z 0]
#guard eqUpToPhase 1 [h 0, z 0, h 0] [x 0]
#guard eqUpToPhase 2 [x 0, cnot 0 1, x 0] [x 1, cnot 0 1]
#guard eqUpToPhase 2 [t 0, cnot 0 1, tdg 0] [cnot 0 1]
#guard eqUpToPhase 2 [cnot 0 1, cnot 1 0, cnot 0 1] [cnot 1 0, cnot 0 1, cnot 1 0]

/-! ## The library gate set

`library_gates(k)` has `7k` one-wire gates and `k(k−1)` `CNOT`s — Rust asserts exactly these
counts. `ccx` and `cz` are absent by design, so a rewrite never introduces them. -/

#guard (libGates 1).length == 7
#guard (libGates 2).length == 16
#guard (libGates 3).length == 27
#guard (libGates 4).length == 40

/-! ## The table

Rust asserts a depth-1 width-1 table holds 8 unitaries and reports depth 1. -/

/-- A depth-1 width-1 table, for the counts Rust checks. -/
def tinyTable : WidthTable := buildWidth 1 { maxQubits := 1, maxGates := 1 }

#guard tinyTable.size == 8
#guard tinyTable.depth == 1
#guard !tinyTable.saturated

-- The entry cap stops the build and says so.
#guard (buildWidth 2 { maxQubits := 2, maxGates := 4, maxEntriesPerQubit := 20 }).saturated

/-! ## The pass -/

/-- Two wires, replacements of up to three gates. -/
def tcfg : SuperOptTableConfig := { maxQubits := 2, maxGates := 3 }

/-- Windows of up to six gates on up to two wires. -/
def cfg : SuperOptConfig := { maxQubits := 2, maxWindow := 6 }

/-- Each case is a name, a wire count, an input, and the expected output. -/
def passCases : List (String × Nat × List Gate × List Gate) :=
  [ -- `empty_circuit_is_unchanged`, `single_gate_is_unchanged`
    ("empty", 1, [], []),
    ("single gate", 1, [h 0], [h 0]),
    -- self-inverse pairs, found by lookup rather than by rule
    ("hh", 1, [h 0, h 0], []),
    ("xx", 1, [x 0, x 0], []),
    ("t tdg", 1, [t 0, tdg 0], []),
    ("ssss", 2, [s 0, s 0, s 0, s 0], []),
    ("cx cx", 2, [cnot 0 1, cnot 0 1], []),
    -- rotations fold
    ("tt", 1, [t 0, t 0], [s 0]),
    ("ss", 1, [s 0, s 0], [z 0]),
    ("tttt", 1, [t 0, t 0, t 0, t 0], [z 0]),
    ("s tttt", 1, [s 0, t 0, t 0, t 0, t 0], [sdg 0]),
    -- conjugations the pass discovers
    ("h z h", 1, [h 0, z 0, h 0], [x 0]),
    ("h x h", 1, [h 0, x 0, h 0], [z 0]),
    ("(hs)^3", 1, [h 0, s 0, h 0, s 0, h 0, s 0], []),
    ("x on control", 2, [x 0, cnot 0 1, x 0], [x 1, cnot 0 1]),
    ("t through control", 2, [t 0, cnot 0 1, tdg 0], [cnot 0 1]),
    -- CZ is not in the library, so `h·cx·h` has no replacement the pass may emit
    ("h cx h stays", 2, [h 1, cnot 0 1, h 1], [h 1, cnot 0 1, h 1]),
    -- a SWAP is already optimal
    ("swap stays", 2, [cnot 0 1, cnot 1 0, cnot 0 1], [cnot 0 1, cnot 1 0, cnot 0 1]),
    -- windows are subsequences: a gate on other wires is skipped and re-emitted
    ("skip disjoint", 2, [t 0, h 1, t 0], [s 0, h 1]),
    ("skip reset", 2, [h 0, reset 1, h 0], [reset 1]),
    ("skip measure", 2, [h 0, measure 1 0, h 0], [measure 1 0]),
    -- …but a barrier on the window's own wire stops it, and both sides still optimize
    ("measure splits", 1, [h 0, h 0, measure 0 0, h 0, h 0], [measure 0 0]),
    ("rz blocks", 1, [h 0, rz (1/3) 0, h 0], [h 0, rz (1/3) 0, h 0]),
    ("rz then pair", 1, [rz (1/3) 0, h 0, h 0], [rz (1/3) 0]),
    -- a three-wire gate is out of a two-wire window's reach
    ("ccx out of reach", 3, [ccx 0 1 2, ccx 0 1 2], [ccx 0 1 2, ccx 0 1 2]),
    -- the Toffoli decomposition has no two-wire win: its `T`s sit on three-wire parities
    ("toffoli decomp", 3,
      [h 2, cnot 1 2, tdg 2, cnot 0 2, t 2, cnot 1 2, tdg 2, cnot 0 2, t 1, t 2, h 2],
      [h 2, cnot 1 2, tdg 2, cnot 0 2, t 2, cnot 1 2, tdg 2, cnot 0 2, t 1, t 2, h 2]) ]

/-- Cases whose output differs from what is expected — empty when all pass. One table serves
every case. -/
def passFailures : List String :=
  let tbl := buildTable tcfg
  passCases.filterMap fun (name, n, inp, want) =>
    if superOptGates cfg tbl n inp == want then none else some name

#guard passFailures.isEmpty

/-- Running the pass on its own output changes nothing further. -/
def idempotentFailures : List String :=
  let tbl := buildTable tcfg
  passCases.filterMap fun (name, n, inp, _) =>
    let once := superOptGates cfg tbl n inp
    if superOptGates cfg tbl n once == once then none else some name

#guard idempotentFailures.isEmpty

/-! ## Three-wire windows

At width 3 the table reaches `ccx` and `ccz` windows, which two-wire windows cannot. -/

/-- Cases needing a three-wire table. -/
def wide3Failures : List String :=
  let tbl := buildTable { maxQubits := 3, maxGates := 1 }
  let cfg3 : SuperOptConfig := { maxQubits := 3, maxWindow := 6 }
  [("ccx pair", [ccx 0 1 2, ccx 0 1 2]),
   ("ccz pair", [ccz 0 1 2, ccz 0 1 2]),
   ("cz pair", [Gate.cz 0 1, Gate.cz 0 1])].filterMap fun (name, inp) =>
    if superOptGates cfg3 tbl 3 inp == ([] : List Gate) then none else some name

#guard wide3Failures.isEmpty

end TzapLean
