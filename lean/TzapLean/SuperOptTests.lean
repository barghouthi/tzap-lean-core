import TzapLean.SuperOptProof

/-!
# `SuperOpt`: tests

The behavioural half of `src/super_opt/tests.rs`. Rust's remaining tests cover machinery this
port does not have — the on-disk table cache, the matrix-store arena, incremental mode, the
subcircuit/rewrite reports — or assert `circuits_equiv`, which here is a theorem for every
input (`superOptGates_correct`).

The exact-matrix checks come first: they are what a floating-point implementation would get
subtly wrong, and what the cyclotomic representation exists to get right.
-/

namespace TzapLean

open Gate

/-- Two gate lists with the same exact matrix, up to one of the eight Clifford+T phases. -/
def eqUpToPhase (k : Nat) (gs hs : List Gate) : Bool :=
  match ExactMat.matrixOf k gs, ExactMat.matrixOf k hs with
  | some A, some B => (ExactMat.phaseMatch A.normalize B.normalize).isSome
  | _, _ => false

/-! ### Exact matrices

`x` and `-x` are the same operator; `s` and `sdg` are not. A representation that rounded, or
that canonicalized phase by dividing, could get either of these wrong. -/

-- `phase_equivalence_ignores_global_phase`: `z·x·z = -x`.
#guard eqUpToPhase 1 [x 0] [z 0, x 0, z 0]
-- …but the phase test does not equate genuinely different gates.
#guard !eqUpToPhase 1 [s 0] [sdg 0]
-- `identity_matches_omega_identity` / `hh_is_identity`.
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

/-! ### The pass -/

/-- Two wires, windows of up to six gates, replacements of up to two. -/
def cfg2 : SuperOptConfig := { maxQubits := 2, maxWindow := 6, maxSearch := 2 }

/-- Three wires, so `ccx`/`ccz` windows are in range. -/
def cfg3 : SuperOptConfig := { maxQubits := 3, maxWindow := 6, maxSearch := 1 }

def so (n : Nat) (gs : List Gate) : List Gate := superOptGates cfg2 n gs

-- `empty_circuit_is_unchanged`, `single_gate_is_unchanged`.
#guard so 1 [] == []
#guard so 1 [h 0] == [h 0]

-- Self-inverse pairs disappear, found by search rather than by rule.
#guard so 1 [h 0, h 0] == []
#guard so 1 [x 0, x 0] == []
#guard so 1 [t 0, tdg 0] == []
#guard so 2 [s 0, s 0, s 0, s 0] == []
#guard so 2 [cnot 0 1, cnot 0 1] == []

-- Rotations fold.
#guard so 1 [t 0, t 0] == [s 0]
#guard so 1 [s 0, s 0] == [z 0]
#guard so 1 [t 0, t 0, t 0, t 0] == [z 0]
#guard so 1 [s 0, t 0, t 0, t 0, t 0] == [sdg 0]

-- Conjugations the pass discovers: `h·z·h = x`, `h·x·h = z`, `h·cx·h = cz`.
#guard so 1 [h 0, z 0, h 0] == [x 0]
#guard so 1 [h 0, x 0, h 0] == [z 0]
#guard so 2 [h 1, cnot 0 1, h 1] == [cz 1 0]
-- `X` on the control of a `CNOT` moves to its target.
#guard so 2 [x 0, cnot 0 1, x 0] == [x 1, cnot 0 1]
-- A phase on the control commutes through.
#guard so 2 [t 0, cnot 0 1, tdg 0] == [cnot 0 1]

-- A `SWAP` is already optimal: three `CNOT`s stay three.
#guard (so 2 [cnot 0 1, cnot 1 0, cnot 0 1]).length == 3

/-! ### Windows are subsequences

A gate on other wires between two window members does not block the window; it is skipped and
re-emitted. `measure` and `reset` may be skipped this way too — they only kill a window whose
wires they touch. -/

-- A disjoint gate in the middle, and a disjoint `reset`.
#guard so 2 [t 0, h 1, t 0] == [s 0, h 1]
#guard so 2 [h 0, reset 1, h 0] == [reset 1]
#guard so 2 [h 0, measure 1 0, h 0] == [measure 1 0]

-- …but a barrier on the window's own wire stops it, and both sides still optimize.
#guard so 1 [h 0, h 0, measure 0 0, h 0, h 0] == [measure 0 0]
#guard so 1 [h 0, rz (1/3) 0, h 0] == [h 0, rz (1/3) 0, h 0]
#guard so 1 [rz (1/3) 0, h 0, h 0] == [rz (1/3) 0]

/-! ### Window limits -/

-- A three-wire gate is out of a two-wire window's reach…
#guard so 3 [ccx 0 1 2, ccx 0 1 2] == [ccx 0 1 2, ccx 0 1 2]
-- …and in reach at three.
#guard superOptGates cfg3 3 [ccx 0 1 2, ccx 0 1 2] == []
#guard superOptGates cfg3 3 [ccz 0 1 2, ccz 0 1 2] == []
#guard superOptGates cfg3 3 [Gate.cz 0 1, Gate.cz 0 1] == []

-- The Toffoli decomposition has no two-wire win: its `T`s sit on three-wire parities.
#guard (so 3 [h 2, cnot 1 2, tdg 2, cnot 0 2, t 2, cnot 1 2, tdg 2, cnot 0 2, t 1, t 2,
  h 2]).length == 11

/-! ### The pass is a fixed point on its own output -/

#guard so 2 (so 2 [h 0, cnot 0 1, h 0, h 1, cnot 0 1, h 1]) ==
  so 2 [h 0, cnot 0 1, h 0, h 1, cnot 0 1, h 1]
#guard so 1 (so 1 [t 0, t 0, t 0]) == so 1 [t 0, t 0, t 0]

end TzapLean
