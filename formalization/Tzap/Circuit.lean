import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Circuit Syntax

Purely syntactic definitions shared by the whole development: computational basis states,
the gate set, and circuits.

* `Basis n = Fin n → Bool` — a computational basis state of `n` qubits, one Boolean per wire.
* `Gate n` — the paper's gate set: `CNOT`, Hadamard, `X` (NOT), and the `z`-rotation `Rz θ`.
  This set is universal, and only `Rz` carries a continuous parameter, which is exactly what
  phase folding optimizes.
* `Circuit n = List (Gate n)` — a circuit is a gate list, executed head-first.

The `Basis` namespace defines how the classical (permutation) gates act on basis states:
`update` writes one bit, `flip` implements `X`, and `cnot` xors the control into the target.
These functions are the "shapes" appearing in the exact gate semantics
(`Semantics.gate`) and in the nonzero-amplitude shape lemma `Semantics.gate_ne_zero_shape`,
which the soundness proof matches against the symbolic transfer functions of
`Tzap/Symbolic.lean`.
-/

namespace Tzap

/-- Computational basis states of `n` qubits: a Boolean value for each wire `Fin n`.
Weighted relations over `Basis n` (see `Tzap/Semantics.lean`) are `2ⁿ × 2ⁿ` matrices. -/
abbrev Basis (n : Nat) := Fin n → Bool

/-- The four gate forms used in the paper: `CNOT` (controlled-NOT), Hadamard, `X` (NOT), and the
`z`-rotation `Rz θ = diag(1, e^{iθ})`. Only `Rz` has a real parameter; phase folding merges `Rz`
gates whose target parities coincide, adding their angles. -/
inductive Gate (n : Nat) where
  | cnot (control target : Fin n)
  | hadamard (target : Fin n)
  | x (target : Fin n)
  | rz (angle : ℝ) (target : Fin n)

/-- Circuits execute from the head of the list to the tail: `g :: gs` applies `g` first.
Semantically this matches the diagrammatic composition order of `WeightedRelation.comp`. -/
abbrev Circuit (n : Nat) := List (Gate n)

namespace Basis

/-- `update b q v` is the basis state `b` with qubit `q` overwritten to `v`;
all other qubits are unchanged. -/
def update {n : Nat} (b : Basis n) (q : Fin n) (v : Bool) : Basis n :=
  fun r => if r = q then v else b r

/-- `flip b q` negates qubit `q` of `b` — the action of the `X` gate on basis states. -/
def flip {n : Nat} (b : Basis n) (q : Fin n) : Basis n :=
  update b q (!b q)

/-- `cnot b c t` xors the control bit `b c` into the target bit `b t` — the action of the
`CNOT` gate on basis states. Mirrored symbolically by the `.cnot` case of `Symbolic.step`,
which xors the control's parity into the target's. -/
def cnot {n : Nat} (b : Basis n) (c t : Fin n) : Basis n :=
  update b t (b t != b c)

/-- Reading the updated qubit returns the written value. -/
@[simp] theorem update_same {n} (b : Basis n) (q : Fin n) (v : Bool) :
    update b q v q = v := by simp [update]

/-- Reading any other qubit returns the original value. -/
@[simp] theorem update_ne {n} (b : Basis n) (q r : Fin n) (v : Bool)
    (h : r ≠ q) : update b q v r = b r := by simp [update, h]

end Basis
end Tzap
