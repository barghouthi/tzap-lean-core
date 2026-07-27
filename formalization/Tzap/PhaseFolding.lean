import Tzap.Semantics

/-! # The phase-folding rewrite

This file states and proves the paper's phase-folding theorem for the exact
weighted-relation semantics. Circuit equivalence (`Equivalent`) is equality of
the denoted weighted relations — full equality of all complex amplitudes, not
merely equality up to global phase.

The rewrite considers a circuit of the shape

  `pre ; Rz θ q ; middle ; Rz φ q' ; suffix`

and a side `Condition`: on every nonzero-amplitude path, the bit at qubit `q`
after `pre` equals the bit at qubit `q'` after `middle`. Since
`Rz θ = diag(1, e^{iθ})` contributes the phase `e^{iθ·bit}` and equal bits
make the two phases multiply as `e^{i(θ+φ)·bit}` (`Semantics.phase_add`), the
first rotation can be removed and its angle added into the second:

  `pre ; middle ; Rz (θ+φ) q' ; suffix`.

The `Condition` itself is discharged, in `Tzap.Algorithm`, by the parity
analysis via `Soundness.parity_equality_sound`.
-/

namespace Tzap.PhaseFolding

open Tzap.Semantics

noncomputable section

/-- Semantic equivalence of circuits: `C` and `D` denote the same weighted
relation, i.e. every input/output amplitude coincides exactly. -/
def Equivalent {n : Nat} (C D : Circuit n) : Prop :=
  Semantics.circuit C = Semantics.circuit D

/-- The paper's side condition for merging two rotations. For every input
`x₀`, if `pre` can reach `x` (nonzero amplitude) and `middle` can carry `x` to
`x'` (nonzero amplitude), then the bit at qubit `q` after the prefix equals
the bit at qubit `q'` after the middle: `x q = x' q'`. -/
def Condition {n : Nat} (pre middle : Circuit n) (q q' : Fin n) : Prop :=
  ∀ x₀ x x' : Basis n,
    Semantics.circuit pre x₀ x ≠ 0 →
    Semantics.circuit middle x x' ≠ 0 →
    x q = x' q'

/-- The redex: `pre ; Rz θ q ; middle ; Rz φ q' ; suffix`, a circuit with two
rotation sites whose angles are candidates for merging. -/
def leftCircuit {n : Nat} (pre middle suffix : Circuit n)
    (θ φ : ℝ) (q q' : Fin n) : Circuit n :=
  pre ++ (.rz θ q :: (middle ++ (.rz φ q' :: suffix)))

/-- The contractum: `pre ; middle ; Rz (θ+φ) q' ; suffix` — the first rotation
is removed and its angle `θ` folded into the second rotation site. -/
def rightCircuit {n : Nat} (pre middle suffix : Circuit n)
    (θ φ : ℝ) (q' : Fin n) : Circuit n :=
  pre ++ (middle ++ (.rz (θ + φ) q' :: suffix))

/-- Pointwise form of the rewrite after the prefix has been peeled off: at a
fixed intermediate state `x` where the bit at `q` is propagated unchanged to
`q'` through `middle` (hypothesis `hbits`), the two tails have identical
amplitudes. The `Rz θ q` phase factor `phase θ (x q)` is pushed through the
sum over intermediate states and recombined with `φ` via
`Semantics.phase_add`. -/
theorem fold_tail {n : Nat} (middle suffix : Circuit n) (θ φ : ℝ)
    (q q' : Fin n) (x z : Basis n)
    (hbits : ∀ y : Basis n,
      Semantics.circuit middle x y ≠ 0 → x q = y q') :
    Semantics.circuit (.rz θ q :: (middle ++ (.rz φ q' :: suffix))) x z =
      Semantics.circuit (middle ++ (.rz (θ + φ) q' :: suffix)) x z := by
  rw [Semantics.rz_cons_apply]
  rw [Semantics.circuit_append, Semantics.circuit_append]
  simp only [WeightedRelation.comp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [Semantics.rz_cons_apply, Semantics.rz_cons_apply]
  by_cases hmiddle : Semantics.circuit middle x y = 0
  · simp [hmiddle]
  · have hxy := hbits y hmiddle
    rw [hxy]
    rw [← Semantics.phase_add]
    ring

/-!
## MAIN THEOREM: phase_folding

**Statement.** Suppose the side `Condition` holds: on every nonzero-amplitude
path, the bit at qubit `q` after `pre` equals the bit at qubit `q'` after
`middle`. Then the circuit `pre ; Rz θ q ; middle ; Rz φ q' ; suffix` is
`Equivalent` — equal as a weighted relation, amplitude for amplitude — to
`pre ; middle ; Rz (θ+φ) q' ; suffix`. That is, moving the angle `θ` from the
first rotation into the second preserves the exact semantics: on every
supported path both rotations see the same bit, so their diagonal phases
combine as `e^{iθ·bit} · e^{iφ·bit} = e^{i(θ+φ)·bit}`, and paths with zero
amplitude contribute nothing to either side.

**Significance.** This is the semantic justification of each individual merge
performed by Algorithm 1; the parity analysis (via
`Soundness.parity_equality_sound`) supplies the `Condition`, and the
randomized variant reuses it in `RandomizedPhaseFolding`.
-/

/-- The exact phase-folding theorem from the paper: under `Condition`, the
merged circuit is amplitude-for-amplitude equal to the original. Proved by
splitting the sum at the state after `pre` and applying `fold_tail`. -/
theorem phase_folding {n : Nat} (pre middle suffix : Circuit n)
    (θ φ : ℝ) (q q' : Fin n)
    (hcondition : Condition pre middle q q') :
    Equivalent (leftCircuit pre middle suffix θ φ q q')
      (rightCircuit pre middle suffix θ φ q') := by
  funext input output
  simp only [leftCircuit, rightCircuit] at *
  rw [Semantics.circuit_append, Semantics.circuit_append]
  simp only [WeightedRelation.comp]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hprefix : Semantics.circuit pre input x = 0
  · simp [hprefix]
  · rw [fold_tail middle suffix θ φ q q' x output]
    intro y hmiddle
    exact hcondition input x y hprefix hmiddle

end
end Tzap.PhaseFolding
