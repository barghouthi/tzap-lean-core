import Tzap.Semantics
import Tzap.Symbolic
import Tzap.Soundness
import Tzap.PhaseFolding
import Tzap.Affine

/-! # Algorithm 1: phase folding via parity analysis

The executable optimizer from the paper. It walks the circuit once, tracking
the symbolic state `σ` of `Tzap.Symbolic`. When it reaches `Rz θ q` whose
parity `σ(q)` recurs at a later `Rz`, the angle `θ` is forwarded into that
later gate; repeated forwarding leaves each merged group as a single `Rz` at
its last position, exactly as in the paper's Algorithm 1.

The main result is `fold_correct : Equivalent (fold C) C`.

Contents and proof architecture:

* `mergeInto s p θ gs` — the single-merge primitive: scan the tail `gs`,
  updating the symbolic state as it goes, for the first `Rz φ q'` whose
  parity has the same canonical affine normal form (`Affine.normalize`) as
  `p`; replace it by `Rz (θ+φ) q'`. Comparing normal forms rather than raw
  parity syntax matches the paper's set membership test and lets the
  randomized algorithm agree with the exact one on faithful samples.
* `foldFrom` / `fold` — the pass itself; termination is by circuit length,
  justified by `mergeInto_length` (a merge rewrites one gate in place).
* `mergeInto_sound` — semantically, a successful merge multiplies every
  amplitude of the tail by exactly `phase θ (p.eval v)`; this is the phase
  that the deleted `Rz θ q` would have contributed, since consistency gives
  `x q = (s.qubit q).eval v`.
* `foldFrom_sound` / `fold_correct` — the induction over the pass, threading
  consistency through intermediate gates with
  `Soundness.step_preserves_consistency`, concluding that the output circuit
  denotes exactly the same weighted relation as the input.
-/

namespace Tzap.Algorithm

open Tzap.Symbolic Tzap.Semantics Tzap.Soundness

noncomputable section

/--
Add `θ` into the first later `Rz` gate whose parity under the evolving
symbolic state `s` equals `p` as a canonical affine form (`Affine.normalize`).
Non-`Rz` gates are passed over while stepping the symbolic state with the
transfer functions; `Rz` gates do not change the state. Returns `none` when
no matching rotation exists, in which case the caller keeps the original gate.
-/
def mergeInto {n : Nat} (s : State n) (p : Parity) (θ : ℝ) :
    Circuit n → Option (Circuit n)
  | [] => none
  | .rz φ q' :: gs =>
      if Affine.normalize (s.qubit q') = Affine.normalize p then
        some (.rz (θ + φ) q' :: gs)
      else (mergeInto s p θ gs).map (.rz φ q' :: ·)
  | g :: gs => (mergeInto (Symbolic.step s g) p θ gs).map (g :: ·)

/-- A successful merge rewrites one `Rz` angle in place, so it preserves the
length of the tail. This is the measure fact behind `foldFrom`'s termination. -/
theorem mergeInto_length {n : Nat} {p : Parity} {θ : ℝ} :
    ∀ {gs : Circuit n} {s : State n} {gs' : Circuit n},
      mergeInto s p θ gs = some gs' → gs'.length = gs.length := by
  intro gs
  induction gs with
  | nil => intro s gs' h; simp [mergeInto] at h
  | cons g gs ih =>
      intro s gs' h
      cases g with
      | rz φ q' =>
          simp only [mergeInto] at h
          split at h
          · cases h; rfl
          · rcases Option.map_eq_some_iff.mp h with ⟨rest', hrest, rfl⟩
            simp [ih hrest]
      | cnot c t =>
          rcases Option.map_eq_some_iff.mp h with ⟨rest', hrest, rfl⟩
          simp [ih hrest]
      | x t =>
          rcases Option.map_eq_some_iff.mp h with ⟨rest', hrest, rfl⟩
          simp [ih hrest]
      | hadamard t =>
          rcases Option.map_eq_some_iff.mp h with ⟨rest', hrest, rfl⟩
          simp [ih hrest]

set_option linter.unusedVariables false in
/--
Algorithm 1, from an arbitrary symbolic state. One left-to-right pass; at
each `Rz θ q` the angle is forwarded (via `mergeInto`) into the next `Rz`
with the same parity if one exists — dropping the current gate and recursing
on the rewritten tail — otherwise the gate is kept. All other gates are kept
and update the symbolic state via the transfer functions. Repeated forwarding
leaves each merged group as a single `Rz` at its last position. Terminates
because `mergeInto` preserves length, so the measure `C.length` decreases.
-/
def foldFrom {n : Nat} (s : State n) : Circuit n → Circuit n
  | [] => []
  | .rz θ q :: gs =>
      match h : mergeInto s (s.qubit q) θ gs with
      | some gs' => foldFrom s gs'
      | none => .rz θ q :: foldFrom s gs
  | g :: gs => g :: foldFrom (Symbolic.step s g) gs
  termination_by C => C.length
  decreasing_by
    · simp [mergeInto_length h]
    · simp
    · simp

/-- The optimizer: run Algorithm 1 from the initial symbolic state, in which
qubit `q` carries the parity `var q` and `n` variables are allocated. -/
def fold {n : Nat} (C : Circuit n) : Circuit n :=
  foldFrom (Symbolic.initial n) C

/--
The inductive step of merge soundness for a non-`Rz` head gate `g`: if the
tails satisfy the phase relation from every state reachable through `g`
(hypothesis `hIH`, quantified over the witness valuations produced by
`step_preserves_consistency`), the whole circuits satisfy it. The parity `p`
being bounded by `s.nextFresh` guarantees its evaluation is unchanged when
the valuation is extended at fresh Hadamard variables.
-/
theorem cons_phase_congr {n : Nat} (g : Gate n) (s : State n)
    (rest rest' : Circuit n) (θ : ℝ) (p : Parity)
    (v : Nat → Bool) (x z : Basis n)
    (hb : s.Bounded) (hpb : p.Bounded s.nextFresh) (hc : Consistent s v x)
    (hIH : ∀ (w : Nat → Bool) (y : Basis n),
      Consistent (Symbolic.step s g) w y →
      AgreeBelow s.nextFresh v w →
      Semantics.circuit rest' y z =
        phase θ (p.eval w) * Semantics.circuit rest y z) :
    Semantics.circuit (g :: rest') x z =
      phase θ (p.eval v) * Semantics.circuit (g :: rest) x z := by
  simp only [Semantics.circuit, WeightedRelation.comp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hgate : Semantics.gate g x y = 0
  · simp [hgate]
  · rcases step_preserves_consistency s g v x y hb hc hgate with ⟨w, hw, hagree⟩
    rw [hIH w y hw hagree,
      Parity.eval_eq_of_agree hpb (fun i hi => hagree i hi)]
    ring

/-!
## MAIN THEOREM: mergeInto_sound

**Statement.** Suppose `mergeInto s p θ gs = some gs'`, i.e. the merge found
a later `Rz φ q'` whose parity normalizes to the same affine form as `p` and
added `θ` to it. Then for every valuation `v` consistent with the bounded
symbolic state `s` on the input `x` (with `p` bounded by `s.nextFresh`), and
for every output `z`, the rewritten tail's amplitude is exactly
`phase θ (p.eval v) * Semantics.circuit gs x z`. Since consistency makes
`p.eval v` the concrete bit the deleted `Rz θ q` would have seen, this factor
is precisely the phase that gate would have contributed.

**Significance.** This is the semantic content of one forward step of
Algorithm 1: `foldFrom_sound` cancels this factor against the dropped
rotation via `phase_add`, giving exact preservation of amplitudes.
-/

/--
Soundness of a single forward merge: adding `θ` into the next `Rz` with
parity `p` multiplies every amplitude of the tail by `phase θ (p.eval v)`,
for any valuation `v` consistent with the symbolic state at that point.
By induction on the tail: at the matched `Rz` the equal normal forms give
equal bits (`Affine.bit_injective`) and the phases combine by `phase_add`;
non-`Rz` gates are handled by `cons_phase_congr`.
-/
theorem mergeInto_sound {n : Nat} {p : Parity} {θ : ℝ} :
    ∀ (gs : Circuit n) (s : State n) (gs' : Circuit n)
      (v : Nat → Bool) (x z : Basis n),
      s.Bounded → p.Bounded s.nextFresh → Consistent s v x →
      mergeInto s p θ gs = some gs' →
      Semantics.circuit gs' x z =
        phase θ (p.eval v) * Semantics.circuit gs x z := by
  intro gs
  induction gs with
  | nil => intro s gs' v x z _ _ _ h; simp [mergeInto] at h
  | cons g gs ih =>
      intro s gs' v x z hb hpb hc h
      cases g with
      | rz φ q' =>
          simp only [mergeInto] at h
          split at h
          · -- matched: gs' = rz (θ + φ) q' :: gs
            next hpq =>
              cases h
              rw [Semantics.rz_cons_apply, Semantics.rz_cons_apply]
              have heval : (s.qubit q').eval v = p.eval v := by
                apply Affine.bit_injective
                rw [← Affine.normalize_eval, ← Affine.normalize_eval, hpq]
              have hxq : x q' = p.eval v := by rw [← hc q', heval]
              rw [hxq, ← Semantics.phase_add]
              ring
          · rcases Option.map_eq_some_iff.mp h with ⟨rest', hrest, rfl⟩
            rw [Semantics.rz_cons_apply, Semantics.rz_cons_apply,
              ih s rest' v x z hb hpb hc hrest]
            ring
      | cnot c t =>
          rcases Option.map_eq_some_iff.mp h with ⟨rest', hrest, rfl⟩
          exact cons_phase_congr _ s gs rest' θ p v x z hb hpb hc
            (fun w y hw hagree => ih (Symbolic.step s (.cnot c t)) rest' w y z
              (Symbolic.step_bounded s _ hb)
              (Parity.bounded_mono hpb (step_nextFresh_mono s _)) hw hrest)
      | x t =>
          rcases Option.map_eq_some_iff.mp h with ⟨rest', hrest, rfl⟩
          exact cons_phase_congr _ s gs rest' θ p v x z hb hpb hc
            (fun w y hw hagree => ih (Symbolic.step s (.x t)) rest' w y z
              (Symbolic.step_bounded s _ hb)
              (Parity.bounded_mono hpb (step_nextFresh_mono s _)) hw hrest)
      | hadamard t =>
          rcases Option.map_eq_some_iff.mp h with ⟨rest', hrest, rfl⟩
          exact cons_phase_congr _ s gs rest' θ p v x z hb hpb hc
            (fun w y hw hagree => ih (Symbolic.step s (.hadamard t)) rest' w y z
              (Symbolic.step_bounded s _ hb)
              (Parity.bounded_mono hpb (step_nextFresh_mono s _)) hw hrest)

/-!
## MAIN THEOREM: foldFrom_sound

**Statement.** Let `s` be any bounded symbolic state and `v` a valuation
consistent with `s` on the input basis state `x`. Then the pass started at
`s` preserves every amplitude: `Semantics.circuit (foldFrom s C) x z =
Semantics.circuit C x z` for all outputs `z`. The hypotheses say precisely
that `s` is a sound description of how the bits at `x` arise from the
symbolic variables, which is what justifies each merge decision made during
the pass.

**Significance.** This is the working induction behind `fold_correct`,
stated relative to an arbitrary mid-circuit state so that the induction
hypothesis applies after each gate; it combines `mergeInto_sound` (for the
merge branch) with `step_preserves_consistency` (to thread consistency
through kept gates).
-/

/--
Relative correctness of Algorithm 1: from any bounded symbolic state and any
input basis state consistent with it, the folded circuit has exactly the same
amplitudes as the original. Induction follows the recursion of `foldFrom`;
in the merge branch the factor `phase θ (p.eval v)` from `mergeInto_sound`
is exactly the phase of the dropped `Rz`.
-/
theorem foldFrom_sound {n : Nat} (C : Circuit n) (s : State n)
    (v : Nat → Bool) (x z : Basis n)
    (hb : s.Bounded) (hc : Consistent s v x) :
    Semantics.circuit (foldFrom s C) x z = Semantics.circuit C x z := by
  induction s, C using foldFrom.induct generalizing v x with
  | case1 s => rw [foldFrom]
  | case2 s θ q gs gs' hmerge ih =>
      rw [foldFrom, hmerge]
      rw [ih v x hb hc,
        mergeInto_sound gs s gs' v x z hb (hb q) hc hmerge,
        Semantics.rz_cons_apply, hc q]
  | case3 s θ q gs hmerge ih =>
      rw [foldFrom, hmerge]
      rw [Semantics.rz_cons_apply, Semantics.rz_cons_apply, ih v x hb hc]
  | case4 s g gs hnotrz ih =>
      rw [foldFrom.eq_def]
      cases g with
      | rz θ q => exact absurd rfl (hnotrz θ q)
      | cnot c t =>
          simp only [Semantics.circuit, WeightedRelation.comp]
          apply Finset.sum_congr rfl
          intro y _
          by_cases hgate : Semantics.gate (.cnot c t) x y = 0
          · simp [hgate]
          · rcases step_preserves_consistency s _ v x y hb hc hgate with
              ⟨w, hw, _⟩
            rw [ih w y (Symbolic.step_bounded s _ hb) hw]
      | x t =>
          simp only [Semantics.circuit, WeightedRelation.comp]
          apply Finset.sum_congr rfl
          intro y _
          by_cases hgate : Semantics.gate (.x t) x y = 0
          · simp [hgate]
          · rcases step_preserves_consistency s _ v x y hb hc hgate with
              ⟨w, hw, _⟩
            rw [ih w y (Symbolic.step_bounded s _ hb) hw]
      | hadamard t =>
          simp only [Semantics.circuit, WeightedRelation.comp]
          apply Finset.sum_congr rfl
          intro y _
          by_cases hgate : Semantics.gate (.hadamard t) x y = 0
          · simp [hgate]
          · rcases step_preserves_consistency s _ v x y hb hc hgate with
              ⟨w, hw, _⟩
            rw [ih w y (Symbolic.step_bounded s _ hb) hw]

/-!
## MAIN THEOREM: fold_correct

**Statement.** For every circuit `C` on `n` qubits, the output of Algorithm 1
is semantically EQUAL to its input as a weighted relation:
`Semantics.circuit (fold C) = Semantics.circuit C`. Every complex amplitude
between every pair of basis states is preserved exactly — not merely up to
global phase — with no hypotheses on `C`.

**Significance.** This is the headline correctness theorem for the exact
optimizer (the paper's `C' ≡ C`); the randomized variant's guarantee
(`RandomizedAlgorithm.randomized_fold_correct`) reduces to it on faithful
hash samples.
-/

/--
Correctness of Algorithm 1 (the paper's `C' ≡ C`): the optimized circuit is
semantically equal, as a weighted relation, to the input circuit. Immediate
from `foldFrom_sound` at the initial state with the canonical input
valuation (`initial_consistent`).
-/
theorem fold_correct {n : Nat} (C : Circuit n) :
    PhaseFolding.Equivalent (fold C) C := by
  funext x z
  exact foldFrom_sound C (Symbolic.initial n) (inputValuation x) x z
    (Symbolic.initial_bounded n) (initial_consistent x)

end
end Tzap.Algorithm
