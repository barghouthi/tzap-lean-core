import TZap.Soundness
import TZap.Collision

/-! # Soundness of the randomized (hash-based) parity analysis

This file connects three previously independent pieces:

* the *exact* soundness of the symbolic parity analysis against the complex
  circuit semantics (`TZap.Soundness.symbolic_soundness`),
* the correspondence between the randomized analysis and the symbolic one
  evaluated under an explicit draw stream (`TZap.Randomized`), and
* the affine collision bound for uniform `k`-bit hashing
  (`TZap.Collision.affine_collision_bound`).

The chain of reasoning: a semantic disagreement between qubit `q` of the input
and qubit `q'` of the output on some supported (nonzero-amplitude) transition
forces the two canonical affine parities to be *distinct*
(`semantic_disagreement_implies_normalize_ne`, via the exact soundness
theorem).  The randomized analysis reports the qubits equal exactly when the
hashes of those two affine forms coincide
(`random_event_iff_affine_event`), and distinct affine forms collide under a
uniform `k`-bit sample with probability at most `2⁻ᵏ`.  Composing gives the
main theorem `randomized_analysis_sound`.

Probabilities use Mathlib's `PMF.uniformOfFintype` and its outer measure on the
finite sample space `Sample m k = Fin m → Fin k → 𝔽₂`, where
`m = (analyze C).nextFresh` counts the symbolic variables (initial qubit values
plus Hadamard-allocated fresh variables) that the hashes may mention.
-/

namespace TZap.RandomizedSoundness

open TZap.Symbolic
open TZap.Affine
open TZap.Randomized
open TZap.Collision
open TZap.FiniteProbability

noncomputable section

open scoped ENNReal

/-! ## Bookkeeping: the fresh-variable counter only grows

The sample space is indexed by `(analyze C).nextFresh`, so every parity the
analysis ever produces must be bounded by that counter.  These two lemmas
record the monotonicity facts that make the boundedness arguments go through.
-/

/-- Running the analysis never decreases the fresh-variable counter: each gate
either leaves it unchanged or (for `H`) allocates one new variable. -/
theorem analyzeFrom_nextFresh_mono {n} (s : Symbolic.State n) (C : Circuit n) :
    s.nextFresh ≤ (Symbolic.analyzeFrom s C).nextFresh := by
  induction C generalizing s with
  | nil => rfl
  | cons g C ih =>
      exact (Soundness.step_nextFresh_mono s g).trans (ih (Symbolic.step s g))

/-- The final counter is at least `n`: the initial state already allocates one
variable per qubit, and the counter never decreases. -/
theorem analyze_nextFresh_ge_qubits {n} (C : Circuit n) :
    n ≤ (Symbolic.analyze C).nextFresh :=
  analyzeFrom_nextFresh_mono (Symbolic.initial n) C

/-! ## From semantic disagreement to distinct affine forms -/

/-- A semantic counterexample makes the corresponding canonical parities
distinct.  If some transition `x ↦ x'` with nonzero amplitude has
`x q ≠ x' q'`, then the canonical affine form of qubit `q` in the initial
symbolic state differs from that of qubit `q'` after analyzing `C`.  The proof
uses the exact soundness theorem to produce a valuation realizing `(x, x')`,
on which the two parities evaluate differently — so their normal forms cannot
be equal. -/
theorem semantic_disagreement_implies_normalize_ne {n} (C : Circuit n)
    (q q' : Fin n) (x x' : Basis n)
    (hsupport : Semantics.circuit C x x' ≠ 0) (hne : x q ≠ x' q') :
    Affine.normalize ((Symbolic.initial n).qubit q) ≠
      Affine.normalize ((Symbolic.analyze C).qubit q') := by
  rcases Soundness.symbolic_soundness C x x' hsupport with
    ⟨valuation, hout, hin⟩
  apply Affine.normalize_ne_of_eval_ne (valuation := valuation)
  simpa [Symbolic.initial, hin q, hout q'] using hne

/-- The canonical form of an initial-state qubit parity (the single variable
`q`) mentions only variables below the final counter. -/
theorem initial_normalize_bounded {n} (C : Circuit n) (q : Fin n) :
    Affine.Bounded (Symbolic.analyze C).nextFresh
      (Affine.normalize ((Symbolic.initial n).qubit q)) := by
  apply Affine.normalize_bounded
  exact Nat.lt_of_lt_of_le q.isLt (analyze_nextFresh_ge_qubits C)

/-- The canonical form of an output qubit parity mentions only variables below
the final counter (the analysis maintains this invariant). -/
theorem output_normalize_bounded {n} (C : Circuit n) (q : Fin n) :
    Affine.Bounded (Symbolic.analyze C).nextFresh
      (Affine.normalize ((Symbolic.analyze C).qubit q)) :=
  Affine.normalize_bounded (Symbolic.analyze_bounded C q)

/-! ## The randomized event is exactly a hash collision -/

/-- For every fixed sample, the randomized analysis reports the two qubits
equal exactly when the `k`-bit hashes of the corresponding canonical affine
forms coincide.  This rewrites the algorithmic event into the form to which
the collision bound applies; it uses `analyze_correspond` (the randomized
analysis is the symbolic analysis evaluated under the draws) and the fact that
hashing factors through normalization. -/
theorem random_event_iff_affine_event {n k} (C : Circuit n) (q q' : Fin n)
    (sample : Sample (Symbolic.analyze C).nextFresh k) :
    (Randomized.initial (liftSample sample) n).qubit q =
        (Randomized.analyze (liftSample sample) C).qubit q' ↔
      Collision.output (Affine.normalize ((Symbolic.initial n).qubit q)) sample =
        Collision.output (Affine.normalize ((Symbolic.analyze C).qubit q')) sample := by
  rw [Randomized.analyze_qubit_eq_evalBits]
  change liftSample sample q.val =
      evalBits (liftSample sample) ((Symbolic.analyze C).qubit q') ↔
    evalBits (liftSample sample) ((Symbolic.initial n).qubit q) =
      evalBits (liftSample sample) ((Symbolic.analyze C).qubit q')
  simp [Symbolic.initial]

/-!
## MAIN THEOREM: Soundness of the randomized analysis

**Statement.** Fix a circuit `C` on `n` qubits, an input qubit `q`, and an
output qubit `q'`.  Suppose the two genuinely disagree: there is a transition
`x ↦ x'` of `C` with nonzero amplitude for which the input bit `x q` differs
from the output bit `x' q'`.  Then the probability — over a uniformly random
sample assigning a `k`-bit string to each of the `(analyze C).nextFresh`
symbolic variables — that the randomized analysis nevertheless assigns qubit
`q` (in the initial state) and qubit `q'` (after analyzing `C`) the *same*
hash is at most `(1/2)^k`.  The probability is an exact rational computed by
counting over the finite sample space.

**Significance.** This is the randomized counterpart of the paper's soundness
theorem: a hash equality reported by the `k`-bit analysis is wrong with
probability at most `2⁻ᵏ`.  It is the single-query bound that the phase-folding
and whole-algorithm guarantees amplify by union bounds.
-/

/--
Soundness of the randomized analysis with respect to the exact complex circuit
semantics. If some supported transition disagrees at the queried qubits, a
false randomized equality occurs with probability at most `2⁻ᵏ`.
-/
theorem randomized_analysis_sound {n k : Nat} (C : Circuit n) (q q' : Fin n)
    (hdisagree : ∃ x x' : Basis n,
      Semantics.circuit C x x' ≠ 0 ∧ x q ≠ x' q') :
    (PMF.uniformOfFintype (Sample (Symbolic.analyze C).nextFresh k)).toOuterMeasure
        {sample |
          (Randomized.initial (liftSample sample) n).qubit q =
            (Randomized.analyze (liftSample sample) C).qubit q'} ≤
      ((2 : ℝ≥0∞)⁻¹) ^ k := by
  rcases hdisagree with ⟨x, x', hsupport, hne⟩
  let p := Affine.normalize ((Symbolic.initial n).qubit q)
  let p' := Affine.normalize ((Symbolic.analyze C).qubit q')
  have hp : Affine.Bounded (Symbolic.analyze C).nextFresh p :=
    initial_normalize_bounded C q
  have hp' : Affine.Bounded (Symbolic.analyze C).nextFresh p' :=
    output_normalize_bounded C q'
  have hpp' : p ≠ p' :=
    semantic_disagreement_implies_normalize_ne C q q' x x' hsupport hne
  have hevent :
      {sample : Sample (Symbolic.analyze C).nextFresh k |
        (Randomized.initial (liftSample sample) n).qubit q =
          (Randomized.analyze (liftSample sample) C).qubit q'} =
      {sample | Collision.output p sample = Collision.output p' sample} := by
    ext sample
    exact random_event_iff_affine_event C q q' sample
  rw [hevent]
  exact affine_collision_bound p p' hp hp' hpp'

end
end TZap.RandomizedSoundness
