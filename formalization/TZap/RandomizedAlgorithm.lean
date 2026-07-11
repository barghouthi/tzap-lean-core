import TZap.Algorithm
import TZap.RandomizedSoundness

/-! # Randomized Algorithm 1: phase folding with hashed parities

The randomized variant of Algorithm 1 (`TZap.Algorithm.fold`): instead of
canonical affine parities, each qubit carries a `k`-bit hash (the randomized
analysis of `TZap.Randomized`), and merge decisions compare hashes.

The development follows the paper:
* Whenever the sample is *faithful* — no two distinct parities compared by the
  algorithm collide under the hash — the randomized run coincides gate-for-gate
  with the exact algorithm (`foldFromR_eq_foldFrom`), hence its output is
  equivalent to the input circuit (`foldR_correct_of_faithful`).
* A union bound over the `t` parities at rotation sites (`t` = number of `Rz`
  gates) bounds the probability of an unfaithful sample by `C(t,2) · 2⁻ᵏ`
  (`collides_probability_le`), yielding the headline theorem
  `randomized_fold_correct`: the randomized optimizer returns a non-equivalent
  circuit with probability at most `C(t,2) · 2⁻ᵏ`.

Key notions used throughout:

* `Sample m k = Fin m → Fin k → 𝔽₂`: the finite uniform sample space — one
  `k`-bit string per symbolic variable, sampled via Mathlib's
  `PMF.uniformOfFintype`; event probabilities are `ℝ≥0∞` outer-measure masses.
* `rzParities C`: the symbolic parities at the rotation sites of `C` — the
  only values the algorithm ever compares, so faithfulness need only be
  demanded on this finite list.
* `Faithful draws P`: hash equality implies canonical-form equality on `P`.
* `Collides P sample`: the bad event — two parities in `P` with distinct
  canonical forms nevertheless hash equal under `sample`.
-/

namespace TZap.RandomizedAlgorithm

open TZap.Symbolic TZap.Affine TZap.Randomized TZap.Collision
open TZap.FiniteProbability TZap.Algorithm

attribute [local instance] Classical.propDecidable

noncomputable section

open scoped ENNReal

/-! ## The randomized optimizer

The definitions mirror `Algorithm.mergeInto` / `foldFrom` / `fold` exactly;
the only change is the state: a `Randomized.State n k` carries a `k`-bit hash
per qubit instead of a symbolic parity, and the merge test compares hashes
(`s.qubit q' = p`) instead of canonical affine forms.
-/

/-- Randomized merge: forward `θ` into the first later `Rz` whose *hashed*
parity equals the hash `p`.  Returns `some` of the rewritten tail (with the
target angle bumped to `θ + φ`) if such an `Rz` exists before the end of the
circuit, `none` otherwise.  The hash state is stepped through intervening
gates just as the symbolic state is in `Algorithm.mergeInto`. -/
def mergeIntoR {n k : Nat} (draws : Draws k) (s : Randomized.State n k)
    (p : BitString k) (θ : ℝ) : Circuit n → Option (Circuit n)
  | [] => none
  | .rz φ q' :: gs =>
      if s.qubit q' = p then some (.rz (θ + φ) q' :: gs)
      else (mergeIntoR draws s p θ gs).map (.rz φ q' :: ·)
  | g :: gs => (mergeIntoR draws (Randomized.step draws s g) p θ gs).map (g :: ·)

/-- A successful randomized merge preserves the length of the tail (one gate
is rewritten in place, none added or removed) — this justifies termination of
`foldFromR` by circuit length. -/
theorem mergeIntoR_length {n k : Nat} {draws : Draws k} {p : BitString k}
    {θ : ℝ} :
    ∀ {gs : Circuit n} {s : Randomized.State n k} {gs' : Circuit n},
      mergeIntoR draws s p θ gs = some gs' → gs'.length = gs.length := by
  intro gs
  induction gs with
  | nil => intro s gs' h; simp [mergeIntoR] at h
  | cons g gs ih =>
      intro s gs' h
      cases g with
      | rz φ q' =>
          simp only [mergeIntoR] at h
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
/-- Randomized Algorithm 1: the single pass of `Algorithm.foldFrom`, with the
randomized analysis state and hash comparisons in place of exact parities.
Each `Rz θ q` either forwards its angle into the first later `Rz` carrying the
same hash (and the pass restarts on the rewritten tail, which is strictly
shorter than the original `Rz`-headed circuit) or is kept; other gates step
the hash state and are copied unchanged. -/
def foldFromR {n k : Nat} (draws : Draws k) (s : Randomized.State n k) :
    Circuit n → Circuit n
  | [] => []
  | .rz θ q :: gs =>
      match h : mergeIntoR draws s (s.qubit q) θ gs with
      | some gs' => foldFromR draws s gs'
      | none => .rz θ q :: foldFromR draws s gs
  | g :: gs => g :: foldFromR draws (Randomized.step draws s g) gs
  termination_by C => C.length
  decreasing_by
    · simp [mergeIntoR_length h]
    · simp
    · simp

/-- The randomized optimizer: run the single pass from the initial hash state
(each qubit hashed to its own variable's draw).  This is the function whose
output distribution `randomized_fold_correct` bounds. -/
def foldR {n k : Nat} (draws : Draws k) (C : Circuit n) : Circuit n :=
  foldFromR draws (Randomized.initial draws n) C

/-! ## The parities compared by the algorithm -/

/-- The symbolic parities at the rotation sites of a circuit — exactly the
parities Algorithm 1 ever compares.  Starting from state `s`, each `Rz _ q`
contributes the current parity of `q`; other gates only step the state.
(`Rz` does not change the symbolic state, so the traversal for `Rz` reuses
`s`.) -/
def rzParitiesFrom {n : Nat} (s : Symbolic.State n) : Circuit n → List Parity
  | [] => []
  | .rz _ q :: gs => s.qubit q :: rzParitiesFrom s gs
  | g :: gs => rzParitiesFrom (Symbolic.step s g) gs

/-- The rotation-site parities of `C` from the initial state.  Its length is
the number `t` of `Rz` gates in `C` — the `t` in the headline `C(t,2) · 2⁻ᵏ`
bound. -/
def rzParities {n : Nat} (C : Circuit n) : List Parity :=
  rzParitiesFrom (Symbolic.initial n) C

/-- A draw stream is faithful to a set of parities when hash equality implies
equality of canonical affine forms on it.  On a faithful stream the hash test
`evalBits draws p = evalBits draws p'` is *equivalent* to canonical-form
equality (the converse direction is `evalBits_congr`), so the randomized and
exact algorithms decide every merge identically. -/
def Faithful {k : Nat} (draws : Draws k) (P : List Parity) : Prop :=
  ∀ p ∈ P, ∀ p' ∈ P,
    evalBits draws p = evalBits draws p' →
    Affine.normalize p = Affine.normalize p'

/-- Faithfulness is monotone: a stream faithful to `Q` is faithful to any
sublist `P` — used to pass faithfulness to circuit tails during induction. -/
theorem Faithful.of_subset {k : Nat} {draws : Draws k} {P Q : List Parity}
    (h : Faithful draws Q) (hsub : ∀ p ∈ P, p ∈ Q) : Faithful draws P :=
  fun p hp p' hp' => h p (hsub p hp) p' (hsub p' hp')

/-- Hashing factors through normalization, so equal forms always hash equal. -/
theorem evalBits_congr {k : Nat} (draws : Draws k) {p p' : Parity}
    (h : Affine.normalize p = Affine.normalize p') :
    evalBits draws p = evalBits draws p' := by
  funext j
  simp [evalBits, h]

/-- Merging into the tail leaves the rotation-site parities unchanged: the
exact merge only alters one `Rz` *angle*, never a qubit index or the gate
sequence's effect on the symbolic state.  Hence faithfulness survives a
merge, which case 2 of `foldFromR_eq_foldFrom` needs to recurse. -/
theorem rzParitiesFrom_mergeInto {n : Nat} {p : Parity} {θ : ℝ} :
    ∀ {gs : Circuit n} {s : Symbolic.State n} {gs' : Circuit n},
      Algorithm.mergeInto s p θ gs = some gs' →
      rzParitiesFrom s gs' = rzParitiesFrom s gs := by
  intro gs
  induction gs with
  | nil => intro s gs' h; simp [Algorithm.mergeInto] at h
  | cons g gs ih =>
      intro s gs' h
      cases g with
      | rz φ q' =>
          simp only [Algorithm.mergeInto] at h
          split at h
          · cases h; rfl
          · rcases Option.map_eq_some_iff.mp h with ⟨rest', hrest, rfl⟩
            simp [rzParitiesFrom, ih hrest]
      | cnot c t =>
          rcases Option.map_eq_some_iff.mp h with ⟨rest', hrest, rfl⟩
          simp [rzParitiesFrom, ih hrest]
      | x t =>
          rcases Option.map_eq_some_iff.mp h with ⟨rest', hrest, rfl⟩
          simp [rzParitiesFrom, ih hrest]
      | hadamard t =>
          rcases Option.map_eq_some_iff.mp h with ⟨rest', hrest, rfl⟩
          simp [rzParitiesFrom, ih hrest]

/-! ## Agreement with the exact algorithm on faithful samples -/

/-- On a faithful draw stream, the randomized merge makes exactly the same
decision as the exact merge.  `Correspond draws rs s` says the hash state `rs`
is the symbolic state `s` evaluated under `draws`; the hypothesis on
`rzParitiesFrom s gs` is exactly the faithfulness needed for the encountered
comparisons.  If normal forms are equal the hashes agree by `evalBits_congr`;
if they differ, faithfulness rules out a spurious hash match. -/
theorem mergeIntoR_eq_mergeInto {n k : Nat} (draws : Draws k) {θ : ℝ} :
    ∀ (gs : Circuit n) (s : Symbolic.State n) (rs : Randomized.State n k)
      (p : Parity),
      Correspond draws rs s →
      (∀ p' ∈ rzParitiesFrom s gs,
        evalBits draws p' = evalBits draws p →
        Affine.normalize p' = Affine.normalize p) →
      mergeIntoR draws rs (evalBits draws p) θ gs =
        Algorithm.mergeInto s p θ gs := by
  intro gs
  induction gs with
  | nil => intro s rs p _ _; rfl
  | cons g gs ih =>
      intro s rs p hcorr hf
      cases g with
      | rz φ q' =>
          have hq' : rs.qubit q' = evalBits draws (s.qubit q') := hcorr.2 q'
          have hhead : s.qubit q' ∈ rzParitiesFrom s (.rz φ q' :: gs) := by
            simp [rzParitiesFrom]
          simp only [mergeIntoR, Algorithm.mergeInto]
          by_cases hnorm : Affine.normalize (s.qubit q') = Affine.normalize p
          · rw [if_pos (by rw [hq', evalBits_congr draws hnorm]), if_pos hnorm]
          · rw [if_neg (fun heq => hnorm
                (hf (s.qubit q') hhead (by rw [← hq', heq]))),
              if_neg hnorm,
              ih s rs p hcorr (fun p' hp' => hf p' (by simp [rzParitiesFrom, hp']))]
      | cnot c t =>
          simp only [mergeIntoR, Algorithm.mergeInto]
          rw [ih (Symbolic.step s (.cnot c t)) (Randomized.step draws rs (.cnot c t)) p
            (step_correspond draws rs s _ hcorr)
            (fun p' hp' => hf p' (by simpa [rzParitiesFrom] using hp'))]
      | x t =>
          simp only [mergeIntoR, Algorithm.mergeInto]
          rw [ih (Symbolic.step s (.x t)) (Randomized.step draws rs (.x t)) p
            (step_correspond draws rs s _ hcorr)
            (fun p' hp' => hf p' (by simpa [rzParitiesFrom] using hp'))]
      | hadamard t =>
          simp only [mergeIntoR, Algorithm.mergeInto]
          rw [ih (Symbolic.step s (.hadamard t)) (Randomized.step draws rs (.hadamard t)) p
            (step_correspond draws rs s _ hcorr)
            (fun p' hp' => hf p' (by simpa [rzParitiesFrom] using hp'))]

/-!
## MAIN THEOREM: The randomized pass equals the exact pass on faithful samples

**Statement.** Fix a draw stream and a symbolic state `s`, and let `rs` be
the corresponding hash state (`Correspond draws rs s`).  If the stream is
faithful to the rotation-site parities of `C` from `s` — no two compared
parities with distinct canonical forms hash equal — then the randomized pass
and the exact pass produce *identical* output circuits:
`foldFromR draws rs C = Algorithm.foldFrom s C`.  This is a deterministic,
gate-for-gate statement; no probability is involved.

**Significance.** It reduces correctness of the randomized optimizer to
(a) correctness of the exact one (`Algorithm.fold_correct`) and (b) the
probability of an unfaithful sample — the derandomization step of the paper's
argument.
-/

/-- On a faithful draw stream, the randomized pass returns exactly the output
of the exact Algorithm 1.  Induction over the recursion structure of
`Algorithm.foldFrom`; each merge decision agrees by `mergeIntoR_eq_mergeInto`,
and faithfulness is passed to the (possibly rewritten) tail via
`Faithful.of_subset` and `rzParitiesFrom_mergeInto`. -/
theorem foldFromR_eq_foldFrom {n k : Nat} (draws : Draws k) (C : Circuit n)
    (s : Symbolic.State n) :
    ∀ (rs : Randomized.State n k), Correspond draws rs s →
      Faithful draws (rzParitiesFrom s C) →
      foldFromR draws rs C = Algorithm.foldFrom s C := by
  induction s, C using Algorithm.foldFrom.induct with
  | case1 s =>
      intro rs _ _
      rw [foldFromR, Algorithm.foldFrom]
  | case2 s θ q gs gs' hmerge ih =>
      intro rs hcorr hf
      have hhead : s.qubit q ∈ rzParitiesFrom s (.rz θ q :: gs) := by
        simp [rzParitiesFrom]
      have htail : ∀ p' ∈ rzParitiesFrom s gs,
          p' ∈ rzParitiesFrom s (.rz θ q :: gs) := by
        intro p' hp'
        simp [rzParitiesFrom, hp']
      have hR : mergeIntoR draws rs (rs.qubit q) θ gs = some gs' := by
        rw [hcorr.2 q,
          mergeIntoR_eq_mergeInto draws gs s rs (s.qubit q) hcorr
            (fun p' hp' => hf p' (htail p' hp') (s.qubit q) hhead)]
        exact hmerge
      rw [foldFromR, hR, Algorithm.foldFrom, hmerge]
      exact ih rs hcorr
        ((hf.of_subset htail).of_subset
          (fun p' hp' => by rwa [rzParitiesFrom_mergeInto hmerge] at hp'))
  | case3 s θ q gs hmerge ih =>
      intro rs hcorr hf
      have hhead : s.qubit q ∈ rzParitiesFrom s (.rz θ q :: gs) := by
        simp [rzParitiesFrom]
      have htail : ∀ p' ∈ rzParitiesFrom s gs,
          p' ∈ rzParitiesFrom s (.rz θ q :: gs) := by
        intro p' hp'
        simp [rzParitiesFrom, hp']
      have hR : mergeIntoR draws rs (rs.qubit q) θ gs = none := by
        rw [hcorr.2 q,
          mergeIntoR_eq_mergeInto draws gs s rs (s.qubit q) hcorr
            (fun p' hp' => hf p' (htail p' hp') (s.qubit q) hhead)]
        exact hmerge
      rw [foldFromR, hR, Algorithm.foldFrom, hmerge]
      rw [ih rs hcorr (hf.of_subset htail)]
  | case4 s g gs hnotrz ih =>
      intro rs hcorr hf
      rw [foldFromR.eq_def, Algorithm.foldFrom.eq_def]
      cases g with
      | rz θ q => exact absurd rfl (hnotrz θ q)
      | cnot c t =>
          simp only
          rw [ih (Randomized.step draws rs _) (step_correspond draws rs s _ hcorr)
            (hf.of_subset (fun p' hp' => by simpa [rzParitiesFrom] using hp'))]
      | x t =>
          simp only
          rw [ih (Randomized.step draws rs _) (step_correspond draws rs s _ hcorr)
            (hf.of_subset (fun p' hp' => by simpa [rzParitiesFrom] using hp'))]
      | hadamard t =>
          simp only
          rw [ih (Randomized.step draws rs _) (step_correspond draws rs s _ hcorr)
            (hf.of_subset (fun p' hp' => by simpa [rzParitiesFrom] using hp'))]

/-!
## MAIN THEOREM: Conditional correctness of the randomized optimizer

**Statement.** If the draw stream is faithful to `rzParities C` — hash
equality implies canonical-form equality on the finitely many parities the
algorithm compares — then the output of the randomized optimizer is
semantically equivalent to the input: `⟦foldR draws C⟧ = ⟦C⟧` as weighted
relations.  Deterministic, given the faithfulness hypothesis.

**Significance.** Together with the bound on unfaithful samples
(`collides_probability_le`), this yields the headline probabilistic guarantee:
the randomized algorithm can only err on the rare bad event.
-/

/-- Conditional correctness: on a faithful draw stream the randomized
optimizer is exact (`foldFromR_eq_foldFrom`), hence its output is equivalent
to the input circuit by the exact `Algorithm.fold_correct`. -/
theorem foldR_correct_of_faithful {n k : Nat} (draws : Draws k) (C : Circuit n)
    (h : Faithful draws (rzParities C)) :
    PhaseFolding.Equivalent (foldR draws C) C := by
  unfold foldR
  rw [foldFromR_eq_foldFrom draws C (Symbolic.initial n)
    (Randomized.initial draws n) (initial_correspond draws) h]
  exact Algorithm.fold_correct C

/-! ## The failure probability

It remains to bound the probability that a uniformly drawn sample is
unfaithful.  The bad event is a hash collision between some pair of compared
parities with distinct canonical forms; a union bound over the at most
`t × t` pairs, each with collision probability at most `2⁻ᵏ` by
`affine_collision_bound`, gives `C(t,2) · 2⁻ᵏ`.
-/

/-- All compared parities are bounded by the final fresh-variable counter of
the analysis — the boundedness hypothesis the collision bound needs, since the
sample only assigns bit strings to variables below that counter. -/
theorem rzParitiesFrom_bounded {n : Nat} :
    ∀ (gs : Circuit n) (s : Symbolic.State n), s.Bounded →
      ∀ p ∈ rzParitiesFrom s gs,
        p.Bounded (Symbolic.analyzeFrom s gs).nextFresh := by
  intro gs
  induction gs with
  | nil => intro s _ p hp; simp [rzParitiesFrom] at hp
  | cons g gs ih =>
      intro s hb p hp
      cases g with
      | rz θ q =>
          simp only [rzParitiesFrom, List.mem_cons] at hp
          have hstate : Symbolic.analyzeFrom s (.rz θ q :: gs) =
              Symbolic.analyzeFrom s gs := rfl
          rw [hstate]
          rcases hp with rfl | hp
          · exact Parity.bounded_mono (hb q)
              (RandomizedSoundness.analyzeFrom_nextFresh_mono s gs)
          · exact ih s hb p hp
      | cnot c t =>
          exact ih _ (Symbolic.step_bounded s _ hb) p hp
      | x t =>
          exact ih _ (Symbolic.step_bounded s _ hb) p hp
      | hadamard t =>
          exact ih _ (Symbolic.step_bounded s _ hb) p hp

/-- Specialization of `rzParitiesFrom_bounded` to the initial state: every
parity compared on circuit `C` is bounded by `(analyze C).nextFresh`. -/
theorem rzParities_bounded {n : Nat} (C : Circuit n) :
    ∀ p ∈ rzParities C, p.Bounded (Symbolic.analyze C).nextFresh :=
  rzParitiesFrom_bounded C (Symbolic.initial n) (Symbolic.initial_bounded n)

/-- The bad event: two compared parities with distinct canonical forms receive
the same hash under the sample.  `¬ Collides P sample` is exactly
`Faithful (liftSample sample) P` (see `faithful_of_not_collides`), phrased in
terms of `Collision.output` so the collision bound applies directly. -/
def Collides {m k : Nat} (P : List Parity) (sample : Sample m k) : Prop :=
  ∃ p ∈ P, ∃ p' ∈ P,
    Affine.normalize p ≠ Affine.normalize p' ∧
    Collision.output (Affine.normalize p) sample =
      Collision.output (Affine.normalize p') sample

/-- No collision on the compared parities means the sample is faithful —
the bridge from the probabilistic bad event back to the hypothesis of
`foldR_correct_of_faithful`. -/
theorem faithful_of_not_collides {m k : Nat} {P : List Parity}
    {sample : Sample m k} (h : ¬ Collides P sample) :
    Faithful (liftSample sample) P := by
  intro p hp p' hp' heval
  by_contra hne
  exact h ⟨p, hp, p', hp', hne, heval⟩

/-!
## MAIN THEOREM: The union bound on unfaithful samples

**Statement.** Let `P` be any list of parities, all bounded by the number `m`
of hashed variables.  Then the probability — over a uniform sample
`Sample m k` — that some pair of parities in `P` with *distinct* canonical
affine forms nevertheless hashes equal (`Collides P sample`) is at most
`C(|P|,2) · (1/2)^k`.  The collision event is symmetric in the pair, so a
witnessing pair can always be reordered to a pair of list indices `j < i`;
the union bound then runs over the `C(|P|,2)` such index pairs, and each pair
is bounded by the affine collision bound (pairs with equal normal forms
contribute probability zero).

**Significance.** Instantiated with `P = rzParities C` (so `|P| = t`, the
number of `Rz` gates), this bounds the probability that the randomized
optimizer's run differs from the exact one, giving the binomial factor
`C(t,2)` in the headline theorem — matching the paper's union bound over
unordered pairs of rotations.
-/

/-- Union bound over unordered pairs of compared parities: an unfaithful
sample occurs with probability at most `C(|P|,2) · 2⁻ᵏ`. -/
theorem collides_probability_le {m k : Nat} (P : List Parity)
    (hP : ∀ p ∈ P, Parity.Bounded m p) :
    (PMF.uniformOfFintype (Sample m k)).toOuterMeasure
        {sample | Collides P sample} ≤
      (P.length.choose 2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ k := by
  classical
  let μ := (PMF.uniformOfFintype (Sample m k)).toOuterMeasure
  -- Total function reading the `i`-th compared parity (junk beyond the end).
  let get : Nat → Parity := fun i => P.getD i (.const false)
  -- The collision event for the index pair `(i, j)`.
  let E : Nat → Nat → Set (Sample m k) := fun i j =>
    {sample |
      Affine.normalize (get i) ≠ Affine.normalize (get j) ∧
      Collision.output (Affine.normalize (get i)) sample =
        Collision.output (Affine.normalize (get j)) sample}
  have hgetD : ∀ i (h : i < P.length), get i = P[i] := fun i h => by
    simp [get, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  -- Any collision is witnessed at a pair of indices `j < i` — the event is
  -- symmetric, so an out-of-order witness can be swapped.
  have hsub : {sample : Sample m k | Collides P sample} ⊆
      ⋃ i ∈ Finset.range P.length, ⋃ j ∈ Finset.range i, E i j := by
    rintro sample ⟨p, hp, p', hp', hne, hout⟩
    rcases List.mem_iff_getElem.mp hp with ⟨i, hi, hpi⟩
    rcases List.mem_iff_getElem.mp hp' with ⟨j, hj, hpj⟩
    have hgi : get i = p := (hgetD i hi).trans hpi
    have hgj : get j = p' := (hgetD j hj).trans hpj
    have hij : i ≠ j := by
      rintro rfl
      exact hne (congrArg Affine.normalize (hpi.symm.trans hpj))
    rcases Nat.lt_or_ge i j with hlt | hge
    · refine Set.mem_biUnion (Finset.mem_range.mpr hj)
        (Set.mem_biUnion (Finset.mem_range.mpr hlt) ?_)
      exact ⟨by rw [hgi, hgj]; exact hne.symm, by rw [hgi, hgj]; exact hout.symm⟩
    · refine Set.mem_biUnion (Finset.mem_range.mpr hi)
        (Set.mem_biUnion (Finset.mem_range.mpr (lt_of_le_of_ne hge hij.symm)) ?_)
      exact ⟨by rw [hgi, hgj]; exact hne, by rw [hgi, hgj]; exact hout⟩
  -- Each index pair is a collision of two bounded canonical forms.
  have hpair : ∀ i < P.length, ∀ j < i, μ (E i j) ≤ ((2 : ℝ≥0∞)⁻¹) ^ k := by
    intro i hi j hj
    have hj' : j < P.length := hj.trans hi
    have hmem : ∀ {a : Nat}, a < P.length → get a ∈ P := fun {a} ha =>
      (hgetD a ha) ▸ List.getElem_mem ha
    by_cases heq : Affine.normalize (get i) = Affine.normalize (get j)
    · have hempty : E i j = ∅ := by
        ext sample
        simp [E, heq]
      rw [hempty]
      simp
    · calc
        μ (E i j) ≤ μ {sample : Sample m k |
            Collision.output (Affine.normalize (get i)) sample =
              Collision.output (Affine.normalize (get j)) sample} :=
          μ.mono fun sample hs => hs.2
        _ ≤ ((2 : ℝ≥0∞)⁻¹) ^ k :=
          affine_collision_bound _ _
            (Affine.normalize_bounded (hP _ (hmem hi)))
            (Affine.normalize_bounded (hP _ (hmem hj')))
            heq
  calc
    (PMF.uniformOfFintype (Sample m k)).toOuterMeasure
        {sample | Collides P sample} ≤
        μ (⋃ i ∈ Finset.range P.length, ⋃ j ∈ Finset.range i, E i j) :=
      μ.mono hsub
    _ ≤ ∑ i ∈ Finset.range P.length, μ (⋃ j ∈ Finset.range i, E i j) :=
      MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ Finset.range P.length, ∑ j ∈ Finset.range i, μ (E i j) :=
      Finset.sum_le_sum fun i _ => MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ Finset.range P.length, ∑ _j ∈ Finset.range i,
          ((2 : ℝ≥0∞)⁻¹) ^ k :=
      Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
        hpair i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
    _ = ((∑ i ∈ Finset.range P.length, i : ℕ) : ℝ≥0∞) *
          ((2 : ℝ≥0∞)⁻¹) ^ k := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← Finset.sum_mul]
      push_cast
      rfl
    _ = (P.length.choose 2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ k := by
      rw [Finset.sum_range_id, ← Nat.choose_two_right]

/-!
## MAIN THEOREM: Correctness of the randomized Algorithm 1 (headline result)

**Statement.** Fix any circuit `C` on `n` qubits and any hash width `k`.
Draw a sample uniformly at random from
`Sample (analyze C).nextFresh k` — one independent uniform `k`-bit string per
symbolic variable — and run the randomized optimizer `foldR` on `C` with those
draws.  The probability that the output circuit is *not* semantically
equivalent to `C` (as an exact complex weighted relation) is at most
`C(t,2) · (1/2)^k`, where `t = (rzParities C).length` is the number of `Rz` gates
in `C`.  The probability is an exact rational over the finite sample space;
there are no hypotheses on `C`.

**Significance.** This is the paper's end-to-end guarantee for the hash-based
Algorithm 1 and the headline theorem of the whole formalization's randomized
half: the output is wrong only when the sample is unfaithful
(`foldR_correct_of_faithful` contrapositive), and unfaithful samples have
probability at most `C(t,2) · 2⁻ᵏ` (`collides_probability_le`).
-/

/--
Correctness of the randomized Algorithm 1: with `t` rotation gates and `k`-bit
hashes, the probability (over the uniformly drawn sample) that the optimizer
returns a circuit *not* equivalent to its input is at most `C(t,2) · 2⁻ᵏ`.
-/
theorem randomized_fold_correct {n k : Nat} (C : Circuit n) :
    (PMF.uniformOfFintype
        (Sample (Symbolic.analyze C).nextFresh k)).toOuterMeasure
        {sample | ¬ PhaseFolding.Equivalent (foldR (liftSample sample) C) C} ≤
      ((rzParities C).length.choose 2 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹) ^ k := by
  let μ := (PMF.uniformOfFintype
    (Sample (Symbolic.analyze C).nextFresh k)).toOuterMeasure
  calc
    (PMF.uniformOfFintype
        (Sample (Symbolic.analyze C).nextFresh k)).toOuterMeasure
        {sample | ¬ PhaseFolding.Equivalent (foldR (liftSample sample) C) C} ≤
        μ {sample | Collides (rzParities C) sample} := by
      apply μ.mono
      intro sample hne
      by_contra hnc
      exact hne (foldR_correct_of_faithful _ C (faithful_of_not_collides hnc))
    _ ≤ _ := collides_probability_le _ (rzParities_bounded C)

end
end TZap.RandomizedAlgorithm
