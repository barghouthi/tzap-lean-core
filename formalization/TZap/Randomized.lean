import TZap.Affine

/-!
# The randomized (hash-based) parity analysis

The symbolic analysis (`TZap.Symbolic`) tracks, for each qubit, an exact parity
expression over ℕ-indexed variables. For large circuits the paper replaces these
expressions by short *hashes*: each variable independently draws a uniform `k`-bit
string, and a parity is hashed by XORing (adding in `𝔽₂`, per hash coordinate) the
draws of its variables, plus the constant.

This file formalizes that analysis with the randomness made explicit:

* `Draws k = Nat → BitString k` is a stream assigning one `k`-bit string per variable
  (the finite truncation actually sampled, `Sample m k`, lives in `Collision.lean`);
* `evalBits draws p` hashes a parity `p` by evaluating its canonical affine form
  (`Affine.normalize p`) coordinatewise under the draws;
* `step`/`analyzeFrom`/`analyze` mirror the symbolic transfer functions gate for gate,
  but on hashed states: CNOT adds bitstrings, X adds the all-ones string, H installs
  the draw of a fresh variable, Rz is the identity.

The main theorem `analyze_correspond` shows there is nothing approximate about the
*algorithm* itself: given a fixed draw stream, the randomized analysis is exactly the
symbolic analysis evaluated under the draws (`Correspond`). All probabilistic content
is thus isolated in the collision bound (`Collision.lean`) and its uses.
-/


namespace TZap.Randomized

open TZap.Symbolic
open TZap.Affine

noncomputable section

/-- A `k`-bit string, represented as a function `Fin k → 𝔽₂` so that XOR of bitstrings
is pointwise addition. Hash values of parities live here. -/
abbrev BitString (k : Nat) := Fin k → F₂

/-- An infinite stream of draws: one uniform `k`-bit string per ℕ-indexed variable.
This makes the randomized analysis a *deterministic* function of its randomness; the
finite prefix that is actually sampled is `Collision.Sample m k`, lifted to a `Draws`
by `Collision.liftSample`. -/
abbrev Draws (k : Nat) := Nat → BitString k

/-- The all-ones `k`-bit string. Adding it flips every hash bit — the hashed counterpart
of negating a parity (the `X` gate / `Parity.flip`). -/
def allOnes (k : Nat) : BitString k := fun _ => 1

/-! ## Hashing parities -/

/-- Evaluate one symbolic parity under a valuation by `k`-bit strings: coordinate `j` of
the hash is the affine evaluation of `normalize p` at bit `j` of each variable's draw.
Concretely, the hash is the 𝔽₂-sum (XOR) of the draws of the variables of `p`, plus its
constant. Hashing factors through `Affine.normalize`, so parities with equal normal
forms always hash equal — the "no false negatives" direction used by
`RandomizedAlgorithm.lean`. -/
def evalBits {k : Nat} (draws : Draws k) (p : Parity) : BitString k :=
  fun j => Affine.eval (fun i => draws i j) (Affine.normalize p)

/-- Hash of a constant parity: the constant bit replicated over all `k` coordinates. -/
@[simp] theorem evalBits_const {k} (draws : Draws k) (b : Bool) :
    evalBits draws (.const b) = fun _ => bit b := by
  funext j
  simp [evalBits, Affine.normalize, Affine.eval]

/-- Hash of a single variable: exactly that variable's draw. -/
@[simp] theorem evalBits_var {k} (draws : Draws k) (i : Nat) :
    evalBits draws (.var i) = draws i := by
  funext j
  simp [evalBits, Affine.normalize, Affine.eval]

/-- Hashing is a homomorphism for xor: the hash of `p ⊕ q` is the pointwise 𝔽₂-sum of
the hashes. This is what makes the CNOT transfer rule below match the symbolic one. -/
@[simp] theorem evalBits_xor {k} (draws : Draws k) (p q : Parity) :
    evalBits draws (.xor p q) = evalBits draws p + evalBits draws q := by
  funext j
  simp [evalBits]

/-- Hashing a flipped parity adds the all-ones string: negation flips every hash bit.
Matches the `X` transfer rule below. -/
@[simp] theorem evalBits_flip {k} (draws : Draws k) (p : Parity) :
    evalBits draws p.flip = evalBits draws p + allOnes k := by
  funext j
  simp [Parity.flip, allOnes, bit]

/-! ## The randomized analysis -/

/-- The randomized analysis state: each of the `n` qubits carries a `k`-bit hash (in
place of the symbolic parity expression), together with the same fresh-variable counter
as the symbolic analysis (`nextFresh` counts variables allocated so far, so it also
tells which draws have been consumed). -/
structure State (n k : Nat) where
  qubit : Fin n → BitString k
  nextFresh : Nat

/-- The initial randomized state: qubit `q` starts as the hash of the input variable
`var q`, i.e. draw number `q`; the first `n` variables (and draws) are consumed. Mirrors
`Symbolic.initial`, which assigns `var q` to qubit `q` with counter `n`. -/
def initial {k : Nat} (draws : Draws k) (n : Nat) : State n k where
  qubit q := draws q.val
  nextFresh := n

/-- The randomized transfer rules, made deterministic by an explicit draw stream — the
hashed image of `Symbolic.step`: `CNOT c t` XORs the control's hash into the target's;
`X t` XORs in the all-ones string (bit flip); `H t` discards the target's hash and
installs the draw of a fresh variable, bumping the counter; `Rz` leaves the state
unchanged. Each rule is exactly the symbolic rule pushed through `evalBits`
(proved gate by gate in `step_correspond`). -/
def step {n k : Nat} (draws : Draws k) (s : State n k) : Gate n → State n k
  | .cnot c t =>
      { s with qubit := fun q => if q = t then s.qubit t + s.qubit c else s.qubit q }
  | .x t =>
      { s with qubit := fun q => if q = t then s.qubit t + allOnes k else s.qubit q }
  | .hadamard t =>
      { qubit := fun q => if q = t then draws s.nextFresh else s.qubit q
        nextFresh := s.nextFresh + 1 }
  | .rz _ _ => s

/-- Run the randomized analysis over a circuit from an arbitrary starting state, folding
`step` left to right. Generalizing over the start state is what lets the correspondence
proof (and the algorithm proofs that resume the analysis mid-circuit) go by induction. -/
def analyzeFrom {n k : Nat} (draws : Draws k) : State n k → Circuit n → State n k
  | s, [] => s
  | s, g :: gs => analyzeFrom draws (step draws s g) gs

/-- The full randomized analysis of a circuit: run `analyzeFrom` from `initial`.
The hashed counterpart of `Symbolic.analyze`; `RandomizedAlgorithm.lean` interleaves
this state evolution with its merge decisions. -/
def analyze {n k : Nat} (draws : Draws k) (C : Circuit n) : State n k :=
  analyzeFrom draws (initial draws n) C

/-! ## Correspondence with the symbolic analysis -/

/-- Pointwise correspondence between a randomized state and a symbolic state: the fresh
counters agree, and each qubit's bitstring is exactly the hash (`evalBits`) of that
qubit's symbolic parity. The invariant threaded through the analysis in the theorems
below. -/
def Correspond {n k : Nat} (draws : Draws k)
    (random : State n k) (symbolic : Symbolic.State n) : Prop :=
  random.nextFresh = symbolic.nextFresh ∧
  ∀ q, random.qubit q = evalBits draws (symbolic.qubit q)

/-- Base case: the initial randomized state corresponds to the initial symbolic state
(qubit `q` holds draw `q`, which is precisely the hash of `var q`). -/
theorem initial_correspond {n k} (draws : Draws k) :
    Correspond draws (initial draws n) (Symbolic.initial n) := by
  constructor
  · rfl
  · intro q
    simp [initial, Symbolic.initial]

/-- Inductive step: one gate preserves the correspondence. Checked case by case; the
CNOT and X cases use that `evalBits` is a homomorphism for xor/flip, and the Hadamard
case uses that both sides consume the *same* fresh variable (counters agree). -/
theorem step_correspond {n k} (draws : Draws k)
    (random : State n k) (symbolic : Symbolic.State n) (g : Gate n)
    (h : Correspond draws random symbolic) :
    Correspond draws (step draws random g) (Symbolic.step symbolic g) := by
  rcases h with ⟨hnext, hqubit⟩
  constructor
  · cases g <;> simp [step, Symbolic.step, hnext]
  · intro q
    cases g with
    | cnot c t =>
        by_cases hqt : q = t
        · subst q
          simp [step, Symbolic.step, hqubit]
        · simp [step, Symbolic.step, hqt, hqubit]
    | x t =>
        by_cases hqt : q = t
        · subst q
          simp [step, Symbolic.step, hqubit]
        · simp [step, Symbolic.step, hqt, hqubit]
    | hadamard t =>
        by_cases hqt : q = t
        · subst q
          simp [step, Symbolic.step, hnext]
        · simp [step, Symbolic.step, hqt, hqubit]
    | rz θ t => simp [step, Symbolic.step, hqubit]

/-- The correspondence is preserved along a whole circuit: iterate `step_correspond` by
induction on the gate list, generalizing over the pair of corresponding start states. -/
theorem analyzeFrom_correspond {n k} (draws : Draws k)
    (random : State n k) (symbolic : Symbolic.State n) (C : Circuit n)
    (h : Correspond draws random symbolic) :
    Correspond draws (analyzeFrom draws random C) (Symbolic.analyzeFrom symbolic C) := by
  induction C generalizing random symbolic with
  | nil => exact h
  | cons g C ih => exact ih _ _ (step_correspond draws random symbolic g h)

/-!
## MAIN THEOREM: the randomized analysis is the symbolic analysis under the draws

**Statement.** Fix any draw stream (one `k`-bit string per variable) and any circuit.
Then the randomized analysis with that explicit stream is EXACTLY the symbolic analysis
evaluated under the draws: the two runs have the same fresh-variable counter, and each
qubit's bitstring equals the hash of that qubit's symbolic parity — the 𝔽₂-sum of the
draws of the parity's variables (plus its constant), per hash coordinate. There is no
approximation in the algorithm itself; randomness enters only through which draws were
sampled.

**Significance.** This reduces every question about the randomized analysis to a
question about hashes of symbolic parities. In particular, the randomized optimizer
misbehaves only when two parities with *distinct* normal forms hash equal — exactly the
event bounded by `Collision.affine_collision_bound` — which is how
`RandomizedAlgorithm.randomized_fold_correct` obtains its `t² · 2⁻ᵏ` failure bound.
-/

/-- The randomized analysis is exactly symbolic analysis evaluated under the draws:
same fresh counter, and each qubit's bitstring is the hash of its symbolic parity. -/
theorem analyze_correspond {n k} (draws : Draws k) (C : Circuit n) :
    Correspond draws (analyze draws C) (Symbolic.analyze C) :=
  analyzeFrom_correspond draws _ _ C (initial_correspond draws)

/-- Convenient projection of `analyze_correspond`: the bitstring of qubit `q` after the
randomized analysis is the hash of its symbolic parity. This is the form consumed by
`RandomizedSoundness.lean` and the randomized algorithm proofs. -/
theorem analyze_qubit_eq_evalBits {n k} (draws : Draws k) (C : Circuit n) (q : Fin n) :
    (analyze draws C).qubit q = evalBits draws ((Symbolic.analyze C).qubit q) :=
  (analyze_correspond draws C).2 q

end
end TZap.Randomized
