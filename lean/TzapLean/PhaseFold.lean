import TzapLean.Merge
import TzapLean.CnotMin

/-!
# `PhaseFoldRand`: the algorithm

The executable half of phase folding, following `src/phase_fold_rand.rs`. Each wire carries a
random `k`-bit *tag* standing for the parity it holds: `x` complements the tag, `cnot` XORs
the control's into the target's, `h`, `ccx` and `reset` draw a fresh one, and everything else
leaves tags alone. Two rotations may merge when their wires' tags agree — or are complements,
in which case the angle merges negated.

Nothing here mentions `Form`: like Rust, the pass only ever compares tags. The symbolic
parities live in `TzapLean.Analysis` and are attached to this algorithm in
`TzapLean.PhaseFoldProof`, where a tag collision is the *only* way the pass can be wrong.
-/

namespace TzapLean

open Form

/-! ## Tag states -/

/-- The all-ones tag: the hash of the constant parity `1`, i.e. Rust's bitwise `!`. -/
def ones (k : Nat) : BitString k := fun _ => 1

/-- A tag, as the algorithm stores it: `k` bits packed into a natural number.

The theory's tag is a *function* `Fin k → F₂` (`BitString k`), which is the right object for
the collision bound and the wrong one to compute with. Two measurements drove this:

* a stored function is a closure over its predecessors, so reading one bit of a tag `d` gates
  deep cost `kᵈ` — exactly `k` per `cnot`;
* an array of `k` bits fixed that but still allocated and compared `k` cells per operation,
  which was most of the pass's remaining time.

A packed number is one machine word: XOR and equality are single operations, and
`Nat.testBit` gives the bridge back to the theory. This is what Rust does too, with `u128`. -/
abbrev Tag := Nat

/-- The bits of a packed tag. -/
def wordToBits {k : Nat} (w : Tag) : BitString k := fun j => bit (w.testBit (j : Nat))

/-- Pack the low `j` bits of a bit function. -/
def bitsToWordAux (t : Nat → Bool) : Nat → Tag
  | 0 => 0
  | j + 1 => bitsToWordAux t j ||| (if t j then 2 ^ j else 0)

theorem testBit_bitsToWordAux (t : Nat → Bool) :
    ∀ (j i : Nat), (bitsToWordAux t j).testBit i = (decide (i < j) && t i) := by
  intro j
  induction j with
  | zero => intro i; simp [bitsToWordAux]
  | succ j ih =>
      intro i
      rw [bitsToWordAux, Nat.testBit_or, ih]
      cases htj : t j with
      | false =>
          simp only [htj, Bool.false_eq_true, if_false, Nat.zero_testBit, Bool.or_false]
          by_cases hij : i < j
          · simp [hij, Nat.lt_succ_of_lt hij]
          · by_cases hje : i = j
            · subst hje; simp [hij, htj]
            · have : ¬ (i < j + 1) := by omega
              simp [hij, this]
      | true =>
          simp only [htj, if_true, Nat.testBit_two_pow]
          by_cases hij : i < j
          · have hne : ¬ (j = i) := by omega
            simp [hij, Nat.lt_succ_of_lt hij, hne]
          · by_cases hje : i = j
            · subst hje; simp [hij, htj]
            · have : ¬ (i < j + 1) := by omega
              have hne : ¬ (j = i) := by omega
              simp [hij, this, hne]

/-- Pack a bit function into a tag. -/
def bitsToWord {k : Nat} (t : BitString k) : Tag :=
  bitsToWordAux (fun j => if h : j < k then unbit (t ⟨j, h⟩) else false) k

/-- **Packing and unpacking are inverse.** This is what lets the theory read a stored tag as
the function it stands for. -/
@[simp] theorem wordToBits_bitsToWord {k : Nat} (t : BitString k) :
    wordToBits (k := k) (bitsToWord t) = t := by
  funext j
  have hj : (j : Nat) < k := j.isLt
  simp only [wordToBits, bitsToWord, testBit_bitsToWordAux, hj, decide_true, Bool.true_and,
    dif_pos hj]
  simp

/-- Distinct tag functions have distinct packings, so comparing tags decides the functions. -/
theorem wordToBits_congr {k : Nat} {a b : Tag} (h : a = b) :
    wordToBits (k := k) a = wordToBits (k := k) b := by rw [h]

@[simp] theorem wordToBits_zero {k : Nat} : wordToBits (k := k) 0 = 0 := by
  funext j; simp [wordToBits, bit]

/-- XOR of tags is addition of the functions they stand for. -/
@[simp] theorem wordToBits_xor {k : Nat} (a b : Tag) :
    wordToBits (k := k) (a ^^^ b) = wordToBits (k := k) a + wordToBits (k := k) b := by
  funext j
  simp only [wordToBits, Nat.testBit_xor, Pi.add_apply]
  exact bit_xor _ _

/-- The all-ones tag. -/
def onesTag (k : Nat) : Tag := 2 ^ k - 1

@[simp] theorem wordToBits_onesTag (k : Nat) : wordToBits (k := k) (onesTag k) = ones k := by
  funext j
  simp [wordToBits, onesTag, Nat.testBit_two_pow_sub_one, j.isLt, ones, bit]

/-! ## Tag states -/

/-- Per-wire tags, plus the index of the next unused draw. -/
structure TState (k : Nat) where
  /-- One tag per wire. -/
  tags : List Tag
  /-- The next unused draw index. -/
  fresh : Nat

namespace TState

/-- Wire `q`'s tag (the zero tag for a wire the state does not cover). -/
def tagOf {k : Nat} (ts : TState k) (q : Qubit) : Tag := ts.tags.getD q 0

/-- Wire `i` starts out tagged with the `i`-th draw. -/
def initial {k : Nat} (wdraws : Nat → Tag) (n : Nat) : TState k where
  tags := (List.range n).map wdraws
  fresh := n

/-- The Rust transfer functions, on tags. -/
def step {k : Nat} (wdraws : Nat → Tag) (ts : TState k) (g : Gate) : TState k :=
  match g with
  | .x q => { ts with tags := ts.tags.set q (ts.tagOf q ^^^ onesTag k) }
  | .cnot c t => { ts with tags := ts.tags.set t (ts.tagOf t ^^^ ts.tagOf c) }
  | .h q => { tags := ts.tags.set q (wdraws ts.fresh), fresh := ts.fresh + 1 }
  | .ccx _ _ t => { tags := ts.tags.set t (wdraws ts.fresh), fresh := ts.fresh + 1 }
  | .reset q => { tags := ts.tags.set q (wdraws ts.fresh), fresh := ts.fresh + 1 }
  | _ => ts

/-- The tag state after a gate list. -/
def steps {k : Nat} (wdraws : Nat → Tag) (ts : TState k) : List Gate → TState k
  | [] => ts
  | g :: gs => steps wdraws (ts.step wdraws g) gs

end TState

/-! ## Matching -/

/-- Compare a later site's tag with a pending one: `some false` when they agree, `some true`
when the later wire carries the complementary parity (Rust's canonicalisation), `none`
otherwise. -/
def matchTag (k : Nat) (pending later : Tag) : Option Bool :=
  if later == pending then some false
  else if later == pending ^^^ onesTag k then some true
  else none

/-! ## The fold -/

/-- Scan forward for a rotation on the same parity, carrying the tag state. A gate that is
not unitary stops the scan: this pass never folds across a `measure` or a `reset`. -/
def mergeInto {k : Nat} (wdraws : Nat → Tag) (ts : TState k) (tag : Tag) (θ : ℚ) :
    List Gate → Option (List Gate)
  | [] => none
  | g :: gs =>
      if g.isUnitary then
        match rotAngle g with
        | some (φ, q') =>
            match matchTag k tag (ts.tagOf q') with
            | some sign => some (Gate.rz (φ + signedAngle sign θ) q' :: gs)
            | none => (mergeInto wdraws (ts.step wdraws g) tag θ gs).map (g :: ·)
        | none => (mergeInto wdraws (ts.step wdraws g) tag θ gs).map (g :: ·)
      else none

/-- Merging rewrites one rotation in place, so the list keeps its length. -/
theorem mergeInto_length {k : Nat} (wdraws : Nat → Tag) (tag : Tag) (θ : ℚ) :
    ∀ (gs gs' : List Gate) (ts : TState k), mergeInto wdraws ts tag θ gs = some gs' →
      gs'.length = gs.length := by
  intro gs
  induction gs with
  | nil => intro gs' ts h; simp [mergeInto] at h
  | cons g gs ih =>
      intro gs' ts h
      simp only [mergeInto] at h
      split at h
      · split at h
        · split at h
          · simp only [Option.some.injEq] at h
            subst h
            simp
          · rcases Option.map_eq_some_iff.1 h with ⟨t, ht, rfl⟩
            simp [ih t _ ht]
        · rcases Option.map_eq_some_iff.1 h with ⟨t, ht, rfl⟩
          simp [ih t _ ht]
      · exact absurd h (by simp)

/-- Fold a gate list: every rotation is pushed forward into the next rotation on its parity,
if there is one. -/
def foldFrom {k : Nat} (wdraws : Nat → Tag) (ts : TState k) : List Gate → List Gate
  | [] => []
  | g :: gs =>
      match rotAngle g with
      | some (θ, q) =>
          match hm : mergeInto wdraws ts (ts.tagOf q) θ gs with
          | some gs' => foldFrom wdraws ts gs'
          | none => g :: foldFrom wdraws (ts.step wdraws g) gs
      | none => g :: foldFrom wdraws (ts.step wdraws g) gs
  termination_by gs => gs.length
  decreasing_by
    all_goals
      first
        | (rw [mergeInto_length wdraws (ts.tagOf q) θ gs gs' ts hm]; simp)
        | simp

/-- Re-emit every rotation as Clifford+T where its angle allows, dropping those that
cancelled — the tail of Rust's reconstruction loop. -/
def emitAll : List Gate → List Gate
  | [] => []
  | g :: gs =>
      (match rotAngle g with
        | some (a, q) => emitRotation q a
        | none => [g]) ++ emitAll gs

/-- Phase folding on a gate list, with the draws supplied. -/
def phaseFoldGates (k : Nat) (wdraws : Nat → Tag) (n : Nat) (gs : List Gate) : List Gate :=
  emitAll (foldFrom (k := k) wdraws (TState.initial (k := k) wdraws n) gs)

/-- Phase folding on a circuit. -/
def phaseFold (k : Nat) (wdraws : Nat → Tag) (c : Circuit) : Circuit where
  numQubits := c.numQubits
  numCbits := c.numCbits
  gates := phaseFoldGates k wdraws c.numQubits c.gates

@[simp] theorem phaseFold_numQubits (k : Nat) (wdraws : Nat → Tag) (c : Circuit) :
    (phaseFold k wdraws c).numQubits = c.numQubits := rfl

@[simp] theorem phaseFold_numCbits (k : Nat) (wdraws : Nat → Tag) (c : Circuit) :
    (phaseFold k wdraws c).numCbits = c.numCbits := rfl

/-! ## Where the randomness comes from

The pass is a pure function of its word-draw stream, so entropy enters only here, at the
boundary. The correctness theorem relates that stream to the theory's `Draws k` through
`wordToBits`, which is why nothing in the inner loop ever touches an `F₂` function: the pass
XORs machine words, and only the statement of the theorem talks about bits.

`bitsToWord` converts a drawn `Sample` into that stream — once per variable, never per step —
so `phaseFoldIO` runs the very distribution `PhaseFoldRand.correct` bounds, modulo the one
thing no proof can supply: that `IO.rand` is uniform. -/

/-- The number of variables a circuit's analysis can allocate: one per wire, plus at most one
per gate (`h`, `ccx` and `reset` are the only allocating gates). -/
def varBound (c : Circuit) : Nat := c.numQubits + c.gates.length

/-- Executable `liftSample`: pad a finite seed out to a draw stream. -/
def padSample {m k : Nat} (sample : Sample m k) : Draws k :=
  fun i => if h : i < m then sample ⟨i, h⟩ else 0

theorem padSample_eq {m k : Nat} (sample : Sample m k) : padSample sample = liftSample sample :=
  rfl

/-- The packed word stream a bit-valued draw stream stands for. -/
def wordsOf (k : Nat) (draws : Draws k) : Nat → Tag := fun i => bitsToWord (draws i)

@[simp] theorem wordToBits_wordsOf (k : Nat) (draws : Draws k) (i : Nat) :
    wordToBits (k := k) (wordsOf k draws i) = draws i := by
  simp [wordsOf]

/-- A deterministic word stream from a seed: splitmix64 bit mixing, one `k`-bit tag per
variable. Used by the CLI, where a run is reproducible from `--seed`.

Packed directly, never through a bit function: converting per step was measurably most of the
pass's remaining cost. -/
def seedWords (k : Nat) (seed : Nat) : Nat → Tag := fun i =>
  let x : UInt64 := (seed.toUInt64 + i.toUInt64 + 1) * 0x9E3779B97F4A7C15
  let x := (x ^^^ (x >>> 30)) * 0xBF58476D1CE4E5B9
  let x := (x ^^^ (x >>> 27)) * 0x94D049BB133111EB
  let x := x ^^^ (x >>> 31)
  x.toNat % 2 ^ k

/-- Draw one uniform `k`-bit tag per variable from the runtime's generator. -/
def randomWords (m k : Nat) : IO (Nat → Tag) := do
  let mut rows : Array Nat := #[]
  for _ in [0:m] do
    let mut w : Nat := 0
    for j in [0:k] do
      let b ← IO.rand 0 1
      w := w ||| (if b == 1 then 2 ^ j else 0)
    rows := rows.push w
  return fun i => rows[i]!

/-- Phase folding with freshly drawn tags: the pass as it would actually be run. -/
def phaseFoldIO (k : Nat) (c : Circuit) : IO Circuit := do
  let wdraws ← randomWords (varBound c) k
  return phaseFold k wdraws c

end TzapLean
