import Tzap.SuperOpt.GlobalPhase

/-!
# Bounded Search and the Synthesis Table

This file formalizes how SuperOpt *builds* its synthesis table (`src/super_opt/table.rs`): grow
circuits over a finite gate library one gate at a time, and record each unitary the first time it
is reached, keyed by the phase-canonical form from `Tzap.SuperOpt.GlobalPhase`. The payoff is
`build_minimal`: a table hit is not merely *a* circuit for that unitary, it is a *shortest* one,
which is why a lookup needs no search of its own.

## Why the enumeration order is the whole argument

Minimality is not a property of the search *space* — every order enumerates the same circuits —
it is a property of the *order*, and only of the order:

* `find?_length_le_of_pairwise` isolates exactly what is needed: if the visiting order is
  nondecreasing in circuit length, then the first circuit matching any predicate is a shortest
  one matching it. Nothing about unitaries enters.
* `searchOrder_pairwise_length` discharges that side condition for the enumeration used here,
  which visits all circuits of length `0`, then all of length `1`, and so on up to `bound`.

The distinction matters. A **plain depth-first search is not length-monotone and breaks the
theorem**: DFS pre-order reaches `[T, T]` long before it reaches `[S]`, so with `T² = S` a
first-wins table would file the length-2 circuit under `S`'s key. What is safe is any
length-ordered traversal — breadth-first by layers (what `table.rs` does), or equivalently
iterative-deepening DFS, whose `d`-th round is precisely `level library d` below.

## Correspondence with the Rust implementation

| Lean | Rust (`src/super_opt/table.rs`) |
| --- | --- |
| `level library d` | one breadth-first layer: the `frontier` at `depth = d` |
| `searchOrder library bound` | the whole `'depths: for depth in 1..=config.max_gates` loop |
| `build`'s first-match-wins | `if !table.contains_key(&fingerprint)` before `insert_child` |
| `canonicalize` as the key | `unitary_fingerprint`, which hashes the phase-canonical matrix |
| `build_minimal` | the module comment's "the first circuit to reach a unitary is a smallest one" |

Two differences are deliberate. The Rust prunes the frontier (a gate never follows its own
inverse; qubit-disjoint neighbours are expanded in one canonical order only) and stops early when
`max_entries_per_qubit` is hit; both are refinements that only *remove* circuits already known to
be redundant or unreachable within the budget, so they are omitted here — this file is about why
first-wins-in-length-order yields minimality, which is what the prunes are designed to preserve.
The Rust also keys on a 64-bit hash of the canonical matrix and confirms hits by exact comparison;
the hash is a performance device, and the exact comparison is what `canonicalize` models.
-/

namespace Tzap.SuperOpt

open Tzap.Unitary
open Tzap.SuperOpt.GlobalPhase

open scoped Classical

noncomputable section

variable {n : Nat}

/-! ## The search space -/

/-- Every circuit of exactly length `d` over `library`, in enumeration order. A circuit is
extended at its tail, matching the implementation's left-multiplication of the new gate onto the
accumulated matrix (`apply_gate_left`): the new gate runs last. -/
def level (library : List (Gate n)) : Nat → List (Circuit n)
  | 0 => [[]]
  | d + 1 => (level library d).flatMap fun C => library.map fun g => C ++ [g]

/-- `C` lies in the bounded search space: at most `bound` gates, each from `library`. -/
def InSpace (library : List (Gate n)) (bound : Nat) (C : Circuit n) : Prop :=
  C.length ≤ bound ∧ ∀ g ∈ C, g ∈ library

/-- A layer contains exactly the library circuits of its own length. -/
theorem mem_level {library : List (Gate n)} {d : Nat} {C : Circuit n} :
    C ∈ level library d ↔ C.length = d ∧ ∀ g ∈ C, g ∈ library := by
  induction d generalizing C with
  | zero =>
    constructor
    · intro h
      have : C = [] := by simpa [level] using h
      subst this
      simp
    · rintro ⟨hlen, -⟩
      have : C = [] := List.length_eq_zero_iff.mp hlen
      subst this
      simp [level]
  | succ d ih =>
    simp only [level, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨C', hC', g, hg, rfl⟩
      obtain ⟨hlen, hmem⟩ := ih.mp hC'
      refine ⟨by simp [hlen], fun g' hg' => ?_⟩
      rcases List.mem_append.mp hg' with h | h
      · exact hmem g' h
      · rw [List.mem_singleton.mp h]; exact hg
    · rintro ⟨hlen, hmem⟩
      -- A circuit of length `d + 1` is a shorter one with a final gate.
      rcases List.eq_nil_or_concat C with rfl | ⟨C', g, rfl⟩
      · simp at hlen
      · rw [List.concat_eq_append] at hlen hmem ⊢
        have hg : g ∈ library := hmem g (by simp)
        have hlen' : C'.length = d := by simpa using hlen
        have hmem' : ∀ g' ∈ C', g' ∈ library := fun g' hg' => hmem g' (by simp [hg'])
        exact ⟨C', ih.mpr ⟨hlen', hmem'⟩, g, hg, rfl⟩

/-- Every circuit in a layer has that layer's length. -/
theorem length_of_mem_level {library : List (Gate n)} {d : Nat} {C : Circuit n}
    (h : C ∈ level library d) : C.length = d := (mem_level.mp h).1

/-- The order in which the bounded search visits circuits: all of length `0`, then all of length
`1`, and so on through `bound`. This is the breadth-first layer order of `table.rs`; it is also
the order in which iterative-deepening DFS first visits each circuit. -/
def searchOrder (library : List (Gate n)) (bound : Nat) : List (Circuit n) :=
  (List.range (bound + 1)).flatMap (level library)

/-- The search visits exactly the bounded space. -/
theorem mem_searchOrder {library : List (Gate n)} {bound : Nat} {C : Circuit n} :
    C ∈ searchOrder library bound ↔ InSpace library bound C := by
  simp only [searchOrder, List.mem_flatMap, List.mem_range, InSpace]
  constructor
  · rintro ⟨d, hd, hC⟩
    obtain ⟨hlen, hmem⟩ := mem_level.mp hC
    exact ⟨by omega, hmem⟩
  · rintro ⟨hlen, hmem⟩
    exact ⟨C.length, by omega, mem_level.mpr ⟨rfl, hmem⟩⟩

/-- A list whose entries all have the same length is trivially length-sorted. -/
theorem pairwise_of_constant_length {l : List (Circuit n)} {d : Nat}
    (h : ∀ C ∈ l, C.length = d) : l.Pairwise fun A B => A.length ≤ B.length := by
  induction l with
  | nil => simp
  | cons C l ih =>
    refine List.pairwise_cons.mpr ⟨fun B hB => ?_, ih fun D hD => h D (List.mem_cons_of_mem _ hD)⟩
    rw [h C (List.mem_cons_self ..), h B (List.mem_cons_of_mem _ hB)]

/-- **The side condition that makes first-wins correct.** The search order is nondecreasing in
circuit length. Breadth-first layering is exactly what buys this; a plain depth-first pre-order
would not satisfy it. -/
theorem searchOrder_pairwise_length (library : List (Gate n)) (bound : Nat) :
    (searchOrder library bound).Pairwise fun A B => A.length ≤ B.length := by
  induction bound with
  | zero => simp [searchOrder, level]
  | succ bound ih =>
    have hsplit : searchOrder library (bound + 1)
        = searchOrder library bound ++ level library (bound + 1) := by
      simp [searchOrder, List.range_succ, List.flatMap_append]
    rw [hsplit]
    refine List.pairwise_append.mpr ⟨ih, pairwise_of_constant_length (d := bound + 1) ?_, ?_⟩
    · exact fun C hC => length_of_mem_level hC
    · intro A hA B hB
      have hA' : A.length ≤ bound := (mem_searchOrder.mp hA).1
      have hB' : B.length = bound + 1 := length_of_mem_level hB
      omega

/-! ## First match in a length-ordered traversal is a shortest match -/

/-- The general principle, with no quantum content: in a length-nondecreasing traversal, the
first element satisfying a predicate is a shortest element satisfying it. -/
theorem find?_length_le_of_pairwise {l : List (Circuit n)} {p : Circuit n → Bool} {D C : Circuit n}
    (hsorted : l.Pairwise fun A B => A.length ≤ B.length)
    (hfind : l.find? p = some D) (hC : C ∈ l) (hpC : p C) : D.length ≤ C.length := by
  obtain ⟨-, as, bs, rfl, hbefore⟩ := List.find?_eq_some_iff_append.mp hfind
  -- `C` cannot sit in the discarded prefix: nothing there satisfies `p`.
  have hC' : C ∈ D :: bs := by
    rcases List.mem_append.mp hC with h | h
    · exact absurd hpC (by simpa using hbefore C h)
    · exact h
  -- Everything from `D` onwards is at least as long as `D`.
  obtain ⟨-, hsuffix, -⟩ := List.pairwise_append.mp hsorted
  rcases List.mem_cons.mp hC' with rfl | h
  · exact le_refl _
  · exact (List.pairwise_cons.mp hsuffix).1 C h

/-- The length-monotone hypothesis above cannot be dropped, and this is exactly how a plain
depth-first search fails: in a traversal that goes deep before it goes wide, the first match need
not be a shortest match. -/
theorem find?_not_minimal_without_pairwise :
    ∃ (l : List (Circuit 1)) (p : Circuit 1 → Bool) (D C : Circuit 1),
      l.find? p = some D ∧ C ∈ l ∧ p C ∧ ¬ D.length ≤ C.length :=
  ⟨[[.x 0, .x 0], [.x 0]], fun _ => true, [.x 0, .x 0], [.x 0], rfl,
    List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, by simp⟩

/-! ## The table -/

/-- A table key: the phase-canonical form of a unitary. `canonicalize_idem` says these are
exactly the fixed points of `canonicalize`, one per equivalence class. -/
abbrev CanonicalizedUnitary (n : Nat) := UnitaryMatrix n

/-- The synthesis table: for each key, the first circuit the bounded search reaches whose
canonical form is that key — the Rust's `if !table.contains_key(&fingerprint)` guard before
`insert_child`. -/
def build (library : List (Gate n)) (bound : Nat)
    (key : CanonicalizedUnitary n) : Option (Circuit n) :=
  (searchOrder library bound).find? fun C => decide (canonicalize (unitary C) = key)

/-- A stored circuit comes from the search space. -/
theorem build_inSpace {library : List (Gate n)} {bound : Nat} {key : CanonicalizedUnitary n}
    {D : Circuit n} (h : build library bound key = some D) : InSpace library bound D :=
  mem_searchOrder.mp (List.mem_of_find?_eq_some h)

/-- A stored circuit really does realize its key. -/
theorem build_key {library : List (Gate n)} {bound : Nat} {key : CanonicalizedUnitary n}
    {D : Circuit n} (h : build library bound key = some D) :
    canonicalize (unitary D) = key := by
  have := (List.find?_eq_some_iff_append.mp h).1
  simpa using this

/-- The search misses nothing: if any circuit in the space realizes the key, the table has an
entry for it. -/
theorem build_isSome {library : List (Gate n)} {bound : Nat} {key : CanonicalizedUnitary n}
    {C : Circuit n} (hC : InSpace library bound C) (hkey : canonicalize (unitary C) = key) :
    (build library bound key).isSome := by
  rcases hbuild : build library bound key with _ | D
  · rw [build, List.find?_eq_none] at hbuild
    exact absurd (by simpa using hkey) (hbuild C (mem_searchOrder.mpr hC))
  · rfl

/-- **Main theorem.** The circuit the table stores for a key is a *smallest* circuit in the
search space realizing that key: no circuit of the space with the same canonical form is shorter.

This is what makes a table hit the synthesis answer outright, with no search at lookup time. -/
theorem build_minimal {library : List (Gate n)} {bound : Nat} {key : CanonicalizedUnitary n}
    {D : Circuit n} (h : build library bound key = some D)
    {C : Circuit n} (hC : InSpace library bound C) (hkey : canonicalize (unitary C) = key) :
    D.length ≤ C.length :=
  find?_length_le_of_pairwise (searchOrder_pairwise_length library bound) h
    (mem_searchOrder.mpr hC) (by simpa using hkey)

/-- The bound does not actually weaken `build_minimal`: the stored circuit is a smallest circuit
over the library realizing that key, *full stop*, with no restriction to the search space. A
competitor longer than `bound` is longer than the stored circuit for free, since the stored
circuit fits in the bound. -/
theorem build_minimal_of_library {library : List (Gate n)} {bound : Nat}
    {key : CanonicalizedUnitary n} {D : Circuit n} (h : build library bound key = some D)
    {C : Circuit n} (hC : ∀ g ∈ C, g ∈ library) (hkey : canonicalize (unitary C) = key) :
    D.length ≤ C.length := by
  by_cases hlen : C.length ≤ bound
  · exact build_minimal h ⟨hlen, hC⟩ hkey
  · exact le_trans (build_inSpace h).1 (by omega)

/-- **Main theorem, up to global phase.** Stated the way the optimizer uses it: the stored
circuit implements the same operator as any competing circuit up to an unobservable phase, and
is no longer than any of them.

The nonzero hypotheses are what `Tzap.SuperOpt.GlobalPhase.canonicalize_eq_iff` needs to turn
equality of canonical forms into genuine phase-equivalence; they hold for any circuit whose
matrix is unitary. -/
theorem build_minimal_up_to_phase {library : List (Gate n)} {bound : Nat}
    {key : CanonicalizedUnitary n} {D : Circuit n} (h : build library bound key = some D)
    {C : Circuit n} (hC : ∀ g ∈ C, g ∈ library) (hkey : canonicalize (unitary C) = key)
    (hCne : unitary C ≠ 0) (hDne : unitary D ≠ 0) :
    EquivUpToPhase (unitary C) (unitary D) ∧ D.length ≤ C.length := by
  refine ⟨(canonicalize_eq_iff hCne hDne).mp ?_, build_minimal_of_library h hC hkey⟩
  rw [hkey, build_key h]

end

end Tzap.SuperOpt
