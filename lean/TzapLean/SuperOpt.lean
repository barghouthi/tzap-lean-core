import TzapLean.ExactMat
import TzapLean.Locality
import TzapLean.SynthTable

/-!
# `SuperOpt`: the Algorithm

A forward scan that carves out small *windows* — causally connected groups of gates on a few
wires — computes each window's exact matrix, and replaces it whenever a shorter gate list has
the same matrix. Nothing is matched syntactically: any identity expressible in the search
space is found without ever being written down.

Candidates come from the precomputed synthesis table (`SynthTable.lean`): a window's matrix
is canonicalized to a key and looked up, and a hit *is* the shortest circuit the enumeration
found for that unitary. The table is unverified — its BFS, its prunes, its key, its reified
matrices are all outside the proof — because every candidate is re-verified by `accepts`
before it is taken. A wrong table costs optimization, never correctness.

This is `src/super_opt/mod.rs`, with one deliberate departure: **skipped gates move to just
after the replacement** rather than staying interleaved. They commute with every window gate,
so this is invisible; it keeps the reconstruction to one list splice.

Windows are subsequences, not slices: gates in between that share no wire with the window are
simply skipped. The invariant that makes this sound — *no skipped gate touches the window's
support* — is maintained by re-checking every skipped gate when a new member widens the
support, and it is the hypothesis the correctness proof consumes.
-/

namespace TzapLean

/-- Limits on window growth and on how far the search looks. -/
structure SuperOptConfig where
  /-- Widest window, in wires. -/
  maxQubits : Nat := 2
  /-- Longest window, in gates. -/
  maxWindow : Nat := 6
deriving Repr

/-- Gates a window may contain: `rz` is outside the exact Clifford+T domain, and
`measure`/`reset` are not unitary. -/
def isWindowGate (g : Gate) : Bool :=
  match g with
  | .rz _ _ | .measure _ _ | .reset _ => false
  | _ => true

/-- Whether a gate touches any of these wires. -/
def touches (S : List Qubit) (g : Gate) : Bool := g.qubitsOf.any (fun q => S.contains q)

/-- `S`, plus any of these wires that are new. -/
def widen (S : List Qubit) : List Qubit → List Qubit
  | [] => S
  | q :: qs => widen (if S.contains q then S else S ++ [q]) qs

/-! ## Windows

A window is the **connected closure of its anchor**: the gates of a span that reach the
anchor through shared wires, with everything else in the span disjoint from the window's
wires and therefore commuting past it. That is Rust's `expand_component_closure`, and the
point of it is that a gate bringing in a *new* wire pulls in the earlier gates on that wire
too — retroactively. A window that refused to widen whenever some already-skipped gate
touched the new wire would systematically miss every rewrite that has to be discovered that
way, and this one used to.

So the span is stored as gates tagged with whether they are members, and widening runs
`closeSpan` to re-establish the closure. `members` is kept alongside as a plain list because
the hot path asks for its length once per gate scanned and it is capped at `maxWindow`, where
the span is not; `WinOk.memEq` is what keeps the two honest.

The span is stored **most recent first**: it grows once per gate the scan passes, and
`xs ++ [g]` copies the whole list each time, which made a single window's scan quadratic in
its span. Cons is `O(1)`; the accessors reverse once, and only where order is needed. -/

/-- A span of gates, each tagged with whether the window holds it. -/
abbrev Span := List (Gate × Bool)

/-- The gates the window holds, in the order given. -/
def spanMembers (span : Span) : List Gate :=
  span.filterMap fun p => if p.2 then some p.1 else none

/-- The gates the span passed over, in the order given. -/
def spanSkipped (span : Span) : List Gate :=
  span.filterMap fun p => if p.2 then none else some p.1

/-- Every gate of the span, in the order given. -/
def spanGates (span : Span) : List Gate := span.map (·.1)

@[simp] theorem spanMembers_nil : spanMembers [] = [] := rfl
@[simp] theorem spanSkipped_nil : spanSkipped [] = [] := rfl
@[simp] theorem spanGates_nil : spanGates [] = [] := rfl

@[simp] theorem spanMembers_cons_true (g : Gate) (rest : Span) :
    spanMembers ((g, true) :: rest) = g :: spanMembers rest := rfl

@[simp] theorem spanMembers_cons_false (g : Gate) (rest : Span) :
    spanMembers ((g, false) :: rest) = spanMembers rest := rfl

@[simp] theorem spanSkipped_cons_true (g : Gate) (rest : Span) :
    spanSkipped ((g, true) :: rest) = spanSkipped rest := rfl

@[simp] theorem spanSkipped_cons_false (g : Gate) (rest : Span) :
    spanSkipped ((g, false) :: rest) = g :: spanSkipped rest := rfl

@[simp] theorem spanGates_cons (p : Gate × Bool) (rest : Span) :
    spanGates (p :: rest) = p.1 :: spanGates rest := rfl

/-- Membership in the member list is membership in the span, tagged. -/
theorem mem_spanMembers_iff {span : Span} {x : Gate} :
    x ∈ spanMembers span ↔ (x, true) ∈ span := by
  constructor
  · intro h
    rcases List.mem_filterMap.1 h with ⟨⟨y, c⟩, hy, hyx⟩
    cases c
    · simp at hyx
    · simp only [if_pos, Option.some.injEq] at hyx
      exact hyx ▸ hy
  · intro h; exact List.mem_filterMap.2 ⟨(x, true), h, rfl⟩

/-- …and likewise for the skipped list. -/
theorem mem_spanSkipped_iff {span : Span} {x : Gate} :
    x ∈ spanSkipped span ↔ (x, false) ∈ span := by
  constructor
  · intro h
    rcases List.mem_filterMap.1 h with ⟨⟨y, c⟩, hy, hyx⟩
    cases c
    · simp only [Bool.false_eq_true, if_false, Option.some.injEq] at hyx
      exact hyx ▸ hy
    · simp at hyx
  · intro h; exact List.mem_filterMap.2 ⟨(x, false), h, rfl⟩

/-! The span is stored reversed, so every fact proved about a span transfers to the stored
form by these three. -/

@[simp] theorem mem_spanMembers_reverse {span : Span} {x : Gate} :
    x ∈ spanMembers span.reverse ↔ x ∈ spanMembers span := by
  rw [mem_spanMembers_iff, mem_spanMembers_iff, List.mem_reverse]

@[simp] theorem mem_spanSkipped_reverse {span : Span} {x : Gate} :
    x ∈ spanSkipped span.reverse ↔ x ∈ spanSkipped span := by
  rw [mem_spanSkipped_iff, mem_spanSkipped_iff, List.mem_reverse]

@[simp] theorem spanGates_reverse (span : Span) :
    spanGates span.reverse = (spanGates span).reverse := by
  simp [spanGates]

@[simp] theorem spanMembers_append (a b : Span) :
    spanMembers (a ++ b) = spanMembers a ++ spanMembers b := by simp [spanMembers]

@[simp] theorem spanSkipped_append (a b : Span) :
    spanSkipped (a ++ b) = spanSkipped a ++ spanSkipped b := by simp [spanSkipped]

@[simp] theorem spanGates_append (a b : Span) :
    spanGates (a ++ b) = spanGates a ++ spanGates b := by simp [spanGates]

/-- A window under construction. -/
structure Win where
  /-- The wires the window covers. -/
  support : List Qubit
  /-- The window's gates, in order — `spanMembers` of the span, memoized. -/
  members : List Gate
  /-- The whole span consumed so far, most recent first, tagged with membership. -/
  revSpan : Span

/-- The span, in order. -/
def Win.span (w : Win) : Span := w.revSpan.reverse

/-- Gates of the span that the window skipped, in order. -/
def Win.skipped (w : Win) : List Gate := spanSkipped w.span

/-- The whole span consumed so far, in order — the gates a rewrite replaces. -/
def Win.consumed (w : Win) : List Gate := spanGates w.span

/-- The window an anchor gate starts. -/
def Win.start (g : Gate) : Win where
  support := g.qubitsOf
  members := [g]
  revSpan := [(g, true)]

@[simp] theorem Win.members_start (g : Gate) : (Win.start g).members = [g] := rfl

@[simp] theorem Win.support_start (g : Gate) : (Win.start g).support = g.qubitsOf := rfl

@[simp] theorem Win.skipped_start (g : Gate) : (Win.start g).skipped = [] := rfl

@[simp] theorem Win.consumed_start (g : Gate) : (Win.start g).consumed = [g] := rfl

/-! ### Closing the window over its wires -/

/-- One sweep of the closure: every skipped gate the support touches becomes a member, and
its wires join the support. Reports whether anything moved.

Written through projections of the recursive call rather than a destructuring `let`, so that
the equation lemmas below are the three cases and nothing else. -/
def absorbPass (S : List Qubit) : Span → List Qubit × Span × Bool
  | [] => (S, [], false)
  | (g, true) :: rest =>
      let r := absorbPass S rest
      (r.1, (g, true) :: r.2.1, r.2.2)
  | (g, false) :: rest =>
      if touches S g then
        let r := absorbPass (widen S g.qubitsOf) rest
        (r.1, (g, true) :: r.2.1, true)
      else
        let r := absorbPass S rest
        (r.1, (g, false) :: r.2.1, r.2.2)

@[simp] theorem absorbPass_nil (S : List Qubit) : absorbPass S [] = (S, [], false) := rfl

@[simp] theorem absorbPass_true (S : List Qubit) (g : Gate) (rest : Span) :
    absorbPass S ((g, true) :: rest) =
      ((absorbPass S rest).1, (g, true) :: (absorbPass S rest).2.1,
        (absorbPass S rest).2.2) := rfl

theorem absorbPass_false_touch {S : List Qubit} {g : Gate} (rest : Span)
    (h : touches S g = true) :
    absorbPass S ((g, false) :: rest) =
      ((absorbPass (widen S g.qubitsOf) rest).1,
        (g, true) :: (absorbPass (widen S g.qubitsOf) rest).2.1, true) := by
  simp only [absorbPass, if_pos h]

theorem absorbPass_false_miss {S : List Qubit} {g : Gate} (rest : Span)
    (h : touches S g = false) :
    absorbPass S ((g, false) :: rest) =
      ((absorbPass S rest).1, (g, false) :: (absorbPass S rest).2.1,
        (absorbPass S rest).2.2) := by
  simp only [absorbPass, h, Bool.false_eq_true, if_false]

/-- Sweep until nothing moves: the connected closure of the window over the span.

`none` when the fuel runs out, which cannot happen at the fuel the caller passes — each
sweep that reports a change absorbs at least one gate — but returning it rather than the
unclosed window is what lets `closeSpan_spec` state the invariant the proof needs: *every*
remaining skipped gate misses the support. -/
def closeSpan : Nat → List Qubit → Span → Option (List Qubit × Span)
  | 0, _, _ => none
  | fuel + 1, S, span =>
      let r := absorbPass S span
      if r.2.2 then closeSpan fuel r.1 r.2.1 else some (r.1, r.2.1)

/-! ## Proposing and verifying a replacement -/

/-- Whether a candidate is usable *and* really has the window's matrix, up to global phase.
This is the check the correctness proof consumes; the search that proposes candidates is
unverified, so everything the proof needs is re-established here. -/
def accepts {k : Nat} (target : ExactMat k) (cand : List Gate) : Bool :=
  cand.all (fun g => g.qubitsOf.all (fun q => q < k) && decide g.Wf) &&
    (match ExactMat.matrixOf k cand with
     | none => false
     | some N => (ExactMat.phaseMatch target N.normalize).isSome)

/-- Rename a local circuit back to the window's physical wires. -/
def globalizeGate (S : List Qubit) : Gate → Gate := mapQubits (fun i => S.getD i 0)

/-- Whether the table might answer for this window.

`trySynth` builds the window's matrix through `ExactMat`, which is indexed by a *function*, so
every entry access walks the chain of gates applied so far — profiling put `Basis.get`,
`Basis.set` and closure application at the top of the pass. That cost is worth paying once a
replacement exists, and wasted on the overwhelming majority of windows that have none. This
filter answers the same question on the flat representation the table itself is built with.

It is unverified in both directions, and safe in both: a false negative costs an optimization,
a false positive costs one wasted verified lookup. Nothing downstream trusts it — `trySynth`
still computes the real matrix and `accepts` still compares exactly. -/
def windowMayHold (tbl : SynthTable) (k : Nat) (fm : Option FlatMat) : Bool :=
  match fm with
  | none => false
  | some M => tbl.mayHold k M

/-- Whether the table holds a replacement for this window strictly shorter than it — the
question `trySynth` will go on to answer exactly. -/
def windowHasShorter (tbl : SynthTable) (k : Nat) (fm : Option FlatMat) (len : Nat) : Bool :=
  match fm with
  | none => false
  | some M => tbl.hasShorter k M len

/-- Look for a strictly shorter replacement for a window, verified before it is returned. -/
def trySynth (tbl : SynthTable) (w : Win) : Option (List Gate) :=
  if w.members.length ≤ 1 then none
  else
    match ExactMat.matrixOf w.support.length (localizeGates w.support w.members) with
    | none => none
    | some M =>
        match tbl.synthesize w.support.length M.normalize with
        | none => none
        | some cand =>
            if accepts M.normalize cand && cand.length < w.members.length then
              some (cand.map (globalizeGate w.support))
            else none

/-- `trySynth`, but skipping the expensive exact-matrix build when the filter says the table
holds nothing for this window. Same answer whenever the filter is right, and a strictly
verified answer either way. -/
def trySynthFiltered (tbl : SynthTable) (fm : Option FlatMat) (w : Win) : Option (List Gate) :=
  if windowMayHold tbl w.support.length fm then trySynth tbl w else none

/-- The window's flat matrix after one more gate: extended in place when the step changed
nothing else, rebuilt otherwise.

In place is only sound when the step added no wire *and* absorbed nothing: either renumbers
the support, so every earlier member's support-local encoding changes and the incremental
transition no longer starts from this matrix. (Rust says the same thing about its transition
cache.) Both are detected by length, since the support and the members only ever grow. -/
def extendFlat (sup : List Qubit) (members : List Gate) (fm : Option FlatMat) (w : Win)
    (g : Gate) : Option FlatMat :=
  if sup.length == w.support.length && members.length == w.members.length + 1 then
    fm.bind (·.applyGate (localizeGate w.support g))
  else FlatMat.ofGates sup.length (localizeGates sup members)

/-! ## The per-qubit index

`tryWindow` walks the gate list one gate at a time, and most gates it walks touch none of the
window's wires. The expected distance to the next gate on a given wire is `gates/qubit`, so a
window that accepts `maxWindow` members walks about `maxWindow × gates/qubit` gates — on
`gf2^16` that is ~2,300 gates per anchor, and it is where the pass spent its time.

Rust does not scan for the gates it cares about, it looks them up: `tracks[q]` holds the
indices of the gates touching wire `q`, so a lookahead visits only those. This is that index,
used to answer one question cheaply — *would this anchor produce a rewrite at all?* — before
the verified scan runs.

**Everything in this section is unverified, and safe in both directions.** A false negative
skips an anchor that had a rewrite, costing an optimization; a false positive costs one
wasted verified scan. `tryWindow` still produces every rewrite that is taken, and
`tryWindow_correct` still proves it. -/

/-- Per-wire gate indices, ascending. -/
def buildTracks (n : Nat) (gs : Array Gate) : Array (Array Nat) := Id.run do
  let mut tr : Array (Array Nat) := Array.replicate n #[]
  for h : i in [0 : gs.size] do
    for q in gs[i].qubitsOf do
      if q < n then tr := tr.modify q (·.push i)
  return tr

/-- Index of the first entry of a sorted array strictly greater than `x`. -/
def upperBoundIdx (a : Array Nat) (x : Nat) : Nat :=
  go a.size 0 a.size
where
  /-- Binary search, with the interval width as fuel. -/
  go : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if a[mid]! ≤ x then go fuel (mid + 1) hi else go fuel lo mid
      else lo

/-- The first gate on wire `q` strictly after index `i`. -/
def nextOn (tracks : Array (Array Nat)) (q i : Nat) : Option Nat :=
  match tracks[q]? with
  | none => none
  | some a =>
      let j := upperBoundIdx a i
      if j < a.size then some a[j]! else none

/-- Is any gate on wire `q` strictly between `lo` and `hi`? -/
def anyOn (tracks : Array (Array Nat)) (q lo hi : Nat) : Bool :=
  match nextOn tracks q lo with
  | none => false
  | some j => j < hi

/-- The first gate after `i` touching any wire of `S`. -/
def nextTouching (tracks : Array (Array Nat)) (S : List Qubit) (i : Nat) : Option Nat :=
  S.foldl (fun best q =>
    match nextOn tracks q i with
    | none => best
    | some j => some (match best with | none => j | some b => min b j)) none

/-- Would the window anchored at `i` reach a rewrite? Replays `tryWindow`'s growth through
the index, visiting only gates that touch the window — never the gaps between them.

The replay does not model `closeSpan`: when a gate brings in a wire that earlier gates of the
span already touch, the real window absorbs them and carries on with a different member list,
which this walk has no cheap way to reproduce. It answers `true` there and lets the verified
scan decide. That is the safe direction — the filter may only ever *over*-approximate — and it
is the case where the interesting rewrites live, so it is the one to be generous about. -/
def anchorMayFire (cfg : SuperOptConfig) (tbl : SynthTable) (n : Nat) (gs : Array Gate)
    (tracks : Array (Array Nat)) (anchor : Nat) : Bool :=
  let a := gs[anchor]!
  go (cfg.maxWindow + 1) a.qubitsOf [a] 1
    (FlatMat.ofGates a.qubitsOf.length (localizeGates a.qubitsOf [a])) anchor
where
  /-- Walk the window's own gates, widest-first, until it fires or dies. The window's matrix
  is carried and extended in place, rebuilt only when a gate brings a new wire in — rebuilding
  it per step made the filter quadratic in the window's length. -/
  go : Nat → List Qubit → List Gate → Nat → Option FlatMat → Nat → Bool
  | 0, _, _, _, _, _ => false
  | fuel + 1, sup, members, count, fm, i =>
      match nextTouching tracks sup i with
      | none => false
      | some j =>
          let g := gs[j]!
          let sup' := widen sup g.qubitsOf
          if !isWindowGate g || !g.qubitsOf.all (fun q => q < n) || !decide g.Wf
              || sup'.length > cfg.maxQubits || count + 1 > cfg.maxWindow then false
          else if (sup'.filter (fun q => !sup.contains q)).any
              (fun w => anyOn tracks w anchor j) then true
          else
            let members' := members ++ [g]
            let fm' :=
              if sup'.length == sup.length then fm.bind (·.applyGate (localizeGate sup g))
              else FlatMat.ofGates sup'.length (localizeGates sup' members')
            if windowHasShorter tbl sup'.length fm' (count + 1) then true
            else go fuel sup' members' (count + 1) fm' j

/-! ## The scan -/

/-- Is every gate one the window may hold, on wires the register has? Checked over the
*closed* member list, because closing can pull in gates the scan never inspected. -/
def membersOk (n : Nat) (members : List Gate) : Bool :=
  members.all fun g => isWindowGate g && g.qubitsOf.all (fun q => q < n) && decide g.Wf

/-- Accept a closed window if it is within bounds and holds only gates a window may hold.

`members` is passed in rather than recomputed so that the span is walked once, and so that the
test is a plain `if` over its arguments — which is all `acceptWindow_spec` has to invert. -/
def acceptWindow (cfg : SuperOptConfig) (n : Nat) (sup : List Qubit) (members : List Gate)
    (revSpan : Span) : Option Win :=
  if sup.length ≤ cfg.maxQubits && members.length ≤ cfg.maxWindow && membersOk n members then
    some ⟨sup, members, revSpan⟩
  else none

/-- Extend a window by the gate it just touched, re-closing it over its wires.

`none` when the result is out of bounds, or when closing would have to absorb a gate the
window may not hold — a measurement, a reset, an `rz`, or a gate off the register. -/
def growWindow (cfg : SuperOptConfig) (n : Nat) (w : Win) (g : Gate) : Option Win :=
  (closeSpan (w.revSpan.length + 2) (widen w.support g.qubitsOf) ((g, true) :: w.revSpan)).bind
    fun p => acceptWindow cfg n p.1 (spanMembers p.2.reverse) p.2

/-- Grow a window through the gates that follow it, rewriting at the first hit. The result
replaces the whole consumed span *and* the gates after it. -/
def tryWindow (cfg : SuperOptConfig) (tbl : SynthTable) (n : Nat) (fm : Option FlatMat)
    (w : Win) (cnt : Nat) : List Gate → Option (List Gate × List Gate × List Gate × Nat)
  | [] => none
  | g :: rest =>
      if touches w.support g then
        match growWindow cfg n w g with
        | none => none
        | some w' =>
            -- The cheap filter first: only build the window's exact matrix when the table
            -- might actually answer for it (see `windowMayHold`).
            let fm' := extendFlat w'.support w'.members fm w g
            match trySynthFiltered tbl fm' w' with
            | some repl => some (repl, w'.skipped, rest, cnt + 1)
            | none => tryWindow cfg tbl n fm' w' (cnt + 1) rest
      else
        tryWindow cfg tbl n fm ⟨w.support, w.members, (g, false) :: w.revSpan⟩ (cnt + 1) rest

/-- The tail a rewrite leaves is a suffix of what the window was scanning, so a sweep that
continues from it makes progress. -/
theorem tryWindow_tail_le {cfg : SuperOptConfig} {tbl : SynthTable} {n : Nat} :
    ∀ (rest : List Gate) (fm : Option FlatMat) (w : Win) (cnt : Nat)
      (repl sk tail : List Gate) (k : Nat),
      tryWindow cfg tbl n fm w cnt rest = some (repl, sk, tail, k) →
        tail.length ≤ rest.length := by
  intro rest
  induction rest with
  | nil => intro fm w cnt repl sk tail k h; rw [tryWindow] at h; exact absurd h (by simp)
  | cons g rest ih =>
      intro fm w cnt repl sk tail k h
      rw [tryWindow] at h
      split at h
      · split at h
        · exact absurd h (by simp)
        · dsimp only at h
          split at h
          · rw [Option.some.injEq] at h
            obtain ⟨-, -, rfl⟩ := h
            simp
          · exact le_trans (ih _ _ _ _ _ _ _ h) (by simp)
      · exact le_trans (ih _ _ _ _ _ _ _ h) (by simp)

/-- Whether a gate may anchor a window. -/
def canAnchor (cfg : SuperOptConfig) (n : Nat) (g : Gate) : Bool :=
  isWindowGate g && g.qubitsOf.length ≤ cfg.maxQubits &&
    g.qubitsOf.all (fun q => q < n) && decide g.Wf

/-- One sweep: rewrite every window that claims a replacement, **continuing past each one**
rather than restarting.

The old shape found a single rewrite and re-scanned the circuit from the top, which is
`O(rewrites × gates)` — measured at 25 s on a circuit with 256 of them, against Rust's 0.012 s.
Rust collects every non-overlapping rewrite in one scan and applies them together; continuing
from the tail a rewrite leaves is the same idea, and each rewrite is still justified on its own
by `tryWindow_correct`, so the correctness argument composes by transitivity. -/
def sweepOnce (cfg : SuperOptConfig) (tbl : SynthTable) (n : Nat) (gs : Array Gate)
    (tracks : Array (Array Nat)) : Nat → Nat → List Gate → List Gate
  | 0, _, gs => gs
  | _ + 1, _, [] => []
  | fuel + 1, at_, g :: rest =>
      if canAnchor cfg n g && anchorMayFire cfg tbl n gs tracks at_ then
        match tryWindow cfg tbl n
            (FlatMat.ofGates (Win.start g).support.length
              (localizeGates (Win.start g).support (Win.start g).members))
            (Win.start g) 0 rest with
        -- `tryWindow` hands back how many gates it consumed, so the index advances in `O(1)`.
        -- Recovering it from `tail.length` instead cost a walk of the whole remaining list on
        -- every rewrite, which was quadratic on its own.
        | some (repl, sk, tail, consumed) =>
            repl ++ sk ++ sweepOnce cfg tbl n gs tracks fuel (at_ + 1 + consumed) tail
        | none => g :: sweepOnce cfg tbl n gs tracks fuel (at_ + 1) rest
      else g :: sweepOnce cfg tbl n gs tracks fuel (at_ + 1) rest

/-- Peephole superoptimization of a gate list over `n` wires: **one forward scan**, as
`SuperOpt::run` is one forward scan.

It used to sweep to its own fixpoint, which made a single explicit `--passes SuperOpt`
stronger than a single Rust invocation, and — in the default pipeline — meant the pass
exhausted itself before phase folding got another turn, where Rust interleaves one scan with
the other passes each round. Repetition is the driver's job (`runToFixpoint`, and the
`fixpointShrink` it models), not the pass's. -/
def superOptGates (cfg : SuperOptConfig) (tbl : SynthTable) (n : Nat) (gs : List Gate) :
    List Gate :=
  let arr := gs.toArray
  sweepOnce cfg tbl n arr (buildTracks n arr) gs.length 0 gs

/-- Peephole superoptimization of a circuit. -/
def superOpt (cfg : SuperOptConfig) (tbl : SynthTable) (c : Circuit) : Circuit :=
  c.withGates (superOptGates cfg tbl c.numQubits c.gates)

end TzapLean
