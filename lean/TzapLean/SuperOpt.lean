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

/-- A window under construction. -/
structure Win where
  /-- The wires the window covers. -/
  support : List Qubit
  /-- The window's gates, in order. -/
  members : List Gate
  /-- Gates of the span that the window skipped, in order. -/
  skipped : List Gate
  /-- The whole span consumed so far, in order — the gates a rewrite replaces. -/
  consumed : List Gate

/-- The window an anchor gate starts. -/
def Win.start (g : Gate) : Win where
  support := g.qubitsOf
  members := [g]
  skipped := []
  consumed := [g]

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

/-! ## The scan -/

/-- Grow a window through the gates that follow it, rewriting at the first hit. The result
replaces the whole consumed span *and* the gates after it. -/
def tryWindow (cfg : SuperOptConfig) (tbl : SynthTable) (n : Nat) (w : Win) : List Gate → Option (List Gate)
  | [] => none
  | g :: rest =>
      if touches w.support g then
        if isWindowGate g && g.qubitsOf.all (fun q => q < n) && decide g.Wf &&
            (widen w.support g.qubitsOf).length ≤ cfg.maxQubits &&
            w.members.length + 1 ≤ cfg.maxWindow &&
            !w.skipped.any (fun s => touches (widen w.support g.qubitsOf) s) then
          match trySynth tbl
              ⟨widen w.support g.qubitsOf, w.members ++ [g], w.skipped, w.consumed ++ [g]⟩ with
          | some repl => some (repl ++ w.skipped ++ rest)
          | none =>
              tryWindow cfg tbl n
                ⟨widen w.support g.qubitsOf, w.members ++ [g], w.skipped, w.consumed ++ [g]⟩ rest
        else none
      else
        tryWindow cfg tbl n ⟨w.support, w.members, w.skipped ++ [g], w.consumed ++ [g]⟩ rest

/-- Find and apply the first rewrite anywhere in the list. -/
def rewriteOnce (cfg : SuperOptConfig) (tbl : SynthTable) (n : Nat) : List Gate → Option (List Gate)
  | [] => none
  | g :: rest =>
      if isWindowGate g && g.qubitsOf.length ≤ cfg.maxQubits &&
          g.qubitsOf.all (fun q => q < n) && decide g.Wf then
        match tryWindow cfg tbl n (Win.start g) rest with
        | some out => some out
        | none => (rewriteOnce cfg tbl n rest).map (g :: ·)
      else (rewriteOnce cfg tbl n rest).map (g :: ·)

/-- Apply rewrites until none is found. -/
def superOptAux (cfg : SuperOptConfig) (tbl : SynthTable) (n : Nat) : Nat → List Gate → List Gate
  | 0, gs => gs
  | fuel + 1, gs =>
      match rewriteOnce cfg tbl n gs with
      | some gs' => superOptAux cfg tbl n fuel gs'
      | none => gs

/-- Peephole superoptimization of a gate list over `n` wires. -/
def superOptGates (cfg : SuperOptConfig) (tbl : SynthTable) (n : Nat) (gs : List Gate) :
    List Gate :=
  superOptAux cfg tbl n gs.length gs

/-- Peephole superoptimization of a circuit. -/
def superOpt (cfg : SuperOptConfig) (tbl : SynthTable) (c : Circuit) : Circuit :=
  { c with gates := superOptGates cfg tbl c.numQubits c.gates }

end TzapLean
