import TzapLean.ExactMat
import TzapLean.Locality

/-!
# `SuperOpt`: the Algorithm

A forward scan that carves out small *windows* — causally connected groups of gates on a few
wires — computes each window's exact matrix, and replaces it whenever a shorter gate list has
the same matrix. Nothing is matched syntactically: any identity expressible in the search
space is found without ever being written down.

This is `src/super_opt/mod.rs`, with two deliberate departures.

* **Where Rust looks up a precomputed synthesis table, this searches.** Rust builds a table of
  shortest circuits per matrix once per configuration and caches it on disk; here the pass
  enumerates candidate circuits shorter than the window and tests each. Same answer — the
  first hit in increasing length is a shortest equivalent — and no table to persist, at the
  price of doing the work per window. `maxSearch` caps the enumeration.
* **Skipped gates move to just after the replacement** rather than staying interleaved. They
  commute with every window gate, so this is invisible; it keeps the reconstruction to one
  list splice.

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
  /-- Longest replacement the search will consider. -/
  maxSearch : Nat := 2
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

/-! ## The search for a shorter equivalent -/

/-- The gate alphabet the search draws from, on `k` wires. -/
def localAlphabet (k : Nat) : List Gate :=
  (List.range k).flatMap
      (fun q => [Gate.h q, Gate.s q, Gate.sdg q, Gate.t q, Gate.tdg q, Gate.x q, Gate.z q]) ++
    (List.range k).flatMap (fun c =>
      (List.range k).filterMap (fun t => if c == t then none else some (Gate.cnot c t))) ++
    (List.range k).flatMap (fun c =>
      (List.range k).filterMap (fun t => if c < t then some (Gate.cz c t) else none))

/-- Every gate list of a given length over that alphabet. -/
def seqs (k : Nat) : Nat → List (List Gate)
  | 0 => [[]]
  | len + 1 => (seqs k len).flatMap fun gs => (localAlphabet k).map fun g => gs ++ [g]

/-- Whether a candidate is usable *and* really has the window's matrix, up to global phase.
This is the check the correctness proof consumes; the search that proposes candidates is
unverified, so everything the proof needs is re-established here. -/
def accepts {k : Nat} (target : ExactMat k) (cand : List Gate) : Bool :=
  cand.all (fun g => g.qubitsOf.all (fun q => q < k) && decide g.Wf) &&
    (match ExactMat.matrixOf k cand with
     | none => false
     | some N => (ExactMat.phaseMatch target N.normalize).isSome)

/-- The first candidate of length `len` that matches. -/
def searchLen {k : Nat} (target : ExactMat k) (len : Nat) : Option (List Gate) :=
  (seqs k len).find? (fun cand => accepts target cand)

/-- The shortest candidate of length at most `bound` that matches. -/
def search {k : Nat} (target : ExactMat k) : Nat → Option (List Gate)
  | 0 => searchLen target 0
  | bound + 1 =>
      match search target bound with
      | some cand => some cand
      | none => searchLen target (bound + 1)

/-- Rename a local circuit back to the window's physical wires. -/
def globalizeGate (S : List Qubit) : Gate → Gate := mapQubits (fun i => S.getD i 0)

/-- Look for a strictly shorter replacement for a window, verified before it is returned. -/
def trySynth (cfg : SuperOptConfig) (w : Win) : Option (List Gate) :=
  if w.members.length ≤ 1 then none
  else
    match ExactMat.matrixOf w.support.length (localizeGates w.support w.members) with
    | none => none
    | some M =>
        match search M.normalize (min cfg.maxSearch (w.members.length - 1)) with
        | none => none
        | some cand =>
            if accepts M.normalize cand && cand.length < w.members.length then
              some (cand.map (globalizeGate w.support))
            else none

/-! ## The scan -/

/-- Grow a window through the gates that follow it, rewriting at the first hit. The result
replaces the whole consumed span *and* the gates after it. -/
def tryWindow (cfg : SuperOptConfig) (n : Nat) (w : Win) : List Gate → Option (List Gate)
  | [] => none
  | g :: rest =>
      if touches w.support g then
        if isWindowGate g && g.qubitsOf.all (fun q => q < n) && decide g.Wf &&
            (widen w.support g.qubitsOf).length ≤ cfg.maxQubits &&
            w.members.length + 1 ≤ cfg.maxWindow &&
            !w.skipped.any (fun s => touches (widen w.support g.qubitsOf) s) then
          match trySynth cfg
              ⟨widen w.support g.qubitsOf, w.members ++ [g], w.skipped, w.consumed ++ [g]⟩ with
          | some repl => some (repl ++ w.skipped ++ rest)
          | none =>
              tryWindow cfg n
                ⟨widen w.support g.qubitsOf, w.members ++ [g], w.skipped, w.consumed ++ [g]⟩ rest
        else none
      else
        tryWindow cfg n ⟨w.support, w.members, w.skipped ++ [g], w.consumed ++ [g]⟩ rest

/-- Find and apply the first rewrite anywhere in the list. -/
def rewriteOnce (cfg : SuperOptConfig) (n : Nat) : List Gate → Option (List Gate)
  | [] => none
  | g :: rest =>
      if isWindowGate g && g.qubitsOf.length ≤ cfg.maxQubits &&
          g.qubitsOf.all (fun q => q < n) && decide g.Wf then
        match tryWindow cfg n (Win.start g) rest with
        | some out => some out
        | none => (rewriteOnce cfg n rest).map (g :: ·)
      else (rewriteOnce cfg n rest).map (g :: ·)

/-- Apply rewrites until none is found. -/
def superOptAux (cfg : SuperOptConfig) (n : Nat) : Nat → List Gate → List Gate
  | 0, gs => gs
  | fuel + 1, gs =>
      match rewriteOnce cfg n gs with
      | some gs' => superOptAux cfg n fuel gs'
      | none => gs

/-- Peephole superoptimization of a gate list over `n` wires. -/
def superOptGates (cfg : SuperOptConfig) (n : Nat) (gs : List Gate) : List Gate :=
  superOptAux cfg n gs.length gs

/-- Peephole superoptimization of a circuit. -/
def superOpt (cfg : SuperOptConfig) (c : Circuit) : Circuit :=
  { c with gates := superOptGates cfg c.numQubits c.gates }

end TzapLean
