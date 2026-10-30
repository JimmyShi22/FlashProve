-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ParseFull.lean: a parser that fills whole paths with real values, for a wiring with whole paths.

Why. The compiled verifier (`Compile.Batch.verifyOneProtocol`, the function that the compiler's verifier runs
on each proof string) checks openings of Merkle trees in one of two ways, by a flag of the wiring
(`ProtocolQueryLayout`, Iop/BatchWire.lean). With pruned openings (the flag set): one pruned walk for each opened
tree. With whole paths (no flag), the form of the wirings in the compiler's top theorems: it climbs
a whole path for each opened leaf. A file by the format page holds the pruned set alone: a sibling
that lies on another opened leaf's way is computed, not given. So for that form the parser has to
compute: it hashes the opened leaves and walks. The reader and the parser are generic in a monad and
in the hash (h is their first argument).

1. What the file contains.  Definitions that can be evaluated.
    `fullOpens h cfg P ..`: the openings after one draw: parsed, leaves hashed, the walk made
      (Fmt/Rules7.lean: `readOpeningW`: "seen" holds every vertex met, given or computed). The root
      in which the walk ends is compared with nothing.
    `fullWhole h S b`: the fold of Run/ParseLax.lean (`cutWhole`: no test of work) at this reader.
    `pathFrom a seen x`: the whole path of the leaf x, looked up in seen; none if a sibling's value
      is missing.
    `toBPrfFull T o`: as `toBPrf` (Run/ParseChain.lean), with these paths.
    `parseFullW h S T file`: the parser.

   Who checks what. The parser compares no root and makes no test of work. The verifier climbs every
   path itself, from its own leaf query, to the root that was sent: unless the hash collides, a
   wrong column, salt or given digest gives paths that do not end there; no theorem of this file
   says so, and `Typing` (Run/ParseChain.lean) asks nothing of `sym` and `place`. What the parser
   computes is a function of the file and the hash: it can make the verifier refuse, it cannot make
   it accept what it would not accept on these paths.

2. What is checked when the file compiles.  Five tests (#guard).

3. Theorems.  None.

4. What is not claimed.  See "Who checks what".
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.ParseLax

namespace Run
open Iop Rom Compile Compile.Batch
open _root_.Fmt (Plan Src OpenOut Spec ChainOut)

section
variable {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

/-- The openings after one draw: read and walked; no root is compared. -/
def fullOpens (cfg : ByteArray) (P : Plan) (b : ByteArray) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List Nat) :
    List (_root_.Fmt.Shape × Src) → Nat →
    m (Option (List (_root_.Fmt.Shape × List Nat × OpenOut) × Nat))
  | [], i => pure (some ([], i))
  | (sh, src) :: os, i =>
    let start : Option ByteArray :=
      match src with
      | .own n => if (roots[n]?).isSome then run else none
      | .given _ s => some s
    match start with
    | none => pure none
    | some st => do
      let xs := _root_.Fmt.listOf (poss.map (· % 2 ^ sh.a))
      match ← _root_.Fmt.readOpeningW h cfg P.field P.salt sh st xs b i with
      | none => pure none
      | some o =>
        match ← fullOpens cfg P b run roots poss os o.next with
        | none => pure none
        | some (l, k) => pure (some ((sh, xs, o) :: l, k))

/-- The reader: `cutWhole` (Run/ParseLax.lean) at `fullOpens`. -/
def fullWhole (S : Spec) (b : ByteArray) : m (Option ChainOut) :=
  cutWhole h (fun b run roots poss os i => fullOpens h S.cfg S.plan b run roots poss os i) S b

end

/-- the value at a vertex -/
def seenAt (seen : List (Nat × Nat × ByteArray)) (d p : Nat) : Option ByteArray :=
  (seen.find? fun v => v.1 == d && v.2.1 == p).map fun v => v.2.2

/-- The whole path of the leaf x, from the leaves up. -/
def pathFrom (a : Nat) (seen : List (Nat × Nat × ByteArray)) (x : Nat) : Option (List (Dig 256)) :=
  (List.range a).mapM fun k => (seenAt seen (a - k) ((x / 2 ^ k) ^^^ 1)).map bytesToDig

/-- all openings of all rounds, each under its tree's number, with whole paths -/
def opensF (o : ChainOut) : Option (List (Nat × Nat × OpenB × List (List (Dig 256)))) :=
  (o.rounds.toList.flatMap fun r => r.opens).mapM fun x =>
    (x.2.1.mapM (pathFrom x.1.a x.2.2.seen)).map fun ps =>
      (x.1.tree, x.1.W, ⟨x.1.a, x.2.1, x.2.2.cols, x.2.2.salts, x.2.2.given⟩, ps)

/-- From what was read to two of the verifier's inputs, with whole paths. -/
def toBPrfFull {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (T : Typing Q) (o : ChainOut) :
    Option (List (Dig 256) × OneProtocolProof 256 Q) :=
  match o.run, T.plains o.rounds, opensF o with
  | some run, some pl, some ops =>
      if ops.all (fun x => x.2.2.1.ok T.saltBytes x.2.1) then
        some ([bytesToDig o.pd], mkBPrf Q run (rootsB o) pl fun p =>
          match ops.lookup (T.place p).1 with
          | none => none
          | some x => x.2.1.atP (T.sym p) run x.2.2 (T.place p).2)
      else none
  | _, _, _ => none

/-- The parser: the reader `fullWhole`, then `toBPrfFull`. -/
def parseFullW {m : Type → Type} [Monad m]
    (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) {Y : Type} {E : ExtSpec}
    {Q : BatchInteractiveOracleProof Y E} (S : Spec) (T : Typing Q) (file : ByteArray) :
    m (Option (List (Dig 256) × OneProtocolProof 256 Q)) := do
  let o ← fullWhole h S file
  pure (o.bind (toBPrfFull T))

/-! ## Guards, at the example file of Run/ParseChain.lean -/

namespace ParseEx

def full (c : UInt64 × UInt64 × UInt64) (b : ByteArray) : Option ChainOut :=
  fullWhole (m := Id) _root_.Fmt.formatHash (spec c) b

end ParseEx

-- on the honest file: the same `ParseEx.view` as the strict reader's output; three whole paths of
-- four digests; the first entries are the leaves' siblings, which are given here
#guard (ParseEx.full (1, 2, 3) ParseEx.file).map ParseEx.view == (ParseEx.strict (1, 2, 3) ParseEx.file).map ParseEx.view
#guard ((ParseEx.full (1, 2, 3) ParseEx.file).bind opensF).map (fun l => l.map fun x => x.2.2.2.map List.length) == some [[4, 4, 4]]
#guard ((ParseEx.full (1, 2, 3) ParseEx.file).bind opensF).map (fun l => l.map fun x => x.2.2.2.map fun p => (p.head?.map digToBytes)) == ((ParseEx.full (1, 2, 3) ParseEx.file).map fun o => (opensB o).map fun x => (x.2.2.given.take 3).map some)
-- the pruned set read off the whole paths is the file's
#guard ((ParseEx.full (1, 2, 3) ParseEx.file).bind opensF).map (fun l => l.map fun x => (Octopus.reads x.2.2.1.a (x.2.2.1.idx.zip x.2.2.2)).map digToBytes) == ((ParseEx.full (1, 2, 3) ParseEx.file).map fun o => (opensB o).map fun x => x.2.2.given)
-- a flipped byte of a column: read (no root is compared)
#guard (ParseEx.full (1, 2, 3) (ParseEx.flip ParseEx.file 72)).isSome

end Run
