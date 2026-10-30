-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/TestsAtS.lean: the tests behind the adding
(Johnson/Desc/First/Batch/Tests.lean) at the state that the proof file's first chain carries
(Johnson/Desc/First/State.lean: S): the lens; the place's numbers, of the public parameters alone;
and the two parameters as they are filled. Definitions with code; no theorem
(that `closedList` is the program `verify-on-bytes`'s test of that meaning:
Johnson/Desc/First/Batch/TestsAtSLaw.lean).

What is read of S: the open segment's ledger (fork?), the smallness test's state (tl?), the slot of
the merge's end value (`mergeOf`, Johnson/Desc/First/Batch/AtS.lean) and, by the counts, the tables
with their weights
(funs?). What is written: the ledger.

THE TWO PARAMETERS ARE OTHER KINDS' MATTER, TYPED OR NAMED HERE:
  `countsAt`: (2): the sorts' own counts (the layers', attention's, the head's): typed after
    `verify-on-bytes`'s lines (Layer.lean:633-634 · Attention.lean:232 · Head.lean:275-278).
  (3) is `First.Door.weightsE` (Johnson/Desc/First/Door/Sums.lean), BY NAME: the three plain
    functions of Johnson/Desc/First/TailClaims/ in `verify-on-bytes`'s order; a refusal bears its
    guard's name.
Limits: definitions; no law is stated here. The counts are typed after `verify-on-bytes`'s lines and
are held against them by runs alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.State
import Johnson.Desc.First.Batch.AtS
import Johnson.Desc.First.Batch.Tests
import Johnson.Desc.First.Door.Sums
import OnBytes.Model.VerifyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

/-- **The lens.** -/
def tAtS : TLens S where
  get? := fun s => do
    let F ← s.fork?
    let tl ← s.tl?
    pure { merge := mergeOf s, tl := tl, F := F }
  set := fun s G => s.putFork G

/-- The three sorts of segment. -/
inductive SegSort where
  | layers
  | attention
  | head
  deriving DecidableEq, Repr, Inhabited

/-- As many claims were added as the plan counts. -/
def claimsCounted (nLin : Nat) (s : S) : Bool := (s.fork?.map (·.nClaim == nLin)).getD false

/-- Two tables agree in their five fields. -/
def sameTable (a b : HFun) : Bool :=
  a.mat == b.mat && a.len == b.len && a.tree == b.tree && a.start == b.start && a.phi == b.phi

/-- The list funs is the list that the smallness test's record closed: that list is closed; the two
are as long; table by table they agree. IN THIS FILE's OWN WORDS: no test of `verify-on-bytes` is
called. -/
def closedList (tl : HTailF2) (funs : Array HFun) : Bool :=
  tl.funClosed && funs.size == tl.funs.size &&
    (List.range funs.size).all fun i => sameTable (funs.getD i {}) (tl.funs.getD i {})

/-- The list of tables is still the list that was closed. -/
def tablesHeld (s : S) : Bool :=
  match s.tl?, s.funs? with
  | some tl, some funs => closedList tl funs
  | _, _ => false

/-- (2), as it is filled. nLin: the plan's number of claims. -/
def countsAt (k : SegSort) (nLin : Nat) : List (String × (S → Bool)) :=
  match k with
  | .layers => [("K9.claims-counted", claimsCounted nLin), ("K9.tables-held", tablesHeld)]
  | .attention => [("K9.claims-counted", claimsCounted nLin), ("K9.tables-held", tablesHeld)]
  | .head =>
    [("K9.claims-counted", claimsCounted nLin),
     ("K9.matrix-drawn-once", fun s => (s.tl?.map (·.foldDrawn == 1)).getD false),
     ("K9.two-lookups", fun s => (s.tl?.map (1 + ·.groupsRun == 2)).getD false),
     ("K9.tables-held", tablesHeld)]

/-- The sort of segment i, the plan's number of claims, and the place's numbers, OF THE PUBLIC
RECORD ALONE. The split by i is that of the lookups' places
(Johnson/Desc/First/Look/LookAt.lean). -/
def testsWhere (X : Verify.Public) (i piece : Nat) : Option (SegSort × Nat × TWhere) :=
  let step := if X.p4 then 2 else 1
  if i == step * X.NGr then
    some (.head, X.H.nLin, ⟨1, i, piece, X.H.nMsg, X.H.nU⟩)
  else if i % step == 0 then
    X.G[i / step]?.map fun hp => (.layers, hp.nLin, ⟨1, i, piece, hp.used, hp.nU⟩)
  else
    X.A[i / step]?.map fun a => (.attention, a.nLin, ⟨1, i, piece, a.nMsg, a.seam.nU⟩)

/-- **The block at segment i.** -/
def testsAt {Cl : Type} (X : Verify.Public) (i piece : Nat) : Option (Block S Cl) :=
  (testsWhere X i piece).map fun w =>
    testsBehind tAtS w.2.2 (countsAt w.1 w.2.1) First.Door.weightsE

end VerifiableInference.Desc.K9
