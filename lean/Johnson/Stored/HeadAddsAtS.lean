-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Stored/HeadAddsAtS.lean.
WHAT IT IS. The output head's block at State.lean's S WITH ITS FOUR RUNS TYPED AT TRUE CLAIMS
(blockClaims; as a lot seats it: seatedClaims): a description that seats seatedClaims RUNS THIS TEXT
at the head's own rounds, and its batching gathers these runs' claims. Beside it, older: the head's
link's runs as two lists (frontAt, backAt; frontRuns, backRuns; segBlocks), for a seat that adds
claims in two steps of its own: where the batching's own block gathers a link's claims whole, nobody
calls these.
WHAT IT DOES NOT SHOW. Definitions alone. It adds nothing: whoever batches adds the list (addAll,
Desc/Claim.lean).
  frontAt: the lookup's "objects" · "guests" · K6's "norm" · "join" · "policy" · the lookup's
    "planes", at K6's readers.
  backAt: K6's "logits" · "the merge".
WHAT THE RUNS WANT OF THE RECORD. The lookup's four read S.lookHeard?, WHICH ONLY THE LOOKUP'S OWN
BLOCK LAYS (S.hearLook): behind a stand-in at H:3 they refuse "nothing was heard". K6's read what
K6's own block has laid at H:4 (x, squaresP), the heard token in S.out.reply, and the tables of
reads (t). "the merge" is K11's own run, by name: it reads the state of the merge's sumcheck that
the record holds (wo), which K11's own block or a stand-in lays at H:9.
A run's number of claims gathered so far starts at 0 in each step: none of these runs reads it.

-/
import Johnson.Stored.HeadSeatAt
import Johnson.Desc.Claim
import Johnson.Desc.First.Fork.MergeKind
import Johnson.Desc.First.Driver.Chain
import Johnson.Desc.First.Look.Via.Via

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head

open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

/-- A form, claimed to be 0, under its own number's weight. -/
def asClaim (f : Form) : Claim := { form := f }

/-- K6's block at S with true claims. -/
def blockClaims (W : Model.Verify.Public) (l : Nat) : Option (Block S Claim) :=
  (W.H.tl.ix.U.getD 2 none).map fun iU3 =>
    kindWithJoin (K3.seatCalls asClaim) (seatAt W.hS iU3) l 4
      (parOf W.hS ((Params.settingOf W.P.frame).workOf .field .request))

/-- **K6's block with true claims AS A LOT SEATS IT** (HeadSeatAt.lean: tested, laidOk, startOk;
seatedOf is the same at the unit type). -/
def seatedClaims (W : Model.Verify.Public) (l : Nat) (before : List (Nat × Nat)) :
    Option (Block S Claim) :=
  (blockClaims W l).map (tested (laidOk W) (startOk W) before)

/-- The lookup on the head's calls, with "planes" at K6's readers. Its runs alone are called here.
-/
def lookClaims (W : Model.Verify.Public) (l : Nat) : Option (Block S Claim) := do
  let iU3 ← W.H.tl.ix.U.getD 2 none
  let p ← First.Look.placeAt W l false
  pure (K3.withCaller (K3.seatCalls asClaim) p (callerReaders (planesAt iU3))
    (K3.Law.blockVia (K3.seatCalls asClaim) 3 #[] [] p []))

/-- "the merge": K11's own run (Johnson/Desc/First/Fork/MergeKind.lean: headMergeClaim), by name, in
a block of which the run alone is called here. -/
def mergeRun (l : Nat) : Block S Claim :=
  { (roundlessBlock "K11: its run of claims alone" 1 (some l) 9 .ok : Block S Claim) with
    claims := [("the merge", Johnson.Desc.First.ForkMerge.headMergeClaim)] }

/-- The two steps' rows: (the block's number in the segment, the run's name): THE DRIVER's OWN
(Johnson/Desc/First/Driver/Chain.lean: orderCuts): the first and the third stretch of the head's
order. No order is written here a second time. -/
def frontRow : List (Nat × String) := (First.orderCuts .head).getD 0 []

def backRow : List (Nat × String) := (First.orderCuts .head).getD 2 []

/-- The segment's blocks in front of the batching, under the driver's numbers (kindsBeforeBatching .head: K7,
K2, K3, K6, K1, K8, K1, K3, K11), AS FAR AS THESE TWO STEPS CALL THEIR RUNS: the calls' lookup at 2,
the head's own rounds at 3, the merge at 8; at every other number a block without a run: so too at 2
where the plan gives the lookup no place: "H.9.front" then finds no run "objects". l: the head's
link's number. -/
def segBlocks (W : Model.Verify.Public) (l : Nat) : Option (List (Block S Claim)) :=
  let q (i : Nat) : Block S Claim := roundlessBlock "no run of these two steps" 1 (some l) i .ok
  (blockClaims W l).map fun b6 =>
    [q 0, q 1, (lookClaims W l).getD (q 2), b6, q 4, q 5, q 6, q 7, mergeRun l]

def frontBlocks (W : Model.Verify.Public) (l : Nat) : Option (List (Block S Claim)) :=
  segBlocks W l

def backBlocks (W : Model.Verify.Public) (l : Nat) : Option (List (Block S Claim)) :=
  segBlocks W l

/-- **"H.9.front"**, gathered by Block.lean's claimsIn. -/
def frontAt (W : Model.Verify.Public) (l : Nat) : Option (S → Except String (List Claim × S)) :=
  (frontBlocks W l).map (claimsIn · frontRow)

/-- **"H.9.back"**. -/
def backAt (W : Model.Verify.Public) (l : Nat) : Option (S → Except String (List Claim × S)) :=
  (backBlocks W l).map (claimsIn · backRow)

/-- A named run of claims at S: the batching's seat's K9.RunOf S, written out. -/
abbrev RunAtS : Type := String × (Nat → S → Except String (List Claim × S))

/-- A row's runs, each with its name; nothing if a run is not there. -/
def runsOf (bs : List (Block S Claim)) (row : List (Nat × String)) : Option (List RunAtS) :=
  row.mapM fun o => (bs[o.1]?).bind fun b => (b.claims.lookup o.2).map (o.2, ·)

/-- The two steps as lists of named runs. -/
def frontRuns (W : Model.Verify.Public) (l : Nat) : Option (List RunAtS) :=
  (frontBlocks W l).bind (runsOf · frontRow)

def backRuns (W : Model.Verify.Public) (l : Nat) : Option (List RunAtS) :=
  (backBlocks W l).bind (runsOf · backRow)

end VerifiableInference.Desc.Kinds.Head
