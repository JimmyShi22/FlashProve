-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/K11.lean: THE MERGE's LOT FOR THE FOLD OVER BLOCKS: ITS ONE BLOCK ALONE:
no control row; no weakened or planted text is imported.
It lays the kind's block at its place in the proof file's description: definitions with code; no
theorem.
Over LotCore.lean at Cl := VerifiableInference.Desc.Claim (a control's two lists of blocks stand at
Cl too).
THE LOT's STEPS: H.8.call · H.8.quiet: THE WHOLE PLACE «H:9»: no stand-in's half. letters := false,
written out: no token is read.
THE BLOCK COMES IN hearC, AS THE KIND MAKES IT (headClaimMergeKind), WITH ITS ONE LIST OF CLAIMS STATED,
TYPED AT Claim, UNDER THE DRIVER's NAME «the merge»; it states no run behind the batching. own :=
none.
withDecide: the kind's block with another decide, ITS LIST STATED AS THE KIND STATES IT: for the
control rows' tables; blk: the kind's block itself.
parOf reads ONE number off the declared rounds (Z.D): «sent»: how many oracle messages the first
chain has sent in front of the place.
WHERE THE TABLE OF `verify-on-bytes`'s STEPS HAS NO STEP OF THE NAME THAT IS LOOKED FOR
(«H.8.call») that number cannot be made: sentAt? says none, and THE BLOCK STANDS WITH A TEST ON THE
PLAN THAT IS FALSE (blkAt): the description refuses in front of the folds. No count is taken in
silence.
-/
import Johnson.Desc.ProofFile.LotCore
import Johnson.Desc.First.Fork.MergeKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace K11
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First
open Johnson.Desc.First.ForkMerge

/-- How many oracle messages the first chain's declared rounds send in front of `verify-on-bytes`'s
step of the name look; none where the table has no step of that name. -/
def sentAt? (Z : ProofFile.Pub) (look : String) : Option Nat :=
  (Z.roundsBefore? look).map fun k => (Z.D.1.take k).foldl (fun n r => n + r.entry.roots) 0

/-- The place's numbers, with «sent» counted in front of the step look (0 where it is not found:
blkAt refuses there). -/
def parAt (Z : ProofFile.Pub) (look : String) (G : ProofFile.Ground) : HeadMergeP :=
  { link := G.built.size - 1, piece := 9, lay := G.W.layers.wsLay
    work := (Params.settingOf G.W.P.frame).workOf .field .request
    sent := (sentAt? Z look).getD 0
    ncl := G.W.H.NCL, nMsg := G.W.H.nMsg, nLin := G.W.H.nLin }

/-- The place's numbers: out of the public files' records and the declared rounds alone. -/
def parOf (Z : ProofFile.Pub) (G : ProofFile.Ground) : HeadMergeP := parAt Z "H.8.call" G

/-- The kind's block with another decide; all else, its one list of claims too, as the kind states
it. -/
def withDecide (d : HeadMergeP → S → List Fmt.RoundView → Except String S) (P : HeadMergeP) :
    Block S Claim :=
  { headClaimMergeKind P with decide := fun s rs _ => d P s rs }

def blk (P : HeadMergeP) : Block S Claim := headClaimMergeKind P

/-- The kind's block at the place's numbers; where the step look is not found, its test on the plan
is false. -/
def blkAt (Z : ProofFile.Pub) (look : String) (G : ProofFile.Ground) : Block S Claim :=
  { blk (parAt Z look G) with
    planOk := (blk (parAt Z look G)).planOk && (sentAt? Z look).isSome }

def lot (Z : ProofFile.Pub) : ProofFile.Lot :=
  { name := "the merge of the weights' claims"
    letters := false
    own := fun _ => []
    hearC := fun G => [blkAt Z "H.8.call" G]
    controls := [] }

end K11
