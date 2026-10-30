-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/Claims.lean: how the honest side of the merge of the claims on the
weights (Honest/K11/Part.lean) makes the head's one claim: BY THE DESCRIPTION's OWN FUNCTION, called
by name: `First.Look.weightsClaim` (Johnson/Desc/First/Look/LookQuiet.lean). Definitions with code,
and two small theorems.

Why. The verifier's text reads the claim off its state, where the quiet step behind the lookup on
the digits at the head's link has laid it (`quietHead`, Johnson/Desc/First/Look/K3Whole.lean): that
step calls `weightsClaim` at public data, the covered positions, and what the head's rounds have
heard. A part is handed no state of the verifier's: it makes the same call of the public data, the
instance and the challenges heard.

Of what the head heard (`Head.Heard`, OnBytes/Model/HeadHeard.lean) that function reads four fields
and no other (`weightsClaim_reads`, by definition): each call's key point (`g1.zk`), the challenges
of the last token sumcheck's rounds over the positions (`tH.r`) and over the channels (`rs`), and
the token that is checked at each covered position (`win`). THESE FOUR ARE PARAMETERS, LEFT OPEN
HERE (`HeadHeardFour`): functions of the challenges heard and of the instance, to be supplied by
the honest sides of the kinds whose rounds draw them.

  `HeadHeardFour`       the four
  `heardOfFour`         what the head heard, blank but for four fields
  `headHeardAt`         the same at the four parameters
  `headRunAt`           the argument that `weightsClaim` is called at, laid as `quietHead` lays it
  `headMergeClaims`     the claims: that one; none where a test on the request or the claim refuses
  `headMergeLotAt`      the lot's honest side at these claims
  `weightsClaim_reads`  the function reads of its argument's `x` the four fields alone, and neither
                        the reads' tables, nor the number of the vector of reads in the list of
                        arrays, nor the residual stream's matrix
  `weightsClaim_reads_on`   of the covered positions it reads one field alone: which positions are
                        covered (`hOn`)

Limits. The covered positions are made here by the description's `coveredAt`
(Johnson/Desc/First/State.lean) of the request's words and THE ASKED TOKEN; the verifier's step
makes them by the same function of the words in its state and the reply that it has heard. Of them
`weightsClaim` reads `hOn` alone, which `coveredAt` makes of the words alone; the token enters
through one test: that it is an entry of the vocabulary. So what stays open there is less than the
whole: that the words in the verifier's state are the request's, and that the heard reply passes
that one test where the asked token does. Nothing here says either, nor that the four parameters'
fillings are what the hearing lays. A REFUSAL IS TURNED INTO "NO CLAIM", IN SILENCE: where
`coveredAt` or `weightsClaim` refuses, `headMergeClaims` is empty and the part sums nothing; by the
text `quietHead`, which calls the same two functions, refuses at the same arguments too. The public
data are read at `G.W`; the lookups' lot lays `quietHead` at `Z.p.X`
(Johnson/Desc/ProofFile/Lot/K3.lean): the two are one at a ground that `lettersBy` makes
(Johnson/Desc/ProofFile/Pub.lean); nothing in the types says so. Nothing is evaluated here: the
public data want the public files.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Part
import Johnson.Desc.First.Look.LookQuiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E)
open OnBytes.Model
open VerifiableInference.Desc.First (blankHeard)
open VerifiableInference.Desc.First.Look (weightsClaim)

/-- The four things that the head's claim on the weights reads of what the head heard. -/
structure HeadHeardFour where
  /-- each call's key point, of the lookup on the head's calls -/
  keys : List Fmt.Drawn → Array (Array E)
  /-- the challenges of the last token sumcheck's rounds over the positions, the first drawn first
  -/
  overPositions : List Fmt.Drawn → Array E
  /-- those of its rounds over the channels; entry v belongs to bit v -/
  overChannels : List Fmt.Drawn → Array E
  /-- the token that is checked at each covered position -/
  checked : Inst → Array Nat

/-- What the head heard, blank but for four fields. -/
def heardOfFour (keys : Array (Array E)) (overPositions overChannels : Array E)
    (checked : Array Nat) : Head.Heard :=
  { blankHeard with
    win := checked, g1 := { blankHeard.g1 with zk := keys }, tH := { r := overPositions }
    rs := overChannels }

/-- The same at the four parameters. heard: the challenges heard in front of the merge's place. -/
def headHeardAt (H : HeadHeardFour) (x : Inst) (heard : List Fmt.Drawn) : Head.Heard :=
  heardOfFour (H.keys heard) (H.overPositions heard) (H.overChannels heard) (H.checked x)

/-- The argument at which the claim is made, laid as the verifier's quiet step lays it; the reads'
tables are left empty. X: the public data. -/
def headRunAt (Z : Pub) (X : Verify.Public) (H : HeadHeardFour) (x : Inst)
    (heard : List Fmt.Drawn) : Except String Head.Run :=
  ((startS Z x.pub).coveredAt X.T X.P.h.V ((Verify.words32 x.y).getD 0 0).toNat).map fun cov =>
    { h := X.hS, L := X.HLy, b := Verify.borderOf X.y, hp := X.H, cov := cov
      x := headHeardAt H x heard, t := {}, iU3 := (X.H.tl.ix.U.getD 2 none).getD 0 }

/-- **The claims**: the one that the description's function makes; none where `coveredAt` or that
function refuses: the refusal's name is dropped. -/
def headMergeClaims (H : Pub → Ground → HeadHeardFour) (Z : Pub) (G : Ground) (x : Inst)
    (heard : List Fmt.Drawn) : List WsClaim :=
  match (headRunAt Z G.W (H Z G) x heard).bind fun R => weightsClaim R G.W.layers.wsLay with
  | .ok q => [q]
  | .error _ => []

/-- The lot's honest side at these claims. -/
def headMergeLotAt {W₀ Rc Tr X : Type} (H : Pub → Ground → HeadHeardFour)
    (weights : W₀ → Weights) : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  headMergeLot (headMergeClaims H) weights

/-- Of what the head heard the function reads four fields alone; of its argument it reads neither
the reads' tables, nor the number of the vector of reads in the list of arrays, nor the residual
stream's matrix. -/
theorem weightsClaim_reads (R : Head.Run) (lay : WsLay) (t : Head.Tables) (i : Nat)
    (b : Head.Border) :
    weightsClaim
      { R with x := heardOfFour R.x.g1.zk R.x.tH.r R.x.rs R.x.win, t := t, iU3 := i, b := b } lay =
      weightsClaim R lay := rfl

/-- Of the covered positions the function reads one field alone: which positions are covered. c: any
other covered positions. -/
theorem weightsClaim_reads_on (R : Head.Run) (lay : WsLay) (c : Head.Covered) :
    weightsClaim { R with cov := { c with hOn := R.cov.hOn } } lay = weightsClaim R lay := rfl

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.weightsClaim_reads
#print axioms ProofFile.Honest.K11.weightsClaim_reads_on
#print axioms ProofFile.Honest.K11.HeadHeardFour
#print axioms ProofFile.Honest.K11.heardOfFour
#print axioms ProofFile.Honest.K11.headHeardAt
#print axioms ProofFile.Honest.K11.headRunAt
#print axioms ProofFile.Honest.K11.headMergeClaims
#print axioms ProofFile.Honest.K11.headMergeLotAt
