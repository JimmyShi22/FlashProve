-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/LotNo.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR THE
HONEST SIDE: K1's LOT's HONEST SIDE WITH THE NUMBER THAT A PLACE's FIRST NEW MESSAGE GETS MADE OFF A
LIST OF BLOCKS; THE LOT's PUBLIC TEST WITH THE NUMBERS'. Definitions with code, and statements by
unfolding.

  sidePlaces    the places of the side's own halves (dataSide, Honest/K1/LotData.lean); they do not
                hang on the numbers
  dataSideBy    the side with the numbers handed in as a function of the public part and the
                segments' records
  dataSideOn    THE SIDE OVER A LIST OF BLOCKS: the number at a place: how many oracle messages the
                blocks in front of it tell (firstNoAt, Honest/K1/FirstNo.lean)
  noFitsOn      A PUBLIC TEST: at each place at which the side stands the list has a block
                (firstNoFits)
  lotTestOn     THE LOT's PUBLIC TEST, WHOLE, WITH THE NUMBERS': lotSeatsOk (Honest/K1/LotData.lean)
                and noFitsOn
  dataSideBy_name, dataSideBy_places   the name is the lot's own field · place by place, in order,
                the halves' places are the places of the lot's own blocks
  sidePlaces_lot   the side's places are the lot's own blocks' places
  testOn_seats, testOn_no   pins: the whole test hands its two halves

WHICH LIST. The list is a letter here: whoever seats the lots hands in the list that is played.
Honest/K1/LotNoPure.lean lays the description's own.

Limits. S (the sizes that the first place's filling reads) and wit stay letters. WHERE THE LIST HAS
NO BLOCK AT A PLACE THE NUMBER IS 0, WHICH MEANS NOTHING: noFitsOn is the named public test beside
it: whoever states a law that spends a job's "first" at this side names it. THE PART AND THE HALF OF
A JOB ARE ONE VALUE AT EVERY NUMBER LAID INTO "first" (Honest/K1/FirstFree.lean), AND SO THE SIDES
HERE ARE ONE VALUE AT ALL NUMBERS AND ALL LISTS (Honest/K1/HalvesFree.lean): laws of files that
stand over this one; Honest/K1/PlaceFirstFree.lean sees it at two jobs' played rounds. SO THE SIDE's
VALUE HANGS ON NEITHER THE NUMBERS NOR THE LIST: A LAW "UNDER lotTestOn" DOES NOT TIE THE SIDE TO
THE LIST THAT IS PLAYED. The texts still name the number; of the two laws that tie the part's
answers to the chain's statement job_answers asks it, job_answers_free (FirstFree.lean) asks nothing
of it. That the chain's state holds just so many messages in front of a place is no statement of
this file. lotSeatsOk itself does not turn. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.LotData
import Johnson.Desc.ProofFile.Honest.K1.FirstNo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc

variable {V W X St Cl : Type}

/-- The places of the side's own halves. -/
def sidePlaces (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) : List Place :=
  ((dataSide (V := Unit) (W := PlaceIn ProofFile.Inst) (X := Unit) S id fun _ => 0).halves Z G).map
    (·.place)

/-- **K1's lot's honest side, the numbers handed in**: lotHalves (Honest/K1/PlaceJob.lean) at
lotData, with the number that a place's first new message gets as a function of the public part and
the segments' records too. -/
def dataSideBy (S : OnBytes.HonestTrace.Sz) (wit : W → PlaceIn ProofFile.Inst)
    (no : Pub → Ground → Place → Nat) : HLot V W X :=
  { name := (dataSide (V := V) (X := X) S wit fun _ => 0).name
    halves := fun Z G => lotHalves wit (no Z G) (lotData S) Z G }

/-- **THE SIDE OVER A LIST OF BLOCKS.** -/
def dataSideOn (S : OnBytes.HonestTrace.Sz) (wit : W → PlaceIn ProofFile.Inst)
    (bs : Pub → Ground → List (Block St Cl)) : HLot V W X :=
  dataSideBy S wit fun Z G => firstNoAt (bs Z G)

/-- **A PUBLIC TEST**: at each place at which the side stands the list has a block. -/
def noFitsOn (S : OnBytes.HonestTrace.Sz) (bs : Pub → Ground → List (Block St Cl)) (Z : Pub)
    (G : Ground) : Bool := firstNoFits (bs Z G) (sidePlaces S Z G)

/-- **THE LOT's PUBLIC TEST, WHOLE, WITH THE NUMBERS'**, at a public instance. -/
def lotTestOn (S : OnBytes.HonestTrace.Sz) (bs : Pub → Ground → List (Block St Cl)) (Z : Pub)
    (G : Ground) (x : ProofFile.Inst) : Bool := lotSeatsOk S Z G x && noFitsOn S bs Z G

theorem dataSideBy_name (S : OnBytes.HonestTrace.Sz) (wit : W → PlaceIn ProofFile.Inst)
    (no : Pub → Ground → Place → Nat) (quiet : K1.Quiet) (Z : Pub) :
    (dataSideBy (V := V) (X := X) S wit no).name = (K1.lotWith quiet Z).name := rfl

theorem dataSideBy_places (S : OnBytes.HonestTrace.Sz) (wit : W → PlaceIn ProofFile.Inst)
    (no : Pub → Ground → Place → Nat) (quiet : K1.Quiet) (Z : Pub) (G : Ground) :
    ((dataSideBy (V := V) (X := X) S wit no).halves Z G).map (·.place) =
      ((K1.lotWith quiet Z).own G).map (·.place) :=
  lotSide_places wit (no Z G) (lotData S) quiet Z G

theorem sidePlaces_lot (S : OnBytes.HonestTrace.Sz) (quiet : K1.Quiet) (Z : Pub) (G : Ground) :
    sidePlaces S Z G = ((K1.lotWith quiet Z).own G).map (·.place) :=
  dataSide_places S id (fun _ => 0) quiet Z G

theorem testOn_seats (S : OnBytes.HonestTrace.Sz) (bs : Pub → Ground → List (Block St Cl)) (Z : Pub)
    (G : Ground) (x : ProofFile.Inst) (h : lotTestOn S bs Z G x = true) : lotSeatsOk S Z G x = true := by
  unfold lotTestOn at h
  rw [Bool.and_eq_true] at h
  exact h.1

theorem testOn_no (S : OnBytes.HonestTrace.Sz) (bs : Pub → Ground → List (Block St Cl)) (Z : Pub)
    (G : Ground) (x : ProofFile.Inst) (h : lotTestOn S bs Z G x = true) : noFitsOn S bs Z G = true := by
  unfold lotTestOn at h
  rw [Bool.and_eq_true] at h
  exact h.2

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.dataSideBy_name
#print axioms ProofFile.Honest.K1.dataSideBy_places
#print axioms ProofFile.Honest.K1.sidePlaces_lot
#print axioms ProofFile.Honest.K1.testOn_seats
#print axioms ProofFile.Honest.K1.testOn_no
#print axioms ProofFile.Honest.K1.sidePlaces
#print axioms ProofFile.Honest.K1.dataSideBy
#print axioms ProofFile.Honest.K1.dataSideOn
#print axioms ProofFile.Honest.K1.noFitsOn
#print axioms ProofFile.Honest.K1.lotTestOn
