-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/LotNoPure.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: K1's LOT's HONEST SIDE WITH THE NUMBERS OFF THE DESCRIPTION's OWN LIST. Definitions
with code, and statements by unfolding.

  lotNo         the number at a place, off the flat list of the first chain of the description that
                the library makes of the public part (onlineDescriptionFromPublicPart at pureSeat,
                Johnson/Desc/ProofFile/OnlineDescriptionFromBlockTables.lean, OnlineDescription.lean: what onlineDescription makes behind the
                three public files); o: the format's second hash function, a letter there too
  lotNoFits     A PUBLIC TEST: the description is made, and at each place at which the side stands
                its list has a block
  dataSideNo    THE SIDE AT THESE NUMBERS (dataSideBy, Honest/K1/LotNo.lean)
  lotTestOk     THE LOT's PUBLIC TEST, WHOLE, WITH THE NUMBERS': lotSeatsOk and lotNoFits
  dataSideNo_name, dataSideNo_places   as dataSideBy's
  testOk_seats, testOk_no   pins: the whole test hands its two halves

Limits. THE SIDE MAKES THE DESCRIPTION ANEW, BY ITS OWN CALL: if the lots are seated over another
seat than pureSeat o Z the numbers speak of a list that is not the one played:
Honest/K1/LotNo.lean's dataSideOn takes the list as a letter. WHERE THE DESCRIPTION IS NOT MADE
lotNo IS 0 AT EVERY PLACE, WHICH MEANS NOTHING: lotNoFits says no there. Each reading of lotNo makes
the whole description: dear for an evaluator. BY Honest/K1/HalvesFree.lean, A FILE THAT STANDS OVER
THIS ONE's GROUND, THE SIDE's VALUE HANGS ON NEITHER THE NUMBERS NOR A LIST: A LAW "UNDER lotTestOk"
DOES NOT TIE THE SIDE TO THE DESCRIPTION's LIST; the test guards a number that enters nothing that
is sent (Honest/K1/FirstFree.lean). Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.LotNo
import Johnson.Desc.ProofFile.OnlineDescription

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc

variable {V W X : Type}

/-- **The number at a place, off the description's own list.** -/
def lotNo (o : SecondHashFunctionArgument) (Z : Pub) (a : Place) : Nat :=
  ((onlineDescriptionFromPublicPart Z (pureSeat o Z)).toOption.map fun F => firstNoAt F.first.blocksInOrder a).getD 0

/-- **A PUBLIC TEST**: the description is made, and at each place at which the side stands its list
has a block. -/
def lotNoFits (S : OnBytes.HonestTrace.Sz) (o : SecondHashFunctionArgument) (Z : Pub) (G : Ground) : Bool :=
  (onlineDescriptionFromPublicPart Z (pureSeat o Z)).toOption.any fun F => firstNoFits F.first.blocksInOrder (sidePlaces S Z G)

/-- **THE SIDE AT THESE NUMBERS.** -/
def dataSideNo (S : OnBytes.HonestTrace.Sz) (wit : W → PlaceIn ProofFile.Inst) (o : SecondHashFunctionArgument) :
    HLot V W X := dataSideBy S wit fun Z _ => lotNo o Z

/-- **THE LOT's PUBLIC TEST, WHOLE, WITH THE NUMBERS'**, at a public instance. -/
def lotTestOk (S : OnBytes.HonestTrace.Sz) (o : SecondHashFunctionArgument) (Z : Pub) (G : Ground)
    (x : ProofFile.Inst) : Bool := lotSeatsOk S Z G x && lotNoFits S o Z G

theorem dataSideNo_name (S : OnBytes.HonestTrace.Sz) (wit : W → PlaceIn ProofFile.Inst) (o : SecondHashFunctionArgument)
    (quiet : K1.Quiet) (Z : Pub) :
    (dataSideNo (V := V) (X := X) S wit o).name = (K1.lotWith quiet Z).name := rfl

theorem dataSideNo_places (S : OnBytes.HonestTrace.Sz) (wit : W → PlaceIn ProofFile.Inst)
    (o : SecondHashFunctionArgument) (quiet : K1.Quiet) (Z : Pub) (G : Ground) :
    ((dataSideNo (V := V) (X := X) S wit o).halves Z G).map (·.place) =
      ((K1.lotWith quiet Z).own G).map (·.place) :=
  dataSideBy_places S wit (fun Z _ => lotNo o Z) quiet Z G

theorem testOk_seats (S : OnBytes.HonestTrace.Sz) (o : SecondHashFunctionArgument) (Z : Pub) (G : Ground)
    (x : ProofFile.Inst) (h : lotTestOk S o Z G x = true) : lotSeatsOk S Z G x = true := by
  unfold lotTestOk at h
  rw [Bool.and_eq_true] at h
  exact h.1

theorem testOk_no (S : OnBytes.HonestTrace.Sz) (o : SecondHashFunctionArgument) (Z : Pub) (G : Ground)
    (x : ProofFile.Inst) (h : lotTestOk S o Z G x = true) : lotNoFits S o Z G = true := by
  unfold lotTestOk at h
  rw [Bool.and_eq_true] at h
  exact h.2

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.dataSideNo_name
#print axioms ProofFile.Honest.K1.dataSideNo_places
#print axioms ProofFile.Honest.K1.testOk_seats
#print axioms ProofFile.Honest.K1.testOk_no
#print axioms ProofFile.Honest.K1.lotNo
#print axioms ProofFile.Honest.K1.lotNoFits
#print axioms ProofFile.Honest.K1.dataSideNo
#print axioms ProofFile.Honest.K1.lotTestOk
