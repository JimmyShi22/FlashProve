-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/LotNoAt.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: WHERE THE DESCRIPTION IS MADE, THE SIDE AT THE PURE SEAT's NUMBERS IS THE SIDE OVER
THE DESCRIPTION's OWN LIST. Three statements by unfolding, and a fourth by a call.

  lotNo_at      where onlineDescriptionFromPublicPart at the pure seat returns F: lotNo (Honest/K1/LotNoPure.lean) at a place
                is firstNoAt over F's first chain's flat list
  lotNoFits_at  there the numbers' public test is firstNoFits over that list, at the side's places
  dataSideNo_on   there the halves of dataSideNo are those of dataSideOn (Honest/K1/LotNo.lean) at
                that list
  dataSideNo_any   WITHOUT A PREMISE: the side at the pure seat's numbers is, as a value, the side
                over any list (by dataSideOn_any, Honest/K1/HalvesFree.lean)

Why. dataSideNo is typed as dataSideBy at lotNo, not as dataSideOn at a list: the types of a
description's state and claims are the description's own fields, so its list has no type that is
fixed in front. These three say that the two are one wherever the description is made.

Limits. Where the description is not made the first three say nothing. By the fourth the third's
premise is idle. The fourth says that two VALUES are one: the numbers themselves part (lotNo_at says
what they are). Of the folder Johnson/Goal/ nothing is called. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.LotNoPure
import Johnson.Desc.ProofFile.Honest.K1.HalvesFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc

variable {V W X St Cl : Type}

theorem lotNo_at (o : SecondHashFunctionArgument) (Z : Pub) (F : FileDescription Inst)
    (h : onlineDescriptionFromPublicPart Z (pureSeat o Z) = .ok F) (a : Place) :
    lotNo o Z a = firstNoAt F.first.blocksInOrder a := by
  unfold lotNo
  rw [h]
  rfl

theorem lotNoFits_at (S : OnBytes.HonestTrace.Sz) (o : SecondHashFunctionArgument) (Z : Pub) (G : Ground)
    (F : FileDescription Inst) (h : onlineDescriptionFromPublicPart Z (pureSeat o Z) = .ok F) :
    lotNoFits S o Z G = firstNoFits F.first.blocksInOrder (sidePlaces S Z G) := by
  unfold lotNoFits
  rw [h]
  rfl

theorem dataSideNo_on (S : OnBytes.HonestTrace.Sz) (wit : W → PlaceIn ProofFile.Inst) (o : SecondHashFunctionArgument)
    (Z : Pub) (G : Ground) (F : FileDescription Inst) (h : onlineDescriptionFromPublicPart Z (pureSeat o Z) = .ok F) :
    (dataSideNo (V := V) (X := X) S wit o).halves Z G =
      (dataSideOn (V := V) (X := X) S wit fun _ _ => F.first.blocksInOrder).halves Z G := by
  have e : lotNo o Z = firstNoAt F.first.blocksInOrder := funext (lotNo_at o Z F h)
  show lotHalves wit (lotNo o Z) (lotData S) Z G =
    lotHalves wit (firstNoAt F.first.blocksInOrder) (lotData S) Z G
  rw [e]

/-- Without a premise, by HalvesFree.lean: the side at the pure seat's numbers is the side over any
list. -/
theorem dataSideNo_any (S : OnBytes.HonestTrace.Sz) (wit : W → PlaceIn ProofFile.Inst) (o : SecondHashFunctionArgument)
    (bs : Pub → Ground → List (Block St Cl)) :
    dataSideNo (V := V) (X := X) S wit o = dataSideOn S wit bs :=
  (dataSideOn_any S wit bs fun Z _ => lotNo o Z).symm

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.lotNo_at
#print axioms ProofFile.Honest.K1.lotNoFits_at
#print axioms ProofFile.Honest.K1.dataSideNo_on
#print axioms ProofFile.Honest.K1.dataSideNo_any
