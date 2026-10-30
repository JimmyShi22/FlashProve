-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Johnson/Desc/First/Att/Door/Law/FillK5Keeper.lean: THREE OF K5Fill's SEVEN EQUATIONS (Johnson/Desc/First/Att/K05T2.lean: ledger · lookOut · callerIn · lookIn · linkFresh · freeAbove · leftOnB) AT TWO LAYERS COMPOSED: OURS OVER fillKeeper's (Johnson/Desc/First/FillKeeper.lean), WHATEVER LIES BENEATH: BY LEAN. Mathlib beneath (it names our laws' files).
import Johnson.Desc.First.Att.Door.Law.FillK5Tie
import Johnson.Desc.First.Att.Door.OwnersAreOurs
import Johnson.Desc.First.Att.Door.Law.DoorTie

set_option autoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First

variable {Pp W : Type} (d : K5Data) (nsOf : Nat → Option Nat) (Mg : Meaning Pp W) (π : Pp)

/-- K5Fill.ledger. -/
theorem layers_ledger (m : Nat) (s : S) :
    (fillK5 d (fillKeeper nsOf Mg)).pub (.ledger m) (π, s) = s.fork?.any VerifiableInference.Desc.K3.sizedB := rfl

/-- K5Fill.freeAbove, where the letter nsOf of fillKeeper answers the plan's number. -/
theorem layers_freeAbove {m n : Nat} (h : nsOf m = some n) (s : S) :
    (fillK5 d (fillKeeper nsOf Mg)).pub (.freeAbove m) (π, s) = Att.P.freeAboveB n s := by
  show ((nsOf m).any fun n => VerifiableInference.Desc.First.freeAboveB n s) = _
  rw [h]
  exact (keeper_freeAbove_is n s).trans (freeAboveB_is n s)

/-- K5Fill.callerIn. -/
theorem layers_callerIn {m first : Nat} (h : d.isAtt m = true) (hf : d.first? m = some first) (s : S) :
    (fillK5 d (fillKeeper nsOf Mg)).pub (.callerIn m) (π, s) = Att.P.k5CallerIn3 first s :=
  fillK5_is_callerIn d _ π h hf s

/-- The other way round (fillKeeper's over ours) the three hold too. -/
theorem layers'_ledger (m : Nat) (s : S) :
    (fillKeeper nsOf (fillK5 d Mg)).pub (.ledger m) (π, s) = s.fork?.any VerifiableInference.Desc.K3.sizedB := rfl

theorem layers'_freeAbove {m n : Nat} (h : nsOf m = some n) (s : S) :
    (fillKeeper nsOf (fillK5 d Mg)).pub (.freeAbove m) (π, s) = Att.P.freeAboveB n s := by
  show ((nsOf m).any fun n => VerifiableInference.Desc.First.freeAboveB n s) = _
  rw [h]
  exact (keeper_freeAbove_is n s).trans (freeAboveB_is n s)

theorem layers'_callerIn {m first : Nat} (h : d.isAtt m = true) (hf : d.first? m = some first) (s : S) :
    (fillKeeper nsOf (fillK5 d Mg)).pub (.callerIn m) (π, s) = Att.P.k5CallerIn3 first s :=
  fillK5_is_callerIn d Mg π h hf s

#print axioms layers_ledger
#print axioms layers_freeAbove
#print axioms layers_callerIn
#print axioms layers'_ledger
#print axioms layers'_freeAbove
#print axioms layers'_callerIn

end H2K5.Door
