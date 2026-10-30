-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Beside the table. Johnson/Desc/First/Att/Door/OwnersAreOurs.lean: «the owner's Bool at an attention segment is K5's»: against the table's files' own layer (Johnson/Desc/First/FillKeeper.lean): ledger · freeAbove. No Mathlib. The lookups' three (lookIn · lookOut · linkFresh) are not treated here.
import Johnson.Desc.First.FillKeeper
import Johnson.Desc.First.Att.Door.DoorItems

set_option autoImplicit false

namespace H2K5.Door
open VerifiableInference.Desc.First

/-- The test on the ledger in Johnson/Desc/First/FillKeeper.lean (ledgerB) is K5's laws' letter. -/
theorem keeper_ledger_is (s : S) : ledgerB s = s.fork?.any VerifiableInference.Desc.K3.sizedB := rfl

/-- The test "free above, n slots" in Johnson/Desc/First/FillKeeper.lean (freeAboveB) is K5's laws' letter (the two conjuncts stand the other way round). -/
theorem keeper_freeAbove_is (n : Nat) (s : S) : VerifiableInference.Desc.First.freeAboveB n s = Door.freeAboveB n s := by
  unfold VerifiableInference.Desc.First.freeAboveB Door.freeAboveB freeFromB
  cases s.fork? with
  | none => rfl
  | some G => exact Bool.and_comm _ _

/-- So at the layer fillKeeper (Johnson/Desc/First/FillKeeper.lean), whatever lies beneath, ledger m is what K5's files offer (offerK5). (freeAbove m: offer_freeAbove,
Johnson/Desc/First/Att/Door/OfferIsLayer.lean [not in this library]: it wants that layer's letter nsOf m = (W.A[m / 2]?).map (·.ns).) -/
theorem keeper_offer_ledger {P W : Type} (nsOf : Nat → Option Nat) (Mg : Meaning P W) (links : List ModelPart)
    (Wv : OnBytes.Model.Verify.Public) (arrOf : Nat → Array (Nat × String)) (ownOf : Nat → List (Nat × Nat)) (shape : OnBytes.Params.ReqShape) (m : Nat)
    (h : isAtt links m = true) (a : P × S) :
    offerK5 links Wv arrOf ownOf shape (.ledger m) a.2 = some ((fillKeeper nsOf Mg).pub (.ledger m) a) := by
  show (if isAtt links m then _ else _) = _
  rw [if_pos h]
  rfl

#print axioms keeper_ledger_is
#print axioms keeper_freeAbove_is
#print axioms keeper_offer_ledger

end H2K5.Door
