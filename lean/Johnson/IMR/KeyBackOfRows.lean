-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/KeyBackOfRows.lean: THE KEY FILE's BACK AS EIGHT NAMED DEBTS: a ledger,
as a theorem. «The key file's back» is Key.keyDataAndDecisionOfPlannerAnswer X₀ lay m (Johnson/Desc/Key/Slot.lean): what
the key file's piece does behind the planner's return m.
For the statement «where the planner has returned, the key file's seat returns».

WHAT IS SAID.
  descOfMade_of_rows   from the three returns r1 · r2 · r3: Key.descriptionFromPlan m returns Key.descriptionFromSource X N P.
  pinned_of_rows       at the full size's key, from r8 · r8': the door's second test accepts.
  keyBack_of_rows      **Key.keyDataAndDecisionOfPlannerAnswer X₀ lay m returns, and returns the written data
                       writtenKFull with the description's own decision, FROM:**
    r1  Key.sourceOf m returns X             r2  Key.rangesNumbers m returns N
    r3  Key.laterPlaces m returns P          r4  (Key.descriptionFromSource X N P).planOk = true
    r5  (Key.descriptionFromSource X N P).wantedOk = true     r6  (Key.descriptionFromSource X N P).owedOk = true
    r7  each of the seven strings of parameter bytes has fewer than 2 ^ 64 bytes
    hk  the key of m's scan is the full size's (in scope it is: KeyInScope.lean's key_of_steps)
    r8  written out, the description's declared rounds are dryKeyFull     r8' its depth is 32
  keyBack_returns      so ∃ K, Key.keyDataAndDecisionOfPlannerAnswer X₀ lay m = .ok K: the piece's own end.
HOW. Calls alone: Key.laidOfMade_iff · laidOfDesc_iff (Johnson/Desc/Key/SlotIs.lean) · Key.asks_of
(AsksLaw.lean) · PlanWritten.data_of_pinnedKey (Johnson/Desc/Ok/PlanWritten/AtDesc.lean): so «the
data are made» is no debt of its own: it follows from r8 · r8'. X₀ and lay are free letters: the
door (Key.lawsAsk) reads neither.
What is not claimed. NOT ONE OF THE ROWS IS SHOWN, at any m: this file pays nothing: it says what is
owed. That the rows can be met together: NO MEMBER (by an evaluation each step
says yes at the stored full-size files). No soundness.

-/
import Johnson.Desc.Key.SlotIs
import Johnson.Desc.Key.AsksLaw
import Johnson.Desc.Ok.PlanWritten.AtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open VerifiableInference VerifiableInference.Desc
open Johnson.G (dryKeyFull writtenKFull)
open Johnson.G.OfPlan (Made writtenOf)

variable {m : Made} {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}

/-- From the three returns the key file's description is made. -/
theorem descOfMade_of_rows (r1 : Key.sourceOf m = .ok X) (r2 : Key.rangesNumbers m = .ok N)
    (r3 : Key.laterPlaces m = .ok P) : Key.descriptionFromPlan m = .ok (Key.descriptionFromSource X N P) := by
  unfold Key.descriptionFromPlan
  rw [r1, r2, r3]

/-- At the full size's key the door's second test accepts where the declared rounds, written out,
are the written ones and the depth is 32. -/
theorem pinned_of_rows {F : FileDescription Key.Xi} (hk : PlanWritten.keyOf m = PlanWritten.fullKey)
    (r8 : writtenOf "key file" F.roundsDeclaredByBlocks = .ok dryKeyFull) (r8' : F.tableDepth = 32) :
    PlanWritten.pinnedKeyAt m F = true := by
  unfold PlanWritten.pinnedKeyAt PlanWritten.descPinnedKey PlanWritten.descPinned
    PlanWritten.declPinned
  rw [if_pos hk]
  unfold PlanWritten.declIs
  rw [r8, r8']
  simp

/-- **The key file's back returns, from eight named debts.** -/
theorem keyBack_of_rows (X₀ : OnBytes.Model.Verify.Public) (lay : ByteArray)
    (r1 : Key.sourceOf m = .ok X) (r2 : Key.rangesNumbers m = .ok N)
    (r3 : Key.laterPlaces m = .ok P) (r4 : (Key.descriptionFromSource X N P).planOk = true)
    (r5 : (Key.descriptionFromSource X N P).wantedOk = true) (r6 : (Key.descriptionFromSource X N P).owedOk = true)
    (r7 : ∀ n : OnBytes.Model.Verify.ChainName, (m.p.chains.bytes n).size < 2 ^ 64)
    (hk : PlanWritten.keyOf m = PlanWritten.fullKey)
    (r8 : writtenOf "key file" (Key.descriptionFromSource X N P).roundsDeclaredByBlocks = .ok dryKeyFull)
    (r8' : (Key.descriptionFromSource X N P).tableDepth = 32) :
    Key.keyDataAndDecisionOfPlannerAnswer X₀ lay m =
      .ok (writtenKFull, ((Key.descriptionFromSource X N P).pull Key.keyInstanceOfOutOfDomainSample).run) := by
  have hp := pinned_of_rows hk r8 r8'
  have hd : (Key.descriptionFromSource X N P).data "key file" = .ok writtenKFull :=
    PlanWritten.data_of_pinnedKey hk hp
  exact (Key.laidOfMade_iff X₀ lay m _ _).2 ⟨_, descOfMade_of_rows r1 r2 r3,
    (Key.laidOfDesc_iff _ _ _).2 ⟨r4, r5, r6, hd, rfl⟩, Key.asks_of X₀ lay m _ _ r7 hp⟩

/-- The piece's own end. -/
theorem keyBack_returns (X₀ : OnBytes.Model.Verify.Public) (lay : ByteArray)
    (r1 : Key.sourceOf m = .ok X) (r2 : Key.rangesNumbers m = .ok N)
    (r3 : Key.laterPlaces m = .ok P) (r4 : (Key.descriptionFromSource X N P).planOk = true)
    (r5 : (Key.descriptionFromSource X N P).wantedOk = true) (r6 : (Key.descriptionFromSource X N P).owedOk = true)
    (r7 : ∀ n : OnBytes.Model.Verify.ChainName, (m.p.chains.bytes n).size < 2 ^ 64)
    (hk : PlanWritten.keyOf m = PlanWritten.fullKey)
    (r8 : writtenOf "key file" (Key.descriptionFromSource X N P).roundsDeclaredByBlocks = .ok dryKeyFull)
    (r8' : (Key.descriptionFromSource X N P).tableDepth = 32) : ∃ K, Key.keyDataAndDecisionOfPlannerAnswer X₀ lay m = .ok K :=
  ⟨_, keyBack_of_rows X₀ lay r1 r2 r3 r4 r5 r6 r7 hk r8 r8'⟩

end IM

#print axioms IM.descOfMade_of_rows
#print axioms IM.pinned_of_rows
#print axioms IM.keyBack_of_rows
#print axioms IM.keyBack_returns
