-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ClosingLinePayers.lean: CONDITIONAL on the head at the return.
Statements with their proofs; no definition.

What is here. FIVE SMALL PREMISES OF `k4_exchange_all_items`
(Honest/K4/Law/W/ExchangeAllItems.lean: the column hX of the frame's gathering at the members of
the feed-forward layers' own rounds, the sub-protocol K4), PAID AT THE FRAME's FIRST THREAD
(`firstThread`, Honest/Thread/TheFirstThread.lean), at each group g below 12.

  `marked_border_is_not_behind_k4`   hb₀: the thread's number 339 is not 28 g + 5.
  `k4_member_and_public_data`   Lh and hPG: the member's parameters, and the lot's public data of
      the group, under the head at the return.
  `rounds_of_two_members_stand_in_front`   hN, hNm, hNi at the number of rounds of the chain's first
      two members, and at 0.
  `k4_keeps_the_stored_tables`   hKs: what the thread's `keeps` says at K4's border leaves the
      field st of the verifier's state as it was.

The steps. `laid_at` (Law/LaidAtGroup.lean) · `k4PubG_of` (Law/W/PubGOf.lean) with `k4Pub_head`
(Law/FrontCount.lean) · `roundsTo_mono` (Honest/Thread/ScriptFit.lean) · `head_keeps`
(Honest/Thread/FirstHead.lean) at the written place (`k4_written_place_at_border`,
Law/BehindColumns.lean), `k4KeepsM_of_firstClauses` (Law/RidesPastAtFirstThread.lean) and the field
st of `Rest` (Johnson/Desc/First/K4/ReadsAtS.lean).

Limits. Public facts and one clause of `keeps`. Nothing on what is sent. THE FULL SIZE ALONE, at the
format's second hash function alone. A LAW, NOT A PART.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.RidesPastAtFirstThread
import Johnson.Desc.ProofFile.Honest.K4.Law.BehindColumns
import Johnson.Desc.ProofFile.Honest.K4.Law.W.PubGOf
import Johnson.Desc.ProofFile.Honest.K4.Law.TableFitsMember
import Johnson.Desc.ProofFile.Honest.Thread.ScriptFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (Place KindName Chain Block)
open P5J (TS)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts firstClauses firstLetters firstThread
  head_keeps)
open ProofFile.Honest.K4.SeatedHead (LaidK4 laid_at)

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- hb₀. **The number 339 is the border behind no member of K4.** -/
theorem marked_border_is_not_behind_k4 {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) : 339 ≠ k + 1 := by
  have e := Lh.num
  omega

/-- Lh and hPG. CONDITIONAL on h. **The member of group g, and the lot's public data there.** -/
theorem k4_member_and_public_data (h : HeadAtReturn files A) {g : ℕ} (hg : g < 12) :
    ∃ x blk, LaidK4 A.Z h.firstChain (28 * g + 4) (2 * g) g x blk ∧
      Lot.k4PubG A.Z g = some (k4PubAt h.firstChain (28 * g + 4) x) := by
  obtain ⟨x, blk, Lh⟩ := laid_at h.head hg
  exact ⟨x, blk, Lh, W.k4PubG_of Lh (k4Pub_head h.head Lh)⟩

/-- hN, hNm, hNi. **The rounds of the chain's first two members stand in front of every member of
K4**; and so does none. -/
theorem rounds_of_two_members_stand_in_front {S Cl : Type} (bs : List (Block S Cl)) (g : ℕ) :
    roundsTo bs 2 ≤ roundsTo bs (28 * g + 4) ∧ 0 ≤ roundsTo bs (28 * g + 4) :=
  ⟨roundsTo_mono bs 2 (28 * g + 4) (by omega), Nat.zero_le _⟩

/-- hKs. CONDITIONAL on h. **At K4's border `keeps` leaves the field st as it was.** -/
theorem k4_keeps_the_stored_tables (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (w : Local W₀ Rc ProofFile.Inst Tr) {g : ℕ} (hg : g < 12) (s s' : TS)
    (hk : (firstThread h parts w).keeps (28 * g + 4) s s') : s'.st = s.st := by
  have hk' : (firstLetters h parts w).keeps (28 * g + 4) s s' := hk
  unfold firstLetters at hk'
  have hc := (head_keeps h.head _ _ _ _ _ _ _ _ _ _ _ w (k4_written_place_at_border hg) s s').1 hk'
  have hc' : firstClauses h KindName.K4 (IM.k4Place g) s s' :=
    (kpBy_at (firstClauses h) (rfl : (IM.k4Place g).kind = KindName.K4) s s').1 hc
  exact (k4KeepsM_of_firstClauses h _ s s' hc').1.1.st

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.marked_border_is_not_behind_k4
#print axioms ProofFile.Honest.K4.k4_member_and_public_data
#print axioms ProofFile.Honest.K4.rounds_of_two_members_stand_in_front
#print axioms ProofFile.Honest.K4.k4_keeps_the_stored_tables
