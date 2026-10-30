-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/OneSeat.lean: code switching: THE PREMISE M OF THE SECOND AND THE THIRD TIE AT
A PLACE (K2.MembersLike ms ⟨r.l, seatN⟩ (N.sent m 0), Tw/K2C/StringsNew.lean), AT THE ONE
seatN := seatNew N m r (K2Caller/SeatsOfN.lean; m the fourth tie's, the third tie's is m + 1): from
the test on the members at a code switch. Theorems with their proofs. NO SUB-PROTOCOL
IMPORTS THIS FILE.
  seatNew_byPlace       seatNew N m r is seatsByPlace (N.sent (m + 1) 0) r.l.length
                        (Johnson/Desc/Sound/MembersAtB.lean): by definition
  membersLike_seatNew   M at ms := msOf L: the four fields are new_of_B's four clauses
                        (K2Caller/MembersAtK2.lean)
  membersLike_plan      M at the composed meaning's members ms := P5T.msAtR Z rad, from membersPlanB
                        (K2Caller/MembersAtPlan.lean)
AT seatNew N m r STAND SO FAR: the fourth tie's hE (K2Caller/TieFourPadsAt.lean) and hN (seatNew_at)
· the second and third ties' M (here) · the third tie's hAt, field «seats» (Tw/K2C/SentByPlace.lean:
hS_seatNew). THE TESTS THAT IT COSTS, all on public data: numbersFit
(Johnson/Desc/First/Borders.lean; spent in TieFourPadsAt.lean) · membersK2B | membersPlanB ·
sentPlaceB.
LIMITS. NOT COVERED AT seatNew: the second and third ties' hσ (K2.SmpLike) · the law at a place's
hseat and the letter base of wordsMade | k2Piece · SeatFits. That the ties are spent at one N, m, p,
r and k is the assembler's matter: the third and the fourth tie are applied in two checks with
letters of their own. The test's value is a premise. No soundness is claimed. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.MembersAtPlan
import Johnson.Top.H0.K2Caller.SeatsOfN
import Johnson.Top.H0.Tw.K2C.StringsNew

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (MemberLists)
open VerifiableInference.Desc.Sound (msOf seatsByPlace)
open VerifiableInference.Desc.First (Numbers)

theorem seatNew_byPlace (N : Numbers) (m : ℕ) (r : SwRow) :
    seatNew N m r = seatsByPlace (N.sent (m + 1) 0) r.l.length := rfl

/-- **M at seatN := seatNew N m r**, at the members of plain lists. -/
theorem membersLike_seatNew {L : MemberLists} {kq : List (ℕ × ℕ)} {N : Numbers} {m : ℕ}
    {r : SwRow} (h : membersK2B L kq (N.sent (m + 1) 0) r = true) :
    K2.MembersLike (msOf L) ⟨r.l, seatNew N m r⟩ (N.sent (m + 1) 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := new_of_B h
  exact ⟨h2, h3, h4, h1⟩

/-- **M at the composed meaning's members.** -/
theorem membersLike_plan {Z : ProofFile.Pub} {rad : ℕ → ℕ → ℕ} {N : Numbers} {m : ℕ} {r : SwRow}
    (h : membersPlanB Z rad N (m + 1) r = true) :
    K2.MembersLike (P5T.msAtR Z rad) ⟨r.l, seatNew N m r⟩ (N.sent (m + 1) 0) :=
  membersLike_seatNew h

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.seatNew_byPlace
#print axioms VerifiableInference.Desc.First.K2Caller.membersLike_seatNew
#print axioms VerifiableInference.Desc.First.K2Caller.membersLike_plan
