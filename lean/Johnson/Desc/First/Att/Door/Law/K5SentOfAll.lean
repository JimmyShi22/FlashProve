-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5SentOfAll.lean: kind K5 (an attention segment's own rounds): THE FIELD sent OF THE KIND's NAMED CONDITION (K5LeftOfCond.lean: K5Tests.sent; K5Rest's field of that name, K5AtMgPaid.lean) FROM THE TEST ON THE SEATS ASKED AT EVERY MEMBER OF THE CALLS' LIST.

Why. seatsPlanB (Johnson/Desc/First/Att/K05OwnersSent.lean) asks three things of each pair (number, seat); the third: the seat stands in the list own. At the pairs of ALL members (psOf l seat (List.range l.length), Johnson/Desc/First/Att/K05ReadMsgs.lean) that third clause is the field sent, where own is the segment's first sending.

Main names:
  **`sent_of_all`**: the test at every member ⊢ every member's seat lies in own. General in every letter.
Is it empty here? An implication from a Bool. That Bool is SHOWN at nothing here; by an evaluation (no proof) it says yes at all twelve groups at the library's written full-size values.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05OwnersSent
import Johnson.Desc.First.Att.K05ReadMsgs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes
open VerifiableInference.Desc.First.Att.P (psOf ps_mem seatsPlanB)
open VerifiableInference.Desc.First.FillSent (SentData)
open VerifiableInference.Desc.K12.Door (Laid)

/-- **Every member's seat lies in own.** -/
theorem sent_of_all {d : SentData} {m kept : ℕ} {Ld : Laid} {own : List (ℕ × ℕ)} {n : ℕ} (l : List (OracleShape × ℕ))
    (seat : Fin l.length → ℕ × ℕ) (h : seatsPlanB d m kept Ld (psOf l seat (List.range l.length)) own n = true)
    (i : Fin l.length) : seat i ∈ own := by
  unfold seatsPlanB at h
  have h1 := List.all_eq_true.1 h (i.val, seat i) (ps_mem l seat i (List.mem_range.2 i.2))
  obtain ⟨o, _, e2⟩ := (Option.any_eq_true _ _).1 h1
  rw [Bool.and_eq_true] at e2
  exact List.contains_iff_mem.1 e2.2

end H2K5.Door

#print axioms H2K5.Door.sent_of_all
