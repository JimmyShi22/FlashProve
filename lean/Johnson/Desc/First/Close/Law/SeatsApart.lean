-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/SeatsApart.lean (kind K10): AT EVERY LINK's WRITTEN LIST THE MEMBERS'
NUMBERS IN THE WITNESS ARE ALL DIFFERENT, AND SO ARE THEIR SEATS: from one test with code; at the
written values of the full size by an evaluation in Lean's kernel. A definition with code, and
theorems.
Why. AgreeAtFa.lean's `fa_agree` and `fa_agree_seat` pay the pins' "the row's own members agree"
from two premises on the term for seat (`seatK10`, SeatsOfLink.lean): the numbers arr (seat i) are
different for different i; seat is injective. The numbering off the plan (`P5T.arrOf`,
Johnson/P5T/PlanSeats.lean) gives ONE number to an original and all its kept copies: so the first is
no matter of course.
  `numsApartB arr n seats`: as many seats as n, and no number twice. `num_inj_of_B`: **a yes gives
    the first premise, to the letter.** `seat_inj_of_num`: **the first gives the second.**
  `arrFull`: the numbering at the written seats of all three chains. `numsApart_full`: **the test
    says yes at every l < 26.** `numsApart_pair`: THE NEGATIVE LINE: the numbers of links 0 and 1 in
    a row are not all different (link 1 keeps messages of link 0).
  `num_inj_full`, `seat_inj_full`: the two premises at the written values, l < 26.
Limits. AT WRITTEN VALUES. That the composed meaning's numbering in scope is `arrFull` is another
file's. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.SeatsOfLink
import Johnson.P5T.PlanSeatsFull
import Johnson.G.LinkLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open OnBytes

/-- **As many seats as n, and no number twice.** -/
def numsApartB (arr : ℕ → ℕ → ℕ) (n : ℕ) (seats : List (ℕ × ℕ)) : Bool :=
  decide (seats.length = n) && decide ((seats.map fun q => arr q.1 q.2).Nodup)

/-- **WHAT A YES GIVES: different members bear different numbers.** -/
theorem num_inj_of_B {arr : ℕ → ℕ → ℕ} {lo : List (OracleShape × ℕ)} {ps : List P5T.PSeat} {l : ℕ}
    (h : numsApartB arr lo.length (seatsOfLink ps l) = true) :
    ∀ i i' : Fin lo.length,
      arr (seatK10 lo ps l i).1 (seatK10 lo ps l i).2 =
        arr (seatK10 lo ps l i').1 (seatK10 lo ps l i').2 → i = i' := by
  unfold numsApartB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hn, hd⟩ := h
  intro i i' e
  have hi : i.val < (seatsOfLink ps l).length := by
    rw [hn]
    exact i.isLt
  have hi' : i'.val < (seatsOfLink ps l).length := by
    rw [hn]
    exact i'.isLt
  unfold seatK10 at e
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at e
  have hm : i.val < ((seatsOfLink ps l).map fun q => arr q.1 q.2).length := by
    rw [List.length_map]
    exact hi
  have hm' : i'.val < ((seatsOfLink ps l).map fun q => arr q.1 q.2).length := by
    rw [List.length_map]
    exact hi'
  have e2 : ((seatsOfLink ps l).map fun q => arr q.1 q.2)[i.val]'hm =
      ((seatsOfLink ps l).map fun q => arr q.1 q.2)[i'.val]'hm' := by
    rw [List.getElem_map, List.getElem_map]
    exact e
  exact Fin.ext ((List.Nodup.getElem_inj_iff hd).1 e2)

/-- **So the term for seat is injective.** -/
theorem seat_inj_of_num {arr : ℕ → ℕ → ℕ} {lo : List (OracleShape × ℕ)} {ps : List P5T.PSeat}
    {l : ℕ}
    (h : ∀ i i' : Fin lo.length,
      arr (seatK10 lo ps l i).1 (seatK10 lo ps l i).2 =
        arr (seatK10 lo ps l i').1 (seatK10 lo ps l i').2 → i = i') :
    Function.Injective (seatK10 lo ps l) := fun i i' e => h i i' (by rw [e])

/-- The numbering at the written seats of all three chains. -/
abbrev arrFull : ℕ → ℕ → ℕ := P5T.arrOf P5T.seatsAllFull

set_option maxRecDepth 1000000 in
/-- **(W) At every written list the members' numbers are all different.** -/
theorem numsApart_full :
    ((List.range 26).all fun l => numsApartB arrFull (Johnson.G.linksFullLit.getD l []).length
      (seatsOfLink P5T.psFull l)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** The numbers of links 0 and 1 in a row are not all different. -/
theorem numsApart_pair :
    numsApartB arrFull ((Johnson.G.linksFullLit.getD 0 []).length +
        (Johnson.G.linksFullLit.getD 1 []).length)
      (seatsOfLink P5T.psFull 0 ++ seatsOfLink P5T.psFull 1) = false := by decide +kernel

/-- **The first premise at the written values.** -/
theorem num_inj_full (l : ℕ) (hl : l < 26) :
    ∀ i i' : Fin (Johnson.G.linksFullLit.getD l []).length,
      arrFull (seatK10 (Johnson.G.linksFullLit.getD l []) P5T.psFull l i).1
          (seatK10 (Johnson.G.linksFullLit.getD l []) P5T.psFull l i).2 =
        arrFull (seatK10 (Johnson.G.linksFullLit.getD l []) P5T.psFull l i').1
          (seatK10 (Johnson.G.linksFullLit.getD l []) P5T.psFull l i').2 → i = i' :=
  num_inj_of_B (List.all_eq_true.1 numsApart_full l (List.mem_range.2 hl))

/-- **The second.** -/
theorem seat_inj_full (l : ℕ) (hl : l < 26) :
    Function.Injective (seatK10 (Johnson.G.linksFullLit.getD l []) P5T.psFull l) :=
  seat_inj_of_num (num_inj_full l hl)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.num_inj_of_B
#print axioms VerifiableInference.Desc.First.Close.seat_inj_of_num
#print axioms VerifiableInference.Desc.First.Close.numsApart_full
#print axioms VerifiableInference.Desc.First.Close.numsApart_pair
#print axioms VerifiableInference.Desc.First.Close.num_inj_full
#print axioms VerifiableInference.Desc.First.Close.seat_inj_full
