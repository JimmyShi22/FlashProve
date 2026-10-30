-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2R0R/OmegaOfSeats.lean: THE LAST TABLE's TEST "omega" (Johnson/LLT25R/LastLedger.lean:
LastPlan8.omega: Omega's tree lies below the last chain's first: (Ns.tenant .oOmega).1 < D.t₁ +
D.t₂) FOLLOWS FROM FOUR OTHER TESTS OF THE SAME LIST (Johnson/LLT25R/LastOwedCore.lean: PlanOk₃:
someO · allSeats · apartWO · apartIO) AND ONE COMPARISON OF NUMBERS: nΩ < D.t₂. STATED AND PROVED.
So a list of what is left of PlanOk₃ need not name omega.
  omega_seat: Omega's seat in the shared table's numbers IS (t + nΩ, 0): a member of ms₂ sits there
      (someO); it is one of mine (mem_mineOf); every one of mine has one of three seats (allSeats);
      the two elder seats are not Omega's (apartIO · apartWO).
  **omega_of_seats**: so its tree is t + nΩ, which lies below t + t₂ where nΩ < t₂.
  omega_unfolds: what the test says at the join's own numbers numbersSh lo layU layO w i, by rfl:
      lo + layU.shapes.size + layO.tree.getD 0 0 < t₁ + t₂.
  omega_seat_two · **omega_of_two**: THE SAME FROM TWO TESTS ALONE: omegaSeat (one of mine has the
      seat (t + nΩ, 0)) · seatsApart's last two (the two elder seats are not that seat). THE PROOF
      IS tenant_is (Johnson/LLT25R/LastNamedCore.lean), which takes
      PlanOk₃ whole: here at the fields that it reads, so that whoever PAYS PlanOk₃ can call it.
General in every letter: no scope, no size, no file.
Limits. The tests stay premises: NO EXAMPLE IN LEAN shows them met together, AND NO EVALUATION
THAT CAN BE CITED DOES.
nΩ < D.t₂ is the caller's (at the join nΩ is 1, and
AtMg.trees_at, Johnson/HB/LLHARD/HeadFacts.lean, has D.t₂ = 11 under the one head of a counted
statement). Nothing on soundness or on hiding.

-/
import Johnson.LLT25R.LastMine
import Johnson.Desc.Sound.SharedMembers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2R0
open VerifiableInference.Desc.Sound (Mem seatOf SitsAt)
open VerifiableInference.Desc.Shared (NumbersS Msg2)
open VerifiableInference.Desc.First (Numbers)
open LLT25

variable {ms₁ ms₂ : List Mem} {N₁ : Numbers} {Ns : NumbersS} {vI vW : ℕ × ℕ} {t nΩ t₂ : ℕ}

/-- **Omega's seat is (t + nΩ, 0).** -/
theorem omega_seat
    (someO : ∃ x ∈ ms₂, SitsAt x (Ns.tenant .oOmega).1 (Ns.tenant .oOmega).2)
    (allSeats : ∀ z ∈ mineOf ms₁ ms₂ N₁ Ns, seatOf z = vI ∨ seatOf z = vW ∨ seatOf z = (t + nΩ, 0))
    (apartIO : vI ≠ Ns.tenant .oOmega) (apartWO : vW ≠ Ns.tenant .oOmega) :
    Ns.tenant .oOmega = (t + nΩ, 0) := by
  obtain ⟨x, hx, hs⟩ := someO
  have hs' : x.1.seat x.2 = Ns.tenant .oOmega := hs
  have hm : x ∈ mineOf ms₁ ms₂ N₁ Ns := mem_mineOf.2 (Or.inr ⟨hx, hs'⟩)
  have e : seatOf x = Ns.tenant .oOmega := hs'
  rcases allSeats x hm with h | h | h
  · exact absurd (h.symm.trans e) apartIO
  · exact absurd (h.symm.trans e) apartWO
  · exact e.symm.trans h

/-- **The test omega, from the four and one comparison.** -/
theorem omega_of_seats
    (someO : ∃ x ∈ ms₂, SitsAt x (Ns.tenant .oOmega).1 (Ns.tenant .oOmega).2)
    (allSeats : ∀ z ∈ mineOf ms₁ ms₂ N₁ Ns, seatOf z = vI ∨ seatOf z = vW ∨ seatOf z = (t + nΩ, 0))
    (apartIO : vI ≠ Ns.tenant .oOmega) (apartWO : vW ≠ Ns.tenant .oOmega) (hn : nΩ < t₂) :
    (Ns.tenant .oOmega).1 < t + t₂ := by
  rw [omega_seat someO allSeats apartIO apartWO]
  exact Nat.add_lt_add_left hn t

/-- **Omega's seat, from two tests.** -/
theorem omega_seat_two
    (omegaSeat : ∃ x ∈ mineOf ms₁ ms₂ N₁ Ns, seatOf x = (t + nΩ, 0))
    (apartI : N₁.index ≠ (t + nΩ, 0)) (apartW : N₁.w ≠ (t + nΩ, 0)) :
    Ns.tenant .oOmega = (t + nΩ, 0) := by
  obtain ⟨x, hx, sx⟩ := omegaSeat
  rcases mem_mineOf.1 hx with ⟨-, h | h⟩ | ⟨-, h⟩
  · exact absurd ((show seatOf x = N₁.w from h).symm.trans sx) apartW
  · exact absurd ((show seatOf x = N₁.index from h).symm.trans sx) apartI
  · exact (show seatOf x = Ns.tenant .oOmega from h).symm.trans sx

/-- **The test omega, from the two and one comparison.** -/
theorem omega_of_two
    (omegaSeat : ∃ x ∈ mineOf ms₁ ms₂ N₁ Ns, seatOf x = (t + nΩ, 0))
    (apartI : N₁.index ≠ (t + nΩ, 0)) (apartW : N₁.w ≠ (t + nΩ, 0)) (hn : nΩ < t₂) :
    (Ns.tenant .oOmega).1 < t + t₂ := by
  rw [omega_seat_two omegaSeat apartI apartW]
  exact Nat.add_lt_add_left hn t

/-- What the test says at the join's own numbers. -/
theorem omega_unfolds (lo : ℕ) (layU layO : OnBytes.TreeLay) (w i : ℕ × ℕ) (t₁ : ℕ) :
    (((Desc.K14.Law.Fence.numbersSh lo layU layO w i).tenant .oOmega).1 < t₁ + t₂) =
      (lo + layU.shapes.size + layO.tree.getD 0 0 < t₁ + t₂) := rfl

end P2R0

#print axioms P2R0.omega_seat
#print axioms P2R0.omega_of_seats
#print axioms P2R0.omega_seat_two
#print axioms P2R0.omega_of_two
#print axioms P2R0.omega_unfolds
