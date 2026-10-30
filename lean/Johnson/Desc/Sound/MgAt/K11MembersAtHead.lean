-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K11MembersAtHead.lean: THE TEST `k11AtRB Zp 24` (K11MembersAtR.lean) SAYS
YES UNDER THE HEAD. Theorems with their proofs; two closed facts at the written list of seats and
one negative test on it; a bent twin of the end. Through the payers that it calls it needs the
proof file's entry tests (`LPFD.lawsAsk`) with their first thirteen rows (
Johnson/Desc/Laid/ProofAsksLaw2.lean lies in its imports). In this tree they have fourteen rows.

Why. The test stood in a file of evaluations: evaluated, no theorem. Under the head (`P5J.AtMg`)
`AtMg.seats_written` and `AtMg.mask_place` (Johnson/HB/LLHARD/MaskSeatWritten.lean) give the
planner's list of seats, the core of the numbers and the mask row's seat as the written ones. The
test reads the members' places alone (`xAt_isSome`), and these are the seats of the planner's
entries with a sample (`P5T.memsSame_atR`: no premise). So what is left is closed.

Main names. h: the head. Zp: the public part that the laid value opens.
  `seat_mem_atR`: a seat of an entry with a sample is a place of a member of `msAtR Z rad`.
  `mask_sampled_written` | `index_sampled_written`: (73, 2) and the index's seat are such seats of
    the written list. `sampled_rejects`: (0, 3), the seat of an entry without a sample, is none.
  **`k11AtRB_at_head`**: `k11AtRB Zp 24 = true`.
  `k11_bent_at_head`: THE BENT TWIN: at the seat (74, 0) in (73, 2)'s place the same test says no.
  `k11_members_at_head`: `k11_atR`'s five premises at every rad, from the head alone.

Limits. It pays no premise of the head: whether a head exists at any public files is not shown here.
The written list is the planner's at written sendings: that the makers give these values is what
the entry tests compare at a run, no theorem. Segment 24 alone. The full size alone. What the radii
are it does not say: its ends hold at every rad. That the book of a reached state has the message
at (73, 2) is not shown here. No soundness is claimed.

-/
import Johnson.HB.LLHARD.MaskSeatWritten
import Johnson.Desc.Sound.MgAt.K11MembersAtR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc (Chain)
open P5T (psFull N0Full)
open OnBytes.Maker (WholeD)

/-- A seat of an entry with a sample is a place of a member, at every rad. -/
theorem seat_mem_atR (Z : ProofFile.Pub) (rad : ℕ → ℕ → ℕ) (s : ℕ × ℕ)
    (hs : s ∈ ((P5T.planSeats Z Z.D.1).filter (·.smpd)).map (·.seat)) :
    s ∈ (P5T.msAtR Z rad).map seatOf := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
  obtain ⟨x, hx, e⟩ := List.mem_map.1
    ((P5T.memsSame_atR Z rad (p.shape, p.seat)).2 (List.mem_map.2 ⟨p, hp, rfl⟩))
  exact List.mem_map.2 ⟨x, hx, congrArg Prod.snd e⟩

/-! ## At the written list of seats -/

set_option maxRecDepth 1000000 in
/-- The mask row's seat is the seat of an entry with a sample. -/
theorem mask_sampled_written :
    ((73, 2) : ℕ × ℕ) ∈ (psFull.filter (·.smpd)).map (·.seat) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- So is the index's. -/
theorem index_sampled_written : N0Full.index ∈ (psFull.filter (·.smpd)).map (·.seat) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- NEGATIVE TEST: (0, 3), the seat of an entry of the list without a sample, is the seat of no
entry with one. -/
theorem sampled_rejects : ((0, 3) : ℕ × ℕ) ∈ psFull.map (·.seat) ∧
    ((0, 3) : ℕ × ℕ) ∉ (psFull.filter (·.smpd)).map (·.seat) := by decide +kernel

/-! ## Under the head -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **The test says yes under the head.** -/
theorem k11AtRB_at_head (h : P5J.AtMg o Z D r Zp Np cF) : k11AtRB Zp 24 = true := by
  have hp := h.seats_written.1
  have hN := h.seats_written.2.2
  unfold k11AtRB
  rw [h.mask_place]
  show membersAtB (P5T.msAtR Zp fun _ _ => 0) (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)) 24 (73, 2)
    = true
  rw [hN]
  unfold membersAtB
  rw [xAt_isSome, xAt_isSome]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem]
  exact ⟨⟨seat_mem_atR Zp _ _ (hp ▸ mask_sampled_written), P5J.sent_written⟩,
    seat_mem_atR Zp _ _ (hp ▸ index_sampled_written)⟩

/-- **The bent twin**: at the seat (74, 0) the same test says no, under the same head. -/
theorem k11_bent_at_head (h : P5J.AtMg o Z D r Zp Np cF) :
    membersAtB (P5T.msAtR Zp fun _ _ => 0) (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)) 24 (74, 0)
      = false := by
  rw [h.seats_written.2.2]
  unfold membersAtB
  rw [decide_eq_false P5J.sent_rejects, Bool.and_false, Bool.false_and]

/-- `k11_atR`'s five premises at every rad, from the head alone. -/
theorem k11_members_at_head (h : P5J.AtMg o Z D r Zp Np cF) (rad : ℕ → ℕ → ℕ)
    (s : OnBytes.Params.ReqShape) (t : ℕ → ℕ) (n : ℕ) (ps : List Place)
    (told : List (List Oracle)) :
    ∃ pM xM xI, maskPlace (P5T.planSeats Zp Zp.D.1) Zp.first.shape 24 = some pM ∧ seatOf xM = pM ∧
      xM ∈ P5T.msAtR Zp rad ∧
      seatOf xM ∈ (((P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).withRows s t n).withTold ps told).sent
        24 0 ∧
      ((P5T.msAtR Zp rad).find? fun y => decide (seatOf y = seatOf xM)) = some xM ∧
      xI ∈ P5T.msAtR Zp rad ∧
      seatOf xI =
        (((P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).withRows s t n).withTold ps told).index :=
  k11_atR Zp 24 (k11AtRB_at_head h) rad s t n ps told

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.seat_mem_atR
#print axioms VerifiableInference.Desc.Sound.mask_sampled_written
#print axioms VerifiableInference.Desc.Sound.index_sampled_written
#print axioms VerifiableInference.Desc.Sound.sampled_rejects
#print axioms VerifiableInference.Desc.Sound.k11AtRB_at_head
#print axioms VerifiableInference.Desc.Sound.k11_bent_at_head
#print axioms VerifiableInference.Desc.Sound.k11_members_at_head
