-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K11MembersAtR.lean: THE TWO MEMBERS OF `mergeFill_at` AT THE LIST OF MEMBERS
THAT THE COMPOSED MEANING's CLOSED CONSTANT LAYS: ms := `P5T.msAtR Z rad`
(Johnson/P5T/MembersByMake.lean): shapes and places by the make off the planner's seats, the radii
an argument. Definitions with code; theorems with their proofs.

  `xAt_isSome`: there is a member at the place p just where p is among the members' places.
  `membersAtB_seats`: the test `membersAtB` (K11Members.lean) reads the members' places alone.
  `seats_atR`: the places of `msAtR Z rad` do not hang on the radii (`P5T.plain_membersR`).
  **`k11AtRB Z m`**: THE TEST: `membersAtB` at `msAtR Z` with every radius 0, at `maskPlace`. IT
    READS THE PUBLIC PART Z ALONE: no layout file, no rows of the sendings. IT CAN FAIL.
  **`k11_atR`**: its yes gives pM, xM, xI with `mergeFill_at`'s five premises AT EVERY rad, at the
    numbers with whatever rows and told lists laid on.
Limits. That the test says yes is not shown here; at segment 24, under the head, it is shown in
K11MembersAtHead.lean. Nothing on a radius. That the book of a reached
state has the message at `maskPlace` is not shown here. No soundness is claimed.

-/
import Johnson.Desc.Sound.MgAt.K11MembersAt
import Johnson.P5T.MembersByMake

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers)

theorem xAt_isSome (ms : List Mem) (p : ℕ × ℕ) :
    (xAt ms p).isSome = (ms.map seatOf).contains p := by
  unfold xAt
  rw [Bool.eq_iff_iff, List.find?_isSome, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, of_decide_eq_true h⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, decide_eq_true rfl⟩

/-- The test reads the members' places alone. -/
theorem membersAtB_seats (ms ms' : List Mem) (h : ms.map seatOf = ms'.map seatOf) (N : Numbers)
    (m : ℕ) (pM : ℕ × ℕ) : membersAtB ms N m pM = membersAtB ms' N m pM := by
  unfold membersAtB
  rw [xAt_isSome, xAt_isSome, xAt_isSome, xAt_isSome, h]

/-- The members' places do not hang on the radii. -/
theorem seats_atR (Z : ProofFile.Pub) (rad rad' : ℕ → ℕ → ℕ) :
    (P5T.msAtR Z rad).map seatOf = (P5T.msAtR Z rad').map seatOf := by
  have e := fun r => congrArg (List.map Prod.snd)
    (P5T.plain_membersR Z.made.proof.1.sends.length r (P5T.planSeats Z Z.D.1))
  simp only [List.map_map] at e
  exact (e rad).trans (e rad').symm

/-- **The test, off the public part alone.** -/
def k11AtRB (Z : ProofFile.Pub) (m : ℕ) : Bool :=
  match maskPlace (P5T.planSeats Z Z.D.1) Z.first.shape m with
  | some pM =>
    membersAtB (P5T.msAtR Z fun _ _ => 0) (P5T.numbersOf (P5T.planSeats Z Z.D.1)) m pM
  | none => false

/-- **Its yes gives the five premises at every rad.** -/
theorem k11_atR (Z : ProofFile.Pub) (m : ℕ) (h : k11AtRB Z m = true) (rad : ℕ → ℕ → ℕ)
    (s : OnBytes.Params.ReqShape) (t : ℕ → ℕ) (n : ℕ) (ps : List Place)
    (told : List (List Oracle)) :
    ∃ pM xM xI, maskPlace (P5T.planSeats Z Z.D.1) Z.first.shape m = some pM ∧ seatOf xM = pM ∧
      xM ∈ P5T.msAtR Z rad ∧
      seatOf xM ∈ (((P5T.numbersOf (P5T.planSeats Z Z.D.1)).withRows s t n).withTold ps told).sent
        m 0 ∧
      ((P5T.msAtR Z rad).find? fun y => decide (seatOf y = seatOf xM)) = some xM ∧
      xI ∈ P5T.msAtR Z rad ∧
      seatOf xI =
        (((P5T.numbersOf (P5T.planSeats Z Z.D.1)).withRows s t n).withTold ps told).index := by
  unfold k11AtRB at h
  cases hp : maskPlace (P5T.planSeats Z Z.D.1) Z.first.shape m with
  | none => rw [hp] at h; cases h
  | some pM =>
    rw [hp] at h
    have h' : membersAtB (P5T.msAtR Z rad) (P5T.numbersOf (P5T.planSeats Z Z.D.1)) m pM = true :=
      (membersAtB_seats _ _ (seats_atR Z rad fun _ _ => 0) _ m pM).trans h
    obtain ⟨xM, xI, -, -, e, a1, a2, a3, a4, a5⟩ := members_at _ _ m pM h'
    exact ⟨pM, xM, xI, rfl, e, a1, a2, a3, a4, a5⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.xAt_isSome
#print axioms VerifiableInference.Desc.Sound.membersAtB_seats
#print axioms VerifiableInference.Desc.Sound.seats_atR
#print axioms VerifiableInference.Desc.Sound.k11_atR
