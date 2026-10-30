-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K11MembersAt.lean: THE TWO MEMBERS OF `mergeFill_at` AT THE CLOSED
PARAMETERS OFF THE PUBLIC PART Z AND THE LAYOUT FILE: ms := `P5T.msAt Z lay`, the table's numbers
off the planner's seats `P5T.planSeats Z Z.D.1`. Definitions with code; one theorem.

  `maskNo S m`: the number, in segment m's own list of messages, of the first with mask rows: THE
    TEXT BY WHICH THE BATCHING's KIND FINDS THE SEGMENT's MASK ROW (`K9L.maskOracle`,
    Johnson/Desc/First/Batch/Law/AsRow.lean; `K9.maskAt`, First/Batch/FormsIn.lean), its first half.
  `maskPlace ps S m`: the place (tree, tenant) at which the planner's seats have that message as
    segment m's own.
  **`k11AtB Z lay m`**: THE TEST: there is such a place, and `membersAtB` says yes there. IT CAN
    FAIL.
  **`k11_at`**: its yes gives pM, xM, xI with `mergeFill_at`'s five premises, at the numbers with
    whatever rows and told lists laid on (the form of `P5J.At.N`, Johnson/P5J/LettersAt.lean).
Limits. That the test says yes is left to whoever evaluates it. That the book of a reached state
has the message at `maskPlace` is not shown here. No soundness is claimed.

-/
import Johnson.Desc.Sound.MgAt.K11Members
import Johnson.P5T.MemberLists

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers)

/-- The number, in segment m's own list, of its first message with mask rows. -/
def maskNo (S : OnBytes.Params.ReqShape) (m : ℕ) : Option ℕ :=
  ((S.link[m]?.map (·.messages)).getD []).findIdx? fun x => x.shape.maskRows != 0

/-- The place at which the planner's seats have that message as segment m's own. -/
def maskPlace (ps : List P5T.PSeat) (S : OnBytes.Params.ReqShape) (m : ℕ) : Option (ℕ × ℕ) :=
  (maskNo S m).bind fun k =>
    (ps.find? fun p => p.seg.map (·.1) == some m && p.role == .own k).map (·.seat)

/-- **The test at the closed parameters.** -/
def k11AtB (Z : ProofFile.Pub) (lay : ByteArray) (m : ℕ) : Bool :=
  match maskPlace (P5T.planSeats Z Z.D.1) Z.first.shape m with
  | some pM => membersAtB (P5T.msAt Z lay) (P5T.numbersOf (P5T.planSeats Z Z.D.1)) m pM
  | none => false

/-- **Its yes gives the five premises, at the form of the closed numbers `P5J.At.N`.** -/
theorem k11_at (Z : ProofFile.Pub) (lay : ByteArray) (m : ℕ) (h : k11AtB Z lay m = true)
    (s : OnBytes.Params.ReqShape) (t : ℕ → ℕ) (n : ℕ) (ps : List Place)
    (told : List (List Oracle)) :
    ∃ pM xM xI, maskPlace (P5T.planSeats Z Z.D.1) Z.first.shape m = some pM ∧ seatOf xM = pM ∧
      xM ∈ P5T.msAt Z lay ∧
      seatOf xM ∈ (((P5T.numbersOf (P5T.planSeats Z Z.D.1)).withRows s t n).withTold ps told).sent
        m 0 ∧
      ((P5T.msAt Z lay).find? fun y => decide (seatOf y = seatOf xM)) = some xM ∧
      xI ∈ P5T.msAt Z lay ∧
      seatOf xI =
        (((P5T.numbersOf (P5T.planSeats Z Z.D.1)).withRows s t n).withTold ps told).index := by
  unfold k11AtB at h
  cases hp : maskPlace (P5T.planSeats Z Z.D.1) Z.first.shape m with
  | none => rw [hp] at h; cases h
  | some pM =>
    rw [hp] at h
    obtain ⟨xM, xI, -, -, e, a1, a2, a3, a4, a5⟩ := members_at _ _ m pM h
    exact ⟨pM, xM, xI, rfl, e, a1, a2, a3, a4, a5⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.k11_at
