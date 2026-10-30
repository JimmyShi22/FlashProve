-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingSeat.lean: the member of the first chain's flat list
at which its closing proximity test stands seats the test. The member is the test at the finish
behind the mark's guard and the guard on the reply's seat (`firstEntry`, `firstCore`). So it meets
`SeatOf` (K12/SaysYesSeat.lean) with the way out `outCore`, which holds the two guards; and that way
out returns behind whatever the test's block accepts, at a state at which the way in has returned.

  `bind_four`       four reasons to stop, in a row, regrouped
  `seatOf_entry`    `SeatOf` at the member, at every job at that place
  `leaves_outCore`  the way out returns

By what. `outCore_ok` (Johnson/Loose/H2K12/FirstSeatForm.lean); `enterFinish_ok`
(Johnson/Desc/K12/SeatLaws.lean).

Limits. The member is named by its text: that the description's list holds it at that number is
`k12_sits` (Johnson/Loose/H2K12/SitsAtDescPure.lean), at that law's premises. Nothing on completeness,
soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.SaysYesSeat
import Johnson.Loose.H2K12.FirstSeatForm
import Johnson.Desc.K12.SeatLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc (Block seatSame)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts enterFinish leaveFinish atFinish)
open VerifiableInference.Desc.First (S)
open H2K.JointK (a12 firstEntry firstCore outCore outCore_ok guardS)

variable {W X : Type}

/-- Four reasons to stop, in a row, regrouped. -/
theorem bind_four {A B C : Type} (e : Except String A) (K : A → Except String B)
    (lv : B → Except String C) (g h : C → Except String C) :
    ((e.bind fun t => (K t).bind lv).bind g).bind h =
      e.bind fun t => (K t).bind fun u => ((lv u).bind g).bind h := by
  cases e with
  | error _ => rfl
  | ok t =>
    show (((K t).bind lv).bind g).bind h = (K t).bind fun u => ((lv u).bind g).bind h
    cases K t with
    | error _ => rfl
    | ok u => rfl

/-- **The member seats the test**, at every job at that place. -/
theorem seatOf_entry (J : TestJob W X) (nm : String) (hp : J.p.place = a12) :
    SeatOf (firstEntry ProofFile.sameReply (firstCore J.p nm)) J enterFinish
      (outCore ProofFile.sameReply) where
  place := hp.symm
  rounds := rfl
  oracles := rfl
  decide := fun s rs gs => by
    show ((((enterFinish s).bind fun t =>
        ((proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide t rs gs).bind (leaveFinish s)).bind
          guardS).bind (seatSame ProofFile.sameReply s)) = _
    exact bind_four _ _ _ _ _

/-- **The way out returns**, behind whatever the test's block accepts, where the way in has. -/
theorem leaves_outCore {st : S} {R : T12} (he : enterFinish st = .ok R) (t' : T12) :
    ∃ s', outCore ProofFile.sameReply st t' = .ok s' := by
  obtain ⟨o, -, -, hf, -⟩ := VerifiableInference.Desc.K12.Seat.enterFinish_ok st R he
  refine ⟨{ st with st := t'.st, book := t'.book, roots := t'.roots },
    (outCore_ok _ _ _ _).2 ⟨rfl, ?_, ?_⟩⟩
  · exact Option.isNone_iff_eq_none.1 hf
  · simp [ProofFile.sameReply]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.bind_four
#print axioms ProofFile.Honest.K12.seatOf_entry
#print axioms ProofFile.Honest.K12.leaves_outCore
