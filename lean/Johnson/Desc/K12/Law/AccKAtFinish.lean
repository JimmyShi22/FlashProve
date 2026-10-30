-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.AccKAtCourse
import Johnson.Desc.K12.AtFinish
/-
Johnson/Desc/K12/Law/AccKAtFinish.lean: Johnson/Desc/K12/Law/AccKAtCourse.lean's AtSeat AT ONE OF THE FOUR SEATS: atFinish p (Johnson/Desc/K12/AtFinish.lean: the proximity test at the first chain's finish), as Chain.blocksInOrder lays it (its test on the plan alone turned). So that the two equations which AtSeat asks of the block in the list are SEEN TO BE PAID BY rfl at a written seat. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  laidBare b          what Chain.blocksInOrder makes of a block b outside the links (first · front · back · last): Block.lean's own line, copied; laidBare_flat: a chain's flat list is laidBare first :: front.map laidBare ++ the links' ++ back.map laidBare ++ [laidBare last] (Block.lean): by rfl: so the copy is held by a compile.
  atFinish_seat       laidBare (atFinish p) has the kind's block's rounds and the decision of the kind's block behind enterFinish | leaveFinish: ⟨rfl, rfl⟩.
  course_atFinish     runCore's yes · the premises on p · b₁ = pre ++ laidBare (atFinish p) :: l ⇒ the fold over pre leaves (m, …, cols) of s₁, the first view's rounds with the seal's behind them, and its opened columns · enterFinish m = .ok t0 · the seat's stretch is r0 :: rs' · YesConst X p 0 t0 r0 rs' cols.
No sorry and no axiom of our own stands in this file.
LIMITS. All of Johnson/Desc/K12/Law/AccKAtCourse.lean's. course_atFinish THROWS what AtSeat holds beside (the kind's block's step's yes, the way out, the fold behind): harmless for accK's yes; whoever goes on along the chain goes back to AtSeat. THAT A WRITTEN DESCRIPTION's FIRST CHAIN HOLDS THIS SEAT is the premise hb. The three other seats (onGu · onGomega · onOwn) are not taken here: their files are not imported. The constant arm alone.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (Letters)
open H2K.First (nzOk dealOk tieOk logOk)

/-- What Chain.blocksInOrder makes of a block outside the links. -/
def laidBare {S Cl : Type} (b : Block S Cl) : Block S Cl := { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }

theorem laidBare_flat {S Cl : Type} (c : Chain S Cl) :
    c.blocksInOrder = laidBare c.first :: c.front.map laidBare ++ c.links.flatMap Link.blocksInOrder ++
      c.back.map laidBare ++ [laidBare c.last] := rfl

theorem atFinish_seat (p : P12) :
    (laidBare (atFinish p)).rounds = (proximityTestKind guardedProximityTestParts p : Blk').rounds ∧
      (laidBare (atFinish p)).decide =
        (Block.inside enterFinish (proximityTestKind guardedProximityTestParts p : Blk') leaveFinish).decide := ⟨rfl, rfl⟩

/-- At the first chain's finish. -/
theorem course_atFinish (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hnz : nzOk p = true) (hdeal : dealOk p = true)
    (htie : tieOk p = true) (hlog : logOk p = true) {S₂ S₃ : Type} (planWord : Option String)
    (okStart : Bool) (s₁ : First.S) (s₂ : S₂) (start₃ : First.S → S₂ → Except String S₃) (ft : ℕ)
    (b₁ : List (Block First.S Unit)) (b₂ : List (Block S₂ Unit)) (b₃ : List (Block S₃ Unit))
    (fin : First.S → S₂ → S₃ → Bool) (v₁ v₂ v₃ : Fmt.View) (e : First.S × S₂ × S₃)
    (h : runCore planWord okStart s₁ s₂ start₃ ft b₁ b₂ b₃ fin v₁ v₂ v₃ = .ok e)
    (pre l : List (Block First.S Unit)) (hb : b₁ = pre ++ laidBare (atFinish p) :: l) :
    ∃ (m : First.S) (t0 : T12) (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn),
      foldBlocks 0 pre s₁ (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened =
        .ok (m, behindOf pre (withEmptySealRound v₁).rounds, cols) ∧
      enterFinish m = .ok t0 ∧
      (behindOf pre (withEmptySealRound v₁).rounds).take (proximityTestKind guardedProximityTestParts p : Blk').rounds.length = r0 :: rs' ∧
      YesConst X p 0 t0 r0 rs' cols := by
  obtain ⟨m, t0, r0, rs', cols, _, _, _, h0, e1, e3, _, _, _, hy⟩ :=
    (course_atSeat X p he ha hp hnz hdeal htie hlog planWord okStart s₁ s₂ start₃ ft b₁ b₂ b₃ fin
      v₁ v₂ v₃ e h).1 pre _ l enterFinish leaveFinish hb (atFinish_seat p).1 (atFinish_seat p).2
  exact ⟨m, t0, r0, rs', cols, h0, e1, e3, hy⟩

end H2K.JointK

#print axioms H2K.JointK.laidBare_flat
#print axioms H2K.JointK.atFinish_seat
#print axioms H2K.JointK.course_atFinish
