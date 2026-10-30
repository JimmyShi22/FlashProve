-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.AccKAtFinish
import Johnson.Desc.K12.Seat
import Johnson.Desc.K12.Seat.Own
/-
Johnson/Desc/K12/Law/AccKAtSeats.lean: Johnson/Desc/K12/Law/AccKAtCourse.lean's AtSeat AT THE THREE OTHER SEATS of the proximity test: onGu · onGomega (Johnson/Desc/K12/Seat.lean: the shared chain) and onOwn (Johnson/Desc/K12/Seat/Own.lean: the last chain), each as Chain.blocksInOrder lays it. With Johnson/Desc/K12/Law/AccKAtFinish.lean: ALL FOUR. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.

  onGu_seat · onGomega_seat · onOwn_seat     laidBare of the seat has the kind's block's rounds and the decision of the kind's block behind the seat's own door: ⟨rfl, rfl⟩.
  onGomega_mask        onGomega's door lays no mask at any record: the premise henter of atSeat_mask, PAID: so at that seat the own arm's «t0.mask = none» falls.
  onGu_mask | onOwn_mask     at the two other doors the mask is the record's own word: t0.mask = m.loc.firstMask | m.loc.mask.
  shared_atGomega_own  runCore's yes · the premises on p with ownMask · ownTieOk · b₂ = pre ++ laidBare (onGomega (proximityTestKind guardedProximityTestParts p)) :: l ⇒ the fold over pre leaves (m, …, cols) of s₂, the second view's rounds and opened columns · the door's record t0 · the seat's stretch is r0 :: rs' · YesOwn X p 0 t0 r0 rs' cols: NO PREMISE ON THE RECORD IS LEFT. SUPERSEDED FOR A SPENDER by run_atSeat_all (Johnson/Desc/K12/Law/AccKAtCourseAll.lean) with onGomega_isSeat (Johnson/Desc/K12/Law/AccKSeatsAll.lean), which take none of nzOk · dealOk · tieOk · logOk · ownTieOk and need no word on the door's mask: CALL THOSE.
No sorry and no axiom of our own stands in this file.
LIMITS. All of Johnson/Desc/K12/Law/AccKAtCourse.lean's. THAT A WRITTEN DESCRIPTION's CHAIN HOLDS THE SEAT is the premise hb. WHICH ARM A PLACE TAKES (the record names the mask, or the fold brings its own) is not decided here: at onGu and onOwn it hangs on the record. NO MEMBER AT A REAL p.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Seat (onGu onGomega enterOwn leaveOwn onOwn)
open H2K.Pub (Letters)
open H2K.First (nzOk dealOk tieOk logOk ownTieOk)

theorem onGu_seat (p : P12) :
    (laidBare (onGu (proximityTestKind guardedProximityTestParts p : Blk'))).rounds = (proximityTestKind guardedProximityTestParts p : Blk').rounds ∧
      (laidBare (onGu (proximityTestKind guardedProximityTestParts p : Blk'))).decide =
        (Block.inside (Seat.enter (·.gU) (·.firstMask)) (proximityTestKind guardedProximityTestParts p : Blk') Seat.leave).decide
            :=
  ⟨rfl, rfl⟩

theorem onGomega_seat (p : P12) :
    (laidBare (onGomega (proximityTestKind guardedProximityTestParts p : Blk'))).rounds = (proximityTestKind guardedProximityTestParts p : Blk').rounds ∧
      (laidBare (onGomega (proximityTestKind guardedProximityTestParts p : Blk'))).decide =
        (Block.inside (Seat.enter (·.gOmega) fun _ => none) (proximityTestKind guardedProximityTestParts p : Blk')
            Seat.leave).decide :=
  ⟨rfl, rfl⟩

theorem onOwn_seat (p : P12) :
    (laidBare (onOwn (proximityTestKind guardedProximityTestParts p : Blk'))).rounds = (proximityTestKind guardedProximityTestParts p : Blk').rounds ∧
      (laidBare (onOwn (proximityTestKind guardedProximityTestParts p : Blk'))).decide =
        (Block.inside enterOwn (proximityTestKind guardedProximityTestParts p : Blk') leaveOwn).decide :=
  ⟨rfl, rfl⟩

/-- onGomega's door lays no mask. -/
theorem onGomega_mask (s : _root_.Desc.K14.St) (t : T12)
    (h : Seat.enter (·.gOmega) (fun _ => none) s = .ok t) : t.mask = none := by
  cases h
  rfl

theorem onGu_mask (s : _root_.Desc.K14.St) (t : T12)
    (h : Seat.enter (·.gU) (·.firstMask) s = .ok t) : t.mask = s.loc.firstMask := by
  cases h
  rfl

theorem onOwn_mask (s : Third.S₃) (t : T12) (h : enterOwn s = .ok t) : t.mask = s.loc.mask := by
  cases h
  rfl

/-- At the shared chain's test on G_omega, the own mask's arm: no premise on the record is left. -/
theorem shared_atGomega_own (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hnz : nzOk p = true) (hdeal : dealOk p = true)
    (htie : tieOk p = true) (hlog : logOk p = true) (ho : p.nums.ownMask = true)
    (hown : ownTieOk p = true) {S₁ S₃ : Type} (planWord : Option String)
    (okStart : Bool) (s₁ : S₁) (s₂ : _root_.Desc.K14.St)
    (start₃ : S₁ → _root_.Desc.K14.St → Except String S₃) (ft : ℕ)
    (b₁ : List (Block S₁ Unit)) (b₂ : List (Block _root_.Desc.K14.St Unit))
    (b₃ : List (Block S₃ Unit)) (fin : S₁ → _root_.Desc.K14.St → S₃ → Bool) (v₁ v₂ v₃ : Fmt.View)
    (e : S₁ × _root_.Desc.K14.St × S₃)
    (h : runCore planWord okStart s₁ s₂ start₃ ft b₁ b₂ b₃ fin v₁ v₂ v₃ = .ok e)
    (pre l : List (Block _root_.Desc.K14.St Unit))
    (hb : b₂ = pre ++ laidBare (onGomega (proximityTestKind guardedProximityTestParts p : Blk')) :: l) :
    ∃ (m : _root_.Desc.K14.St) (t0 : T12) (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn),
      foldBlocks 0 pre s₂ v₂.rounds v₂.opened = .ok (m, behindOf pre v₂.rounds, cols) ∧
      Seat.enter (·.gOmega) (fun _ => none) m = .ok t0 ∧
      (behindOf pre v₂.rounds).take (laidBare (onGomega (proximityTestKind guardedProximityTestParts p : Blk'))).rounds.length =
        r0 :: rs' ∧
      YesOwn X p 0 t0 r0 rs' cols :=
  atSeat_mask X p 0 b₂ s₂ e.2.1 v₂
    (course_atSeat_own X p he ha hp hnz hdeal htie hlog ho hown planWord okStart s₁ s₂ start₃ ft
      b₁ b₂ b₃ fin v₁ v₂ v₃ e h).2.1
    pre _ l _ Seat.leave onGomega_mask hb (onGomega_seat p).1 (onGomega_seat p).2

end H2K.JointK

#print axioms H2K.JointK.onGu_seat
#print axioms H2K.JointK.onGomega_seat
#print axioms H2K.JointK.onOwn_seat
#print axioms H2K.JointK.onGomega_mask
#print axioms H2K.JointK.shared_atGomega_own
