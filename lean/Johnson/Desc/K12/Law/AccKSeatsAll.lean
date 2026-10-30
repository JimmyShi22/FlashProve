-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.AccKAtSeats
import Johnson.Desc.K12.Law.AccKAtCourseAll
/-
Johnson/Desc/K12/Law/AccKSeatsAll.lean: THE THREE THINGS THAT AtSeatAll (Johnson/Desc/K12/Law/AccKAtCourseAll.lean) ASKS OF THE BLOCK IN THE LIST, PAID AT ALL FOUR WRITTEN SEATS of the proximity test, each as Chain.blocksInOrder lays it: atFinish (Johnson/Desc/K12/AtFinish.lean) · onGu · onGomega (Johnson/Desc/K12/Seat.lean) · onOwn (Johnson/Desc/K12/Seat/Own.lean). NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  IsSeat B p enter leave     the three things: B's rounds are the kind's block's · its decision is the kind's block's behind the door · its yes on the plan gives the kind's block's.
  isSeat_inside        laidBare (Block.inside enter (proximityTestKind guardedProximityTestParts p) leave) is a seat, FOR EVERY DOOR: ⟨rfl, rfl, seat_planOk⟩.
  atFinish_isSeat · onGu_isSeat · onGomega_isSeat · onOwn_isSeat     the four: each by isSeat_inside: SO EACH WRITTEN SEAT IS OF THAT FORM BY Lean's OWN UNFOLDING.
  atSeatAll_at         AtSeatAll at a cut with a seat: its conclusion, the three premises on B paid.
No sorry and no axiom of our own stands in this file.
LIMITS. THAT A WRITTEN DESCRIPTION's FLAT LIST HOLDS ONE OF THE FOUR AT SOME CUT IS SHOWN BY NOBODY. THE FOUR isSeat THEOREMS ARE AT Cl := Unit (the kind's block as the elder theorems type it; atFinish p : Block S Unit): AtSeatAll is general in the list's type of claims, THESE FOUR PAYERS ARE NOT: a description whose claims are of another type holds a re-typed copy of the seat, of which the three things are still to be shown.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Seat (onGu onGomega enterOwn leaveOwn onOwn)
open H2K.Pub (Letters)

/-- The three things that AtSeatAll asks of the block in the list. -/
def IsSeat {S Cl : Type} (B : Block S Cl) (p : P12) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) : Prop :=
  B.rounds = (proximityTestKind guardedProximityTestParts p : Blk').rounds ∧
    B.decide = (Block.inside enter (proximityTestKind guardedProximityTestParts p : Blk') leave).decide ∧
    (B.planOk = true → (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)

theorem isSeat_inside {S : Type} (p : P12) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) :
    IsSeat (laidBare (Block.inside enter (proximityTestKind guardedProximityTestParts p : Blk') leave)) p enter leave :=
  ⟨rfl, rfl, seat_planOk enter _ leave⟩

theorem atFinish_isSeat (p : P12) : IsSeat (laidBare (atFinish p)) p enterFinish leaveFinish :=
  isSeat_inside p enterFinish leaveFinish

theorem onGu_isSeat (p : P12) : IsSeat (laidBare (onGu (proximityTestKind guardedProximityTestParts p : Blk'))) p
    (Seat.enter (·.gU) (·.firstMask)) Seat.leave :=
  isSeat_inside p _ _

theorem onGomega_isSeat (p : P12) : IsSeat (laidBare (onGomega (proximityTestKind guardedProximityTestParts p : Blk'))) p
    (Seat.enter (·.gOmega) fun _ => none) Seat.leave :=
  isSeat_inside p _ _

theorem onOwn_isSeat (p : P12) : IsSeat (laidBare (onOwn (proximityTestKind guardedProximityTestParts p : Blk'))) p enterOwn
    leaveOwn :=
  isSeat_inside p _ _

/-- AtSeatAll at a cut with a seat. -/
theorem atSeatAll_at (X : Letters) (p : P12) (ft : ℕ) {S Cl : Type} (bs : List (Block S Cl))
    (s s' : S) (v : Fmt.View) (h : AtSeatAll X p ft bs s s' v) (pre : List (Block S Cl))
    (B : Block S Cl) (l : List (Block S Cl)) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (hb : bs = pre ++ B :: l) (hB : IsSeat B p enter leave) :
    ∃ (m : S) (t0 : T12) (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (tE : T12) (n : ℕ)
      (t : S),
      foldBlocks ft pre s v.rounds v.opened = .ok (m, behindOf pre v.rounds, cols) ∧
      (∃ j, cols = v.opened.drop j) ∧
      enter m = .ok t0 ∧ (behindOf pre v.rounds).take B.rounds.length = r0 :: rs' ∧
      (proximityTestKind guardedProximityTestParts p : Blk').step ft t0 (r0 :: rs') cols = .ok (tE, n) ∧ leave m tE = .ok t ∧
      foldBlocks ft l t ((behindOf pre v.rounds).drop B.rounds.length) (cols.drop n) =
        .ok (s', [], []) ∧
      YesAll X p ft t0 r0 rs' cols :=
  h pre B l enter leave hb hB.1 hB.2.1 hB.2.2

end H2K.JointK

#print axioms H2K.JointK.isSeat_inside
#print axioms H2K.JointK.atFinish_isSeat
#print axioms H2K.JointK.onGu_isSeat
#print axioms H2K.JointK.onGomega_isSeat
#print axioms H2K.JointK.onOwn_isSeat
#print axioms H2K.JointK.atSeatAll_at
