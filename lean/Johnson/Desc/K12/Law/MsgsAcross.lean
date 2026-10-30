-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.OutK3
import Johnson.Desc.K12.Law.Top
import Johnson.Desc.K12.SeatLaws
/-
Johnson/Desc/K12/Law/MsgsAcross.lean: HOW MANY ORACLE MESSAGES THE PROXIMITY TEST BRINGS: the count of
the statement's messages across an accept of the sub-protocol's decision, as a term of the place's
numbers: two for each code switch (the stages less one), and one more where the first fold sends its own
mask. The like of RootsAcross.lean's count of roots. Wanted by Johnson/IMR/MsgsBehind.lean, for its
walk along the proof file's first chain. CALLS OF k12_out2 (Johnson/Desc/K12/Law/OutK2.lean: the
field oraclesN). BOOK-KEEPING ON THE VERIFIER's STATE. NO
SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  k12_msgs         (proximityTestKind guardedProximityTestParts p).decide t0 rs gs = .ok tE ⇒ tE.st.oracles.size =
      t0.st.oracles.size + (if t0.mask.isNone then 1 else 0) + 2 * (p.nums.stages.length - 1)
  atFinish_msgs    at the first chain's finish, where the first mask is handed in:
      s'.st.oracles.size = s.st.oracles.size + 2 * (p.nums.stages.length - 1)
  k12_places | atFinish_places   the like of the book's places: by k12_out3
      (Johnson/Desc/K12/Law/OutK3.lean: in front of the test and behind it the book has a place for each
      oracle message, and for no other)
WHAT IS NOT HERE: that this term is the count of the tenants that the sub-protocol declares
(((atFinish p).oracles.flatten.map fun o => o.tenants.length).sum): that half is left to callers.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's
end.
-/
set_option autoImplicit false
namespace H2K.Out
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK

/-- The count across the test's own decision. -/
theorem k12_msgs (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    tE.st.oracles.size =
      t0.st.oracles.size + (if t0.mask.isNone then 1 else 0) + 2 * (p.nums.stages.length - 1) := by
  obtain ⟨_, O⟩ := k12_out2 p (early_of_planOk p hp) (answers_of_planOk p hp) t0 tE rs gs h
  exact O.oraclesN

/-- At the first chain's finish. -/
theorem atFinish_msgs (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (s s' : First.S)
    (rs : List Fmt.RoundView) (gs : Gs) (hm : ∀ fo, s.here = .fin fo → fo.mask.isSome = true)
    (h : (atFinish p).decide s rs gs = .ok s') :
    s'.st.oracles.size = s.st.oracles.size + 2 * (p.nums.stages.length - 1) := by
  obtain ⟨fo, t', hfo, _, _, hd, rfl⟩ := Seat.atFinish_ok p s s' rs gs h
  have e := k12_msgs p hp _ t' rs gs hd
  have hn : fo.mask.isNone = false := by
    have := hm fo hfo
    cases hk : fo.mask with
    | none => rw [hk] at this; cases this
    | some _ => rfl
  simpa [hn] using e

/-- The book's places across the test's own decision. -/
theorem k12_places (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    tE.book.place.size =
      t0.book.place.size + (if t0.mask.isNone then 1 else 0) + 2 * (p.nums.stages.length - 1) := by
  have O := k12_out3 p (early_of_planOk p hp) (answers_of_planOk p hp) t0 tE rs gs h
  rw [← O.step, ← O.step0]
  exact k12_msgs p hp t0 tE rs gs h

/-- At the first chain's finish. -/
theorem atFinish_places (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (s s' : First.S)
    (rs : List Fmt.RoundView) (gs : Gs) (hm : ∀ fo, s.here = .fin fo → fo.mask.isSome = true)
    (h : (atFinish p).decide s rs gs = .ok s') :
    s'.book.place.size = s.book.place.size + 2 * (p.nums.stages.length - 1) := by
  obtain ⟨fo, t', hfo, _, _, hd, rfl⟩ := Seat.atFinish_ok p s s' rs gs h
  have e := k12_places p hp _ t' rs gs hd
  have hn : fo.mask.isNone = false := by
    have := hm fo hfo
    cases hk : fo.mask with
    | none => rw [hk] at this; cases this
    | some _ => rfl
  simpa [hn] using e

end H2K.Out

#print axioms H2K.Out.k12_msgs
#print axioms H2K.Out.atFinish_msgs
#print axioms H2K.Out.k12_places
#print axioms H2K.Out.atFinish_places
