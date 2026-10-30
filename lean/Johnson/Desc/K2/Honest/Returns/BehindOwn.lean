-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/BehindOwn.lean: WHAT STANDS BEHIND THE SWITCH AT A SEGMENT's PLACE
RETURNS (`firstBehind`, Johnson/Top/H0/Tw/K2/First.lean: the next segment's own messages of moment 0
join the new group; the frame is laid) wherever premises on the make of what it is handed hold; what
it returns is a term. One statement with its proof, over Returns/Joins.lean and the library's
`firstBehind_iff` (Johnson/Top/H0/Tw/K2C/Asks.lean); and the like behind the last segment.

  `ownPairs`        the own messages with their numbers: what joins
  `firstBehind_returns`   PREMISES: as many numbers came back as there were announcements · there
                    are more of them than own messages (the fresh mask's stands behind the own) ·
                    the group is there and its test has not begun · each own message may join
                    (`MayJoin`: it is in the statement, sampled, of the group's codes; kept only
                    with a main row) · none is a member yet · their numbers differ. IT RETURNS: the
                    statement `joinedAll`; the frame with the plain scalars, the kept copies'
                    numbers, the fresh mask's, what rides at the start, the own messages' numbers,
                    and "a later message or the closing is due"; the own messages' numbers
  `finishBehind_returns`   behind the last segment: the fresh mask's number is the first of the
                    others

Limits. That the step behind the sending leaves these premises is not shown here. Nothing on any
property.

-/
import Johnson.Desc.K2.Honest.Returns.Joins
import Johnson.Top.H0.Tw.K2C.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Params (ReqMessage)
open _root_.Tw.K2 (firstBehind firstBehind_iff finishBehind finishBehind_iff)

/-- The own messages with their numbers. -/
def ownPairs (x : _root_.Tw.K2.Front) (s : Switched) : List (ReqMessage × Nat) :=
  zipT x.own (s.others.extract 0 x.own.length).toList

/-- **What stands behind a segment's switch returns.** -/
theorem firstBehind_returns (S : Statement) (x : _root_.Tw.K2.Front) (s : Switched)
    (plain : List E) (G : Group) (mask : Nat)
    (hn : s.others.size = x.others.size) (hm : s.others[x.own.length]? = some mask)
    (hG : S.groups[x.f.group]? = some G) (hr : G.inRun = false)
    (hj : ∀ p ∈ ownPairs x s, MayJoin S G.code G.maskCode p.2 (decide (0 < p.1.life)))
    (hnot : ∀ p ∈ ownPairs x s, p.2 ∉ G.members.toList)
    (hd : ((ownPairs x s).map (·.2)).Nodup) :
    firstBehind S x s plain = .ok
      (joinedAll x.f.group (fun p : ReqMessage × Nat => p.2) (fun p => decide (0 < p.1.life))
          (ownPairs x s) S,
        { x.f with
          plain := plain, keptBefore := s.kept, mask := some mask,
          atStart := x.f.atStart ++ s.others.extract (x.own.length + 1) s.others.size,
          own := x.f.own ++ s.others.extract 0 x.own.length, next := .laterOrClose },
        s.others.extract 0 x.own.length) := by
  have hlt : x.own.length < s.others.size := Nat.lt_of_not_le fun hc => by
    rw [Array.getElem?_eq_none hc] at hm
    cases hm
  obtain ⟨S', _, e, hf, _⟩ := joins_return x.f.group (fun p : ReqMessage × Nat => p.2)
    (fun p => decide (0 < p.1.life)) (ownPairs x s) S G hG hr hj hnot hd
  refine (firstBehind_iff S x s plain _ _ _).2 ⟨mask,
    { numbers := hn, theMask := hm, theOwn := rfl
      own := by
        rw [Array.size_extract]
        omega
      joins := by
        rw [← e]
        exact hf
      frame := rfl }⟩

/-- **Behind the last segment.** -/
theorem finishBehind_returns (s : Switched) (mask : Nat) (hm : s.others[0]? = some mask) :
    finishBehind s = .ok mask := (finishBehind_iff s mask).2 hm

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.firstBehind_returns
