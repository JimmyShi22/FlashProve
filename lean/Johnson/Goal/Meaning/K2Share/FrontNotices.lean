-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/K2Share/FrontNotices.lean: the code switch at a link: WHAT THE SWITCH ANNOUNCES
IS A TERM OF THE PLAN's SHAPE AND THE LINK's NUMBER.



  frameAtLink sh l: the frame with the shape sh, the groups reqGroups sh, at link l; all else blank.
  othersAt sh l, targetAt sh l, noticesAt sh l: the link's own messages of moment 0 and the fold's
    mask; the target of the switch into group l; switchNotices of the two: functions of sh and l.
  atMoment_pub, foldShape_pub: ReqFrame.atMoment and ReqFrame.foldShape read the frame's shape,
    groups and link alone.
  link_notices: firstFront S0 f = .ok x, FramePub sh f and f.link = l give x.T = targetAt sh l,
    x.others = othersAt sh l, and so switchNotices x.T x.others = noticesAt sh l.
  notices_at_link: at a link's place: RecAll cs sh s, s.check.frame.link = l and frontAt p s = some
    fx give switchNotices fx.T fx.others = noticesAt sh l and fx.st.codes = cs.
  notices_behind_laid: the same with "the block «laid» at link l has just said yes" (layFront l s₀ =
    .ok s) in the place of the equation on the frame's link.
LIMITS. RecAll at s₀ is a premise. That «laid» stands right in front of the switch in a description
is not shown. The head's and the finish's places are not spoken of. That noticesAt sh l is a place's
P.sent is a comparison of two terms of the plan: not made here. No soundness is claimed.

-/
import Johnson.Goal.Meaning.K2Share.K2Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open Meaning.K2 (RecAll FramePub)
open _root_.Tw.K2 (switchNotices firstFront)

/-- The plan's frame at a link: all that moves is blank. -/
def frameAtLink (sh : ReqShape) (l : Nat) : ReqFrame :=
  { shape := sh, groups := reqGroups sh, link := l }

/-- What a link's switch announces beside g and the kept members. -/
def othersAt (sh : ReqShape) (l : Nat) : Array OracleNotice :=
  ReqFrame.notices ((frameAtLink sh l).atMoment 0) ++
    #[foldMaskNotice ((frameAtLink sh l).foldShape l {})]

/-- The target of the switch into group l. -/
def targetAt (sh : ReqShape) (l : Nat) : SwitchTarget := ((reqGroups sh).getD l {}).target

/-- **What the switch at link l announces.** -/
def noticesAt (sh : ReqShape) (l : Nat) : Array OracleNotice :=
  switchNotices (targetAt sh l) (othersAt sh l)

theorem atMoment_pub {sh : ReqShape} {f : ReqFrame} {l : Nat} (F : FramePub sh f)
    (hl : f.link = l) (m : Nat) : f.atMoment m = (frameAtLink sh l).atMoment m := by
  unfold ReqFrame.atMoment frameAtLink
  rw [F.shape, hl]

theorem foldShape_pub {sh : ReqShape} {f : ReqFrame} (F : FramePub sh f) (l k : Nat)
    (lay : GroupLayout) : f.foldShape k lay = (frameAtLink sh l).foldShape k lay := by
  unfold ReqFrame.foldShape frameAtLink
  rw [F.shape, F.groups]

/-- **The front of a link's switch announces the plan's.** -/
theorem link_notices {sh : ReqShape} {S0 : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    {l : Nat} (h : firstFront S0 f = .ok x) (F : FramePub sh f) (hl : f.link = l) :
    x.T = targetAt sh l ∧ x.others = othersAt sh l ∧
      switchNotices x.T x.others = noticesAt sh l := by
  have key : x.T = targetAt sh l ∧ x.others = othersAt sh l := by
    unfold firstFront at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · rename_i L G hL hG
          dsimp only at h
          split at h
          · cases h
          · cases h
            refine ⟨?_, ?_⟩
            · show G.target = _
              unfold targetAt
              rw [F.groups, hl] at hG
              rw [Array.getD_eq_getD_getElem?, hG]
              rfl
            · show ReqFrame.notices (f.atMoment 0) ++
                #[foldMaskNotice (f.foldShape f.link {})] = _
              unfold othersAt
              rw [atMoment_pub F hl, hl, foldShape_pub F l]
        · cases h
        · cases h
  refine ⟨key.1, key.2, ?_⟩
  unfold noticesAt
  rw [key.1, key.2]

/-- **At a link's place.** -/
theorem notices_at_link {cs : Codes} {sh : ReqShape} {p : P2} {s : S} {fx : _root_.Tw.K2.Front}
    {l : Nat} (R : RecAll cs sh s) (hl : s.check.frame.link = l) (hp : p.stands = .link)
    (h : frontAt p s = some fx) :
    switchNotices fx.T fx.others = noticesAt sh l ∧ fx.st.codes = cs :=
  ⟨(link_notices (front_of_link hp h) R.walk hl).2.2, codes_link (recPub_of_all R) hp h⟩

/-- **Right behind «laid».** -/
theorem notices_behind_laid {cs : Codes} {sh : ReqShape} {p : P2} {s₀ s : S}
    {fx : _root_.Tw.K2.Front} {l : Nat} (R : RecAll cs sh s₀)
    (hlaid : _root_.Johnson.Desc.First.Walk.layFront l s₀ = .ok s) (hp : p.stands = .link)
    (h : frontAt p s = some fx) :
    switchNotices fx.T fx.others = noticesAt sh l ∧ fx.st.codes = cs :=
  notices_at_link (Meaning.K2.layFront_rec l s₀ s hlaid R) (Meaning.K2.layFront_link hlaid) hp h

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.link_notices
#print axioms VerifiableInference.Desc.First.K2.notices_at_link
#print axioms VerifiableInference.Desc.First.K2.notices_behind_laid
