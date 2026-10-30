-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/NoticesSent.lean: the announcements of the switch into a later group are what
the planner's record of that group says is sent. Three theorems with their proofs. General in the
request's shape; no text of the switch's kind is read but the one line that makes the announcements.

Why. The law of the switch of groups takes a typed list of the messages that are sent with a sample,
tied to the announcements that the text makes (`Tied`, SeedJoint.lean). The text does not test its
announcements against the plan: it makes them of the record's frame. The planner makes its list of
the request's shape. Here the two makes are held against each other.

What is said.
  `framesFrom_get`: the planner's record number i (`framesFrom`, OnBytes/Plan/ReqFrames.lean) is
    `frameAt` of the i-th group, the groups behind it, and the links and open rows from the i-th on,
    as long as every group in front of it has a link.
  `frameAt_sent`: a later group's record says that its members are sent.
  `notices_sent`: at a frame (`ReqFrame`, OnBytes/Iop/Req.lean) that has the plan's shape and that
    shape's groups, and stands at a link, or at the last test, that is not the first:
    `switchNotices` (Johnson/Top/H0/Tw/K2/Switch.lean) of the group's target and of "the link's
    messages of moment 0, then the fold's mask" is, as a list, the field `sent` of the planner's
    record of that group.

Limits. That a record's frame has the plan's shape and groups, and where it stands, are premises.
The first group is another kind's. Nothing on soundness.

-/
import OnBytes.Plan.ReqFrames
import Johnson.Top.H0.Tw.K2.Switch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Plan OnBytes.Params
open _root_.Tw.K2 (switchNotices)

/-- **The planner's record number i**, counted from the group at which the list begins: it is made
of the i-th group, of the groups behind it, and of the links and open rows from the i-th on: as long
as every group in front of it has a link. -/
theorem framesFrom_get (z : ProofSized) : ∀ (i l : ℕ) (gs : List ReqGroup) (links : List ReqLink)
    (open_ : List ℕ) (before : GroupSize) (g : ReqGroup), gs[i]? = some g →
    (∀ j, j < i → j < links.length) →
    ∃ before', (framesFrom z l gs links open_ before)[i]? =
      some (frameAt z (l + i) g (gs.drop (i + 1)) (links.drop i) (open_.drop i) before')
  | 0, l, [], _, _, _, _, h, _ => by simp at h
  | 0, l, g0 :: gs, links, open_, before, g, h, _ => by
    obtain rfl : g0 = g := by simpa using h
    exact ⟨before, by unfold framesFrom; simp⟩
  | i + 1, l, [], _, _, _, _, h, _ => by simp at h
  | i + 1, l, g0 :: gs, links, open_, before, g, h, hl => by
    have h' : gs[i]? = some g := by simpa using h
    have h0 : 0 < links.length := hl 0 (Nat.succ_pos i)
    obtain ⟨v, hv⟩ : ∃ v, links.head? = some v := by
      cases links with
      | nil => simp at h0
      | cons v _ => exact ⟨v, rfl⟩
    obtain ⟨b', hb'⟩ := framesFrom_get z i (l + 1) gs (links.drop 1) (open_.drop 1)
      (closedGroup z g0 gs) g h' (fun j hj => by
        have := hl (j + 1) (Nat.succ_lt_succ hj)
        rw [List.length_drop]
        omega)
    have e1 : l + 1 + i = l + (i + 1) := by omega
    have e2 : (links.drop 1).drop i = links.drop (i + 1) := by
      rw [List.drop_drop]
      congr 1
      omega
    have e3 : (open_.drop 1).drop i = open_.drop (i + 1) := by
      rw [List.drop_drop]
      congr 1
      omega
    rw [e1, e2, e3] at hb'
    refine ⟨b', ?_⟩
    unfold framesFrom
    rw [hv, List.getElem?_cons_succ, List.drop_succ_cons]
    exact hb'

/-- What a later group's record says is sent: its members. -/
theorem frameAt_sent (z : ProofSized) (l : ℕ) (h0 : 0 < l) (g : ReqGroup) (gs : List ReqGroup)
    (links : List ReqLink) (open_ : List ℕ) (before : GroupSize) :
    (frameAt z l g gs links open_ before).sent =
      membersOf z l g ((links.head?.map (·.messages)).getD []) := by
  have : (l == 0) = false := by simpa using Nat.pos_iff_ne_zero.1 h0
  simp [frameAt, this]

/-- **THE ANNOUNCEMENTS OF THE SWITCH INTO A LATER GROUP ARE WHAT THE PLANNER's RECORD OF THAT GROUP
SAYS IS SENT**: at a frame that has the plan's shape and that shape's groups, and stands at a link,
or at the last test, that is not the first. -/
theorem notices_sent (z : ProofSized) (sub : Subproofs) (f : ReqFrame) (hs : f.shape = z.request)
    (hg : f.groups = reqGroups z.request) (h0 : 0 < f.link)
    (hl : f.link ≤ z.request.link.length) (g : ReqGroup) (hG : f.groups[f.link]? = some g) :
    ∃ n, (framesOf z sub)[f.link]? = some n ∧
      (switchNotices g.target (ReqFrame.notices (f.atMoment 0) ++
        #[foldMaskNotice (f.foldShape f.link {})])).toList = n.sent := by
  have hG' : (reqGroups z.request).toList[f.link]? = some g := by
    rw [← hg]
    simpa using hG
  obtain ⟨b', hb'⟩ := framesFrom_get z f.link 0 (reqGroups z.request).toList z.request.link
    sub.openRows z.link.group g hG' (fun j hj => by omega)
  refine ⟨_, hb', ?_⟩
  rw [Nat.zero_add, frameAt_sent z f.link h0]
  have hd : f.groups.getD f.link {} = g := by
    rw [Array.getD_eq_getD_getElem?, hG]
    rfl
  have hh : (z.request.link.drop f.link).head? = z.request.link[f.link]? := by
    rw [List.head?_drop]
  unfold membersOf switchNotices ReqFrame.notices ReqFrame.atMoment ReqFrame.foldShape keptOf
  rw [hd, hs, hh]
  simp [h0]

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.notices_sent
