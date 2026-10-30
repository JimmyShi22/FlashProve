-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/Link.lean: THE KIND's OWN DECISION SAYS YES AT A SEGMENT's FIRST
PLACE (`decideWith`, Johnson/Top/H0/Tw/K2C/Kind.lean, at `p.stands = .link`), THE SENDING BEING A
LETTER: the front, the guard, the sending, the step behind it, and what stands behind the switch,
laid together. One structure of premises, one statement with its proof, over Returns/Front.lean,
Returns/Read.lean, Returns/BehindAt.lean, Returns/BehindOwn.lean and the library's `switchE_of` and
`link_of` (Johnson/Top/H0/Tw/K2C/AsksWhole.lean).

  `frontAt`         the front's term at a state of the verifier's
  `LinkFits`        ALL PREMISES. ON THE STATE IN FRONT: the chain stands between the segments · a
                    segment's first call is due · nothing waits · the frame's facts for the front
                    (a first message is due; not segment 0; the shape has the segment, the groups'
                    list its group; the two codes are in their lists, the mask code not longer) ·
                    the segment sends no plain scalar · the new group's number is the plan's. ON
                    THE ROUNDS: every drawn position lies in the range. THE GUARD on the target, at
                    the front's statement. THE SENDING RETURNS y; it took no more items than the
                    message holds; it laid as many trees as the entry has roots. AT WHAT THE
                    SENDING HANDS ON: the four premises of the law on the step. FOR WHAT STANDS
                    BEHIND: as many numbers as announcements; the fresh mask's is among them; each
                    own message may join, is neither g nor a copy, and their numbers differ. THE
                    COLUMNS: none is left; as many groups as the place reads trees
  `link_returns`    under `LinkFits`: the decision says yes

Limits. ONE PREMISE HAS THE FORM "… = .ok y": THE SENDING's: `snd` is a letter. That the sending
leaves what is asked at what it hands on is not shown. The entry "LOC" counts no rows: a premise.
The head's place and the place behind the last segment are not here. No member of `LinkFits` is
typed. The law speaks of the kind's own decision: where a block is seated, a run returns only if it
also leaves the reply as it was: not stated here. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.Front
import Johnson.Desc.K2.Honest.Returns.BehindOwn
import Johnson.Desc.K2.Honest.Returns.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Slice (withRows withRows_group withRows_oracles)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (withGroup)
open VerifiableInference.Desc.First.K2 (P2 decideWith par9 flat locOk outOf behindArgs switchE_of
  link_of)
open Johnson.Desc.First.Walk (firstDue)
open _root_.Tw.K2 (switchBehind switchGuard switchNotices)

/-- The front's term at a state. L, Q: the segment and its group, off the frame. -/
def frontAt (s : S) (L : Params.ReqLink) (Q : ReqGroup) : _root_.Tw.K2.Front :=
  ⟨withGroup s.st s.check.frame.shape.code s.check.frame.shape.maskCode,
    { s.check.frame with group := s.st.groups.size, moment := 1, own := #[] },
    s.check.frame.atMoment 0,
    ReqFrame.notices (s.check.frame.atMoment 0) ++
      #[foldMaskNotice (s.check.frame.foldShape s.check.frame.link {})], Q.target, L.plain⟩

/-- **All premises.** y: what the sending returns. c: the old main code. G: the new group behind the
sending. mask: the fresh mask's number. -/
structure LinkFits (snd : _root_.Tw.K2.SendFn) (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (L : Params.ReqLink) (Q : ReqGroup) (c₀ z₀ : Code)
    (y : _root_.Tw.K2.Sent) (c : Code) (G : Group) (mask : Nat) : Prop where
  stands : p.stands = .link
  range : ∀ q ∈ r₂.drawn.poss, q < 2 ^ p.logN
  here : s.here = .between
  due : firstDue s.check = true
  waits : s.noneWaits = true
  first : s.check.frame.next = .first
  later : s.check.frame.link ≠ 0
  link : s.check.frame.shape.link[s.check.frame.link]? = some L
  group : s.check.frame.groups[s.check.frame.link]? = some Q
  code : s.st.codes.base[s.check.frame.shape.code]? = some c₀
  maskCode : s.st.codes.mask[s.check.frame.shape.maskCode]? = some z₀
  shorter : z₀.logN ≤ c₀.logN
  plain : L.plain = 0
  number : s.st.groups.size = p.grp
  noRows : (par9 p).eLoc.rows = 0
  guard : switchGuard (frontAt s L Q).st (frontAt s L Q).f.rows (frontAt s L Q).T = true
  sends : snd (par9 p) (frontAt s L Q).st s.book s.roots s.noneWaits
    (switchNotices (frontAt s L Q).T (frontAt s L Q).others) r₁ r₂ = .ok y
  took : y.took ≤ r₂.vals.length
  trees : y.roots = s.roots + (par9 p).eSeed.roots
  oldCode : (behindArgs (par9 p) (frontAt s L Q) y r₂ (flat p gs)).st.codes.base[
    (behindArgs (par9 p) (frontAt s L Q) y r₂ (flat p gs)).old.code]? = some c
  loc : locOk (behindArgs (par9 p) (frontAt s L Q) y r₂ (flat p gs)) c.logN = true
  reads : ReadFits (behindArgs (par9 p) (frontAt s L Q) y r₂ (flat p gs))
    (Positions.ofDraws c.logN (behindArgs (par9 p) (frontAt s L Q) y r₂ (flat p gs)).drawn.poss)
  front : FrontFits (behindArgs (par9 p) (frontAt s L Q) y r₂ (flat p gs)) c G
  numbers : (y.ids.extract (1 + Q.target.kept.size) y.ids.size).size = (frontAt s L Q).others.size
  theMask : (y.ids.extract (1 + Q.target.kept.size) y.ids.size)[(frontAt s L Q).own.length]? =
    some mask
  join : ∀ q ∈ ownPairs (frontAt s L Q)
      (outOf (behindArgs (par9 p) (frontAt s L Q) y r₂ (flat p gs))
        (Positions.ofDraws c.logN r₂.drawn.poss)),
    MayJoin y.st G.code G.maskCode q.2 (decide (0 < q.1.life)) ∧ q.2 ≠ y.ids.getD 0 noId ∧
      q.2 ∉ (y.ids.extract 1 (1 + Q.target.kept.size)).toList
  differ : ((ownPairs (frontAt s L Q)
      (outOf (behindArgs (par9 p) (frontAt s L Q) y r₂ (flat p gs))
        (Positions.ofDraws c.logN r₂.drawn.poss))).map (·.2)).Nodup
  noneLeft : leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) y.book
    (treesOf (behindArgs (par9 p) (frontAt s L Q) y r₂ (flat p gs))) (flat p gs) = []
  groups : gs.length = p.read.length

/-- **The kind's own decision says yes at a segment's first place.** -/
theorem link_returns {snd : _root_.Tw.K2.SendFn} {p : P2} {s : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {L : Params.ReqLink} {Q : ReqGroup} {c₀ z₀ : Code}
    {y : _root_.Tw.K2.Sent} {c : Code} {G : Group} {mask : Nat}
    (H : LinkFits snd p s r₁ r₂ gs L Q c₀ z₀ y c G mask) :
    ∃ s', decideWith snd p s [r₁, r₂] gs = .ok s' := by
  have hx := firstFront_returns s.st s.check.frame L Q c₀ z₀ H.first H.later H.link H.group H.code
    H.maskCode H.shorter
  obtain ⟨yy, hRead, hsize⟩ := readOld_returns _ _ H.reads (ofDraws_all _ _)
  obtain ⟨S3, G3, rows, _, hAl, hG3, hrun, hc3, hm3, _, hmem, _, hB⟩ :=
    switchBehind_returns_at _ c _ _ yy G H.oldCode H.loc hRead hsize H.front
  have hE := switchE_of (behind := switchBehind) (P := par9 p) (send := snd)
    (s := ⟨s.st, s.book, s.roots, s.check.frame, [], s.noneWaits⟩) (x := frontAt s L Q)
    (rS := r₁) (rL := r₂) (cols := flat p gs)
    ⟨H.waits, H.noRows, H.guard, H.sends, H.took, H.trees, hB, rfl⟩
  have hGw := withRows_group (frontAt s L Q).f.group rows S3 G3 hG3
  have hor := (withRows_oracles (frontAt s L Q).f.group rows S3).1
  have hb := firstBehind_returns (withRows S3 (frontAt s L Q).f.group rows) (frontAt s L Q)
    (outOf (behindArgs (par9 p) (frontAt s L Q) y r₂ (flat p gs))
      (Positions.ofDraws c.logN r₂.drawn.poss)) [] _ mask H.numbers H.theMask hGw hrun
    (fun q hq => by
      have h := (H.join q hq).1
      rw [← hc3, ← hm3] at h
      exact h.of_core (by rw [hor]; exact hAl.cores q.2))
    (fun q hq hin => by
      rcases (hmem q.2).1 hin with h | h
      · exact (H.join q hq).2.1 h
      · exact (H.join q hq).2.2 h)
    H.differ
  exact ⟨_, link_of H.stands ⟨H.range, H.here, H.due, hx, H.plain, hE, hb,
    ⟨H.noneLeft, H.groups⟩, H.number, rfl⟩⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_returns
