-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/HeadBehindPaid.lean: THE NAMED PREMISE OF Returns/HeadAfter.lean,
`BehindReturns u`, HOLDS BEHIND THE YES OF THE CODE SWITCH's OWN DECISION AT THE OUTPUT HEAD's
PLACE, WHEREVER THE PREMISES OF THIS FOLDER's OWN LAW "the kind's decision says yes there" HOLD
(`HeadPlain`, Returns/ArmsSent.lean) AND THE SEGMENT's OWN FIRST MESSAGES ARE ANNOUNCED AS THE NEW
GROUP WANTS THEM (`OwnPlain`'s second clause, Returns/SentOwn.lean). AFTER THE PATTERN OF THE LAW AT
A LINK (`link_returns`, Returns/Link.lean), where the kind's own text runs `firstBehind` itself.
HOW: under `HeadPlain` what the switch returns is a term; the decision is a function, so the given
yes holds that term; at it `firstBehind_returns` has all seven premises. No walk, no head of the
composed meaning: a state, two rounds, columns. Statements with their proofs: calls.

  `more_head` at the head's front there are more other announcements than own messages
  `head_behind_returns` `HeadPlain p s r₁ r₂ gs a Q c G` · for every own message of moment 0 its
                    announcement has an answer, the group's codes where it has rows of the sort, and
                    a main row if the message has a life · a yes u of the kind's own decision at s,
                    [r₁, r₂], gs ⊢ `BehindReturns u`

By, this folder's: `firstBehind_returns` (Returns/BehindOwn.lean) · `switchBehind_returns_at`
(Returns/BehindAt.lean) · `readOld_returns` (Returns/Read.lean), `ofDraws_all`
(Returns/ReadSymbols.lean) · `sendByL8_returns`, `sentAt_codes` (Returns/Sends.lean),
`sentAt_roots`, `sentAt_others` (Returns/SendsMore.lean), `older_sent` (Returns/SentRead.lean),
`frontFits_sent` (Returns/SentFront.lean) · `OwnPlain`, `own_mask`, `own_join`, `own_differ`
(Returns/SentOwn.lean) · `sendingAt_sent`, `took_of_answers` (Returns/LinkSent.lean) · `HeadPlain`,
`CallPlain` (Returns/ArmsSent.lean) · `MayJoin.of_core` (Returns/Joins.lean) · `BehindReturns`
(Returns/HeadAfter.lean). The library's: `head_inv`, `HeadIs`, `headFrontOf`, `outOf`
(Johnson/Top/H0/Tw/K2C/Closed.lean), `switchE_of` (Johnson/Top/H0/Tw/K2C/AsksWhole.lean),
`withRows_group`, `withRows_oracles` (OnBytes/Slice/BlkCalls.lean). NEAR RELATIVES, NOT CALLED:
`others_of_front` (Johnson/Top/H0/Tw/K2C/SentAtPlan.lean): one announcement more than own messages,
at every front of the kind: `more_head` is its like at the head's front's term; `more_link`
(Returns/LinkSent.lean) at a link's · `link_returns` (Returns/Link.lean), `linkFits_sent`
(Returns/LinkSent.lean), `switchE_returns_sent` (Returns/ArmsSent.lean): THE PROOF IS THEIRS, LAID
TOGETHER AT THE HEAD's FRONT.

Limits. `HeadPlain` AND THE CLAUSE ON THE OWN MESSAGES ARE PREMISES: NOBODY PAYS THEM HERE.
`HeadPlain` asks much of the two rounds and the columns (that they fit the plan's entries; what the
reading wants): SO THIS IS NOT "BEHIND EVERY YES": IT IS BEHIND THE YES AT ROUNDS AND COLUMNS AT
WHICH THIS FOLDER's LAW GIVES THE YES. At the decision, not at the step. The output head's place
alone. Over files of this folder that are lined for a sealed library and not yet in one. Nothing on
any property.

-/
import Johnson.Desc.K2.Honest.Returns.HeadAfter
import Johnson.Desc.K2.Honest.Returns.ArmsSent
import Johnson.Desc.K2.Honest.Returns.Link

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Slice (withRows withRows_group withRows_oracles)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.K2 (P2 decideWith par9 flat locOk outOf behindArgs switchE_of
  head_inv headFrontOf)
open Johnson.Prover.Send (SendFront)
open _root_.Tw.K2 (Front Col S9 sendByL8 switchBehind switchE switchNotices)

/-- At the head's front there are more other announcements than own messages. -/
theorem more_head (s : S) (a : HeadOwn) (T : SwitchTarget) :
    (headFrontOf s a T).own.length < (headFrontOf s a T).others.size := by
  show (s.check.frame.atMoment 0).length <
    (ReqFrame.notices (s.check.frame.atMoment 0) ++
      #[foldMaskNotice (s.check.frame.foldShape s.check.frame.link {})]).size
  simp [ReqFrame.notices]

/-- **The named premise holds behind the yes, under the law's own premises at the head.** -/
theorem head_behind_returns {p : P2} {s : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {a : HeadOwn} {Q : ReqGroup} {c : Code} {G : Group}
    (H : HeadPlain p s r₁ r₂ gs a Q c G)
    (own : ∀ (j : Nat) (m : Params.ReqMessage), (headFrontOf s a Q.target).own[j]? = some m →
      ∃ n, (headFrontOf s a Q.target).others[j]? = some n ∧ n.shape.answers ≠ 0 ∧
        (n.shape.mainRows = 0 ∨ n.shape.code = G.code) ∧
        (n.shape.maskRows = 0 ∨ n.shape.maskCode = G.maskCode) ∧
        (0 < m.life → 0 < n.shape.mainRows))
    {u : S} (hy : decideWith sendByL8 p s [r₁, r₂] gs = .ok u) : BehindReturns u := by
  have hs := sendingAt_sent p (headFrontOf s a Q.target)
  have ow : OwnPlain (headFrontOf s a Q.target) G := ⟨more_head s a Q.target, own⟩
  have ol := older_sent (par9 p) (headFrontOf s a Q.target) s.book s.roots r₁ r₂ (flat p gs)
    (sendingAt p (headFrontOf s a Q.target))
  have hSend : sendByL8 (par9 p) (headFrontOf s a Q.target).st s.book s.roots s.noneWaits
      (switchNotices (headFrontOf s a Q.target).T (headFrontOf s a Q.target).others) r₁ r₂ =
      .ok (sentAt (sendingAt p (headFrontOf s a Q.target)) (headFrontOf s a Q.target).st s.book
        s.roots r₁ r₂) := by
    rw [H.waits]
    exact sendByL8_returns (par9 p) (sendingAt p (headFrontOf s a Q.target)) _ _ _ _ r₁ r₂ rfl hs
      H.call.entry H.call.fits₁
      (SendFront.of_lengths _ _ rfl H.call.plan H.call.step H.call.front.lengths)
      H.call.front.lengths H.call.draw H.call.vals H.call.poss H.call.trits H.call.factor
      H.call.answers
  have hTrees : (sentAt (sendingAt p (headFrontOf s a Q.target)) (headFrontOf s a Q.target).st
      s.book s.roots r₁ r₂).roots = s.roots + (par9 p).eSeed.roots := by
    rw [sentAt_roots, H.call.trees]
  have hCode : (sentAt (sendingAt p (headFrontOf s a Q.target)) (headFrontOf s a Q.target).st
      s.book s.roots r₁ r₂).st.codes.base[(headFrontOf s a Q.target).f.rows.code]? = some c := by
    rw [sentAt_codes]
    exact H.call.oldCode
  obtain ⟨yy, hRead, hsize⟩ := readOld_returns _ _ (H.call.reads.older ol) (ofDraws_all _ _)
  obtain ⟨S3, G3, rows, _, hAl, hG3, hrun, hc3, hm3, _, hmem, _, hB⟩ :=
    switchBehind_returns_at _ c _ _ yy G hCode H.call.loc hRead hsize
      (frontFits_sent (par9 p) (headFrontOf s a Q.target) s.book s.roots r₁ r₂ (flat p gs) _ rfl
        hs H.call.front)
  have hE := switchE_of (behind := switchBehind) (P := par9 p) (send := sendByL8)
    (s := ⟨s.st, s.book, s.roots, a.fr, [], s.noneWaits⟩) (x := headFrontOf s a Q.target)
    (rS := r₁) (rL := r₂) (cols := flat p gs)
    ⟨H.waits, rfl, (_root_.Tw.K2.targetOk_eq _ _ _).trans H.call.front.check, hSend,
      took_of_answers _ _ H.call.answers, hTrees, hB, rfl⟩
  -- the given yes holds that term
  obtain ⟨r₁', r₂', a', Q', w, roots, hrs, k⟩ := head_inv H.stands hy
  obtain ⟨rfl, rfl⟩ : r₁ = r₁' ∧ r₂ = r₂' := by
    injection hrs with e1 e2
    injection e2 with e2 _
    exact ⟨e1, e2⟩
  obtain rfl : a = a' := by
    have e := H.here.symm.trans k.hHere
    injection e
  obtain rfl : Q = Q' := Option.some.inj (H.group.symm.trans k.hGroup)
  have ew : w = _ := congrArg Prod.fst (Except.ok.inj (k.hSwitch.symm.trans hE))
  have hGw := withRows_group (headFrontOf s a Q.target).f.group rows S3 G3 hG3
  have hor := (withRows_oracles (headFrontOf s a Q.target).f.group rows S3).1
  intro a'' ha''
  have ea : a'' = { a with kept := w.out.kept, ids := w.out.others } := by
    rw [k.hOut] at ha''
    injection ha'' with e'
    exact e'.symm
  rw [ea, k.hOut, ew]
  exact ⟨_, firstBehind_returns _ _ _ _ _ _
    (sentAt_others (sendingAt p (headFrontOf s a Q.target)) (headFrontOf s a Q.target).st s.book
      s.roots r₁ r₂ (headFrontOf s a Q.target).T (headFrontOf s a Q.target).others hs)
    (own_mask (par9 p) (headFrontOf s a Q.target) s.book s.roots r₁ r₂ (flat p gs) _ hs
      (Positions.ofDraws c.logN r₂.drawn.poss) ow) hGw hrun
    (fun q hq => by
      have h := (own_join (par9 p) (headFrontOf s a Q.target) s.book s.roots r₁ r₂ (flat p gs) _
        hs (Positions.ofDraws c.logN r₂.drawn.poss) ow q hq).1
      rw [← hc3, ← hm3] at h
      have e := hAl.cores q.2
      rw [← hor] at e
      exact h.of_core e)
    (fun q hq hin => by
      have h := own_join (par9 p) (headFrontOf s a Q.target) s.book s.roots r₁ r₂ (flat p gs) _
        hs (Positions.ofDraws c.logN r₂.drawn.poss) ow q hq
      rcases (hmem q.2).1 hin with h' | h'
      · exact h.2.1 h'
      · exact h.2.2 h')
    (own_differ (par9 p) (headFrontOf s a Q.target) s.book s.roots r₁ r₂ (flat p gs) _ hs
      (Positions.ofDraws c.logN r₂.drawn.poss))⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.more_head
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_behind_returns
