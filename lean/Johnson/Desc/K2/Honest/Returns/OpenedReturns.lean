-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/OpenedReturns.lean: THE WAY OUT AT A LINK's FIRST PLACE RETURNS
BEHIND EVERY YES OF THE CODE SWITCH's OWN DECISION: where the state in front bears no mark and its
frame stands at link l, l is not 0, and the row's own test on the plan says yes: `leaveOpened f s u`
returns (Johnson/P1K2R/SitsStep.lean). No walk, no head: a row of `framesOf`, a state and the
decision's yes. THE LIBRARY's LAWS ON A ROW's "opened" ALL GO FROM ITS YES; THAT IT RETURNS IS WHAT
IS NEW HERE. Statements with their proofs: unfolding and calls.

  `unmarked_err` where `S.unmarked` refuses the state bears a mark
  `openAtt_returns`, `openLay_returns` the two texts of "opened" behind link 0: the plan's test ·
                    the state stands between two links · the link's first call has run · no plain
                    scalar · the frame's link is the record's · no mark ⊢ it returns
  `opened_returns` so row l of `framesOf` returns, l ≠ 0, where the row's `plan` says yes (where the
                    link's record is the head's, "opened" hands the state on)
  `yes_frame` behind a yes of the kind's own decision in a link's dress: between two links · the
                    first call has run · no plain scalar · the frame's link, the mark and what the
                    walk has gathered are as in front
  `leave_returns` THE TOP: … ⊢ ∃ t, leaveOpened f s u = ok t

By, the library's: `framesOf_arms` (Johnson/Top/H0/Walk/FrameRows.lean) · `openAtt`, `openLay`,
`planAtt`, `planLay`, `planFlag`, `firstRun` (Johnson/Desc/First/Walk/Frame.lean), `attFirstQuiet`,
`layFirstQuiet` (Johnson/Desc/First/Walk/FirstQuiet.lean), `front`, `firstKept`
(Johnson/Desc/First/Walk/Quiet.lean) · `enterAtt_ok`, `enterLay_ok`, `openAtt_ok`, `openLay_ok`
(Johnson/Top/H0/Walk/FrameLaw.lean) · `link_inv`, `LinkIs` (Johnson/Top/H0/Tw/K2C/Closed.lean),
`firstFront_iff`, `firstBehind_iff` (Johnson/Top/H0/Tw/K2C/Asks.lean). This folder's:
`leaveOpened_iff` (Returns/SeatIff.lean).

Limits. That the state in front bears no mark and stands at link l, and that the row's test on the
plan says yes, are premises: nobody pays them here. In a link's dress alone: nothing at link 0, at
the output head's switch or behind the last segment. At the decision, not at the step. Nothing on
any property.

-/
import Johnson.Desc.K2.Honest.Returns.SeatIff
import Johnson.Top.H0.Walk.FrameRows
import Johnson.Top.H0.Walk.FrameLaw
import Johnson.Top.H0.Tw.K2C.Closed
import Johnson.Top.H0.Tw.K2C.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes OnBytes.Model
open VerifiableInference.Desc (need)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 decideWith link_inv)
open Johnson.Desc.First.Walk (AttPar LayPar openAtt openLay planAtt planLay planFlag firstRun
  attFirstQuiet layFirstQuiet front)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf framesOf_arms pubOf)
open Johnson.Desc.First.Walk.Law (enterAtt_ok enterLay_ok openAtt_ok openLay_ok)
open P1K2 (leaveOpened)

theorem unmarked_err {s : S} {e : String} (h : s.unmarked = .error e) : s.failed ≠ none := by
  intro hn
  unfold S.unmarked at h
  rw [hn] at h
  cases h

/-- **Behind an attention link's first call "opened" returns.** -/
theorem openAtt_returns {shape : Params.ReqShape} {P : AttPar} (hp : planAtt shape P = true)
    {m : S} (hB : m.atBetween = true) (hA : firstRun m.check = true)
    (h0 : m.check.frame.plain = []) (hl : m.check.frame.link = P.l) (hu : m.failed = none) :
    ∃ t, openAtt P m = .ok t := by
  unfold planAtt planFlag at hp
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, ne_eq] at hp
  obtain ⟨⟨hl0, -⟩, hk, -⟩ := hp
  cases h : openAtt P m with
  | ok t => exact ⟨t, rfl⟩
  | error e =>
    exfalso
    unfold openAtt attFirstQuiet front at h
    simp [need, hB, hA, hl0, h0, hk, hl, bind, Except.bind, S.enterAtt?] at h
    exact unmarked_err h ((enterAtt_ok hB).2.2.2.2.2.trans hu)

/-- **Behind a layers' link's first call "opened" returns.** -/
theorem openLay_returns {shape : Params.ReqShape} {P : LayPar} (hp : planLay shape P = true)
    {m : S} (hB : m.atBetween = true) (hA : firstRun m.check = true)
    (h0 : m.check.frame.plain = []) (hl : m.check.frame.link = P.l) (hu : m.failed = none) :
    ∃ t, openLay P m = .ok t := by
  unfold planLay planFlag at hp
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, ne_eq] at hp
  obtain ⟨⟨⟨⟨⟨hl0, -⟩, hg⟩, hn⟩, hz⟩, hk, -⟩ := hp
  cases h : openLay P m with
  | ok t => exact ⟨t, rfl⟩
  | error e =>
    exfalso
    unfold openLay layFirstQuiet front at h
    simp [need, hB, hA, hl0, h0, hk, hl, ← hg, hn, hz, bind, Except.bind, S.enterLay?] at h
    exact unmarked_err h ((enterLay_ok hB).2.2.2.2.2.trans hu)

/-- **Row l's "opened" returns.** -/
theorem opened_returns {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} {f : LinkFrame} {l : Nat} (h : framesOf built first W = .ok fs)
    (hf : fs[l]? = some f) (hl0 : l ≠ 0)
    (hp : f.plan = true) {m : S} (hB : m.atBetween = true) (hA : firstRun m.check = true)
    (h0 : m.check.frame.plain = []) (hl : m.check.frame.link = l) (hu : m.failed = none) :
    ∃ t, f.opened m = .ok t := by
  rcases framesOf_arms h hf with ⟨X, -, -, e⟩ | ⟨e0, -⟩ |
    ⟨-, _, _, Q, -, -, -, eQ, ep, e, -⟩ | ⟨-, _, _, Q, -, -, -, eQ, ep, e, -⟩
  · rw [e]
    exact ⟨m, rfl⟩
  · exact absurd e0 hl0
  · rw [e]
    rw [ep] at hp
    exact openAtt_returns hp hB hA h0 (by rw [hl, eQ]) hu
  · rw [e]
    rw [ep] at hp
    exact openLay_returns hp hB hA h0 (by rw [hl, eQ]) hu

/-- Behind a yes of the kind's own decision in a link's dress. -/
theorem yes_frame {snd : _root_.Tw.K2.SendFn} {p : P2} {s u : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hp : p.stands = .link)
    (hy : decideWith snd p s rs gs = .ok u) :
    u.atBetween = true ∧ firstRun u.check = true ∧ u.check.frame.plain = [] ∧
      u.check.frame.link = s.check.frame.link ∧ u.failed = s.failed ∧ u.out = s.out := by
  obtain ⟨r₁, r₂, x, w, roots, S', f, mine, -, k⟩ := link_inv hp hy
  obtain ⟨_, _, _, _, a⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 k.hFront
  obtain ⟨_, b⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 k.hBehind
  have hb : u.here = .between := by rw [k.hOut]; exact k.hHere
  have h1 : u.atBetween = true := by
    unfold S.atBetween
    rw [hb]
  have h2 : firstRun u.check = true := by
    rw [k.hOut]
    rfl
  have h3 : u.check.frame.plain = [] := by
    rw [k.hOut]
    show f.plain = []
    rw [b.frame]
  have h4 : u.check.frame.link = s.check.frame.link := by
    rw [k.hOut]
    show f.link = _
    rw [b.frame]
    show x.f.link = _
    rw [a.out]
  exact ⟨h1, h2, h3, h4, by rw [k.hOut], by rw [k.hOut]⟩

/-- **The way out at a link's first place returns behind every yes.** -/
theorem leave_returns {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} {f : LinkFrame} {l : Nat} (h : framesOf built first W = .ok fs)
    (hf : fs[l]? = some f) (hl0 : l ≠ 0)
    (hpl : f.plan = true) {snd : _root_.Tw.K2.SendFn} {p : P2} {s u : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hp : p.stands = .link)
    (hy : decideWith snd p s rs gs = .ok u) (hl : s.check.frame.link = l)
    (hu : s.failed = none) : ∃ t, leaveOpened f s u = .ok t := by
  obtain ⟨hB, hA, h0, e1, e2, e3⟩ := yes_frame hp hy
  have hu' : u.failed = none := e2.trans hu
  obtain ⟨t, ht⟩ := opened_returns h hf hl0 hpl hB hA h0 (e1.trans hl) hu'
  have hk3 : t.failed = u.failed ∧ t.out = u.out := by
    rcases framesOf_arms h hf with ⟨X, -, -, e⟩ | ⟨e0, -⟩ |
      ⟨-, _, _, Q, -, -, -, -, -, e, -⟩ | ⟨-, _, _, Q, -, -, -, -, -, e, -⟩
    · rw [e] at ht
      obtain rfl : u = t := Except.ok.inj ht
      exact ⟨rfl, rfl⟩
    · exact absurd e0 hl0
    · rw [e] at ht
      have q := openAtt_ok ht
      exact ⟨q.2.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.2⟩
    · rw [e] at ht
      have q := openLay_ok ht
      exact ⟨q.2.2.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.2.2⟩
  refine ⟨t, (leaveOpened_iff f s u t).2 ⟨hu', ht, hk3.1.trans hu', ?_, ?_⟩⟩
  · show (u.out.reply == t.out.reply) = true
    rw [hk3.2]
    exact beq_self_eq_true _
  · show (s.out.reply == t.out.reply) = true
    rw [hk3.2, e3]
    exact beq_self_eq_true _

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.unmarked_err
#print axioms VerifiableInference.Desc.K2.Honest.Returns.openAtt_returns
#print axioms VerifiableInference.Desc.K2.Honest.Returns.openLay_returns
#print axioms VerifiableInference.Desc.K2.Honest.Returns.opened_returns
#print axioms VerifiableInference.Desc.K2.Honest.Returns.yes_frame
#print axioms VerifiableInference.Desc.K2.Honest.Returns.leave_returns
