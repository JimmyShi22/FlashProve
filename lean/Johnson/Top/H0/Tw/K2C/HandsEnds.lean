-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/HandsEnds.lean: code switching (the kind K2): AT THE HEAD's LINK (the whole
place «H:2») AND AT THE FINISH («F:1»): behind an accept, three of the table of joints' four fixed
tests on the verifier's state accept: rowsHeld · membersHeld · bookAt. By core_three
(K2C/HandsCore.lean). NO BLOCK IMPORTS THIS FILE.
  switch_numbers_gain   the numbers that the switch itself joins are n0, n0 + 1, … (1 + K)
  HeadFresh s     the group that the head's own part of the state names is there and has no row,
                  no member, no flag, and its proximity test has not begun
  head_three      p.stands = .head · the decision accepts from s to m · "H.1.quiet" accepts from m
                  to u · HeadFresh s · N.groupAt mm = p.grp · bookAt in front · the closed facts
                  on the open set behind · SwitchDebts at n := 1 + K + the link's own messages of
                  moment 0: the three tests accept at u
  finish_three    p.stands = .finish · the way in "F.0.front" accepts from s to t · the decision
                  from t to t' · "F.0.quiet" from t' to u · the like, at n := 1 + K: the three
                  tests accept at u. (That the group is fresh is no premise there: the way in has
                  just pushed it.)
LIMITS. HeadFresh and SwitchDebts are met by nobody here. No soundness is claimed.

-/
import Johnson.Top.H0.Tw.K2C.HandsCore
import Johnson.Top.H0.Tw.K2C.BookKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place)
open _root_.Tw.K2 (sendByL8 switchNotices)

theorem switch_numbers_gain (x : _root_.Tw.K2.Front) : (switchGain x).map (·.1) =
    (List.range (1 + x.T.kept.size)).map (· + x.st.oracles.size) := by
  rw [range_shift]
  unfold switchGain
  rw [List.map_cons, List.map_map]
  have : ((fun p : Nat × Bool => p.1) ∘ fun p : Nat × KeptTarget => (p.1, p.2.keptAgain)) =
      Prod.fst := rfl
  rw [this, List.map_fst_zip (by simp)]
  simp

/-- The group that the head's own part of the state names is fresh. -/
def HeadFresh (s : S) : Prop :=
  ∀ a, s.here = .head a → ∃ G : Group, s.st.groups[a.fr.group]? = some G ∧ G.rows = #[] ∧
    G.members = #[] ∧ G.kept = #[] ∧ G.inRun = false

theorem head_three {p : P2} {P : HeadPar} {s m u : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hp : p.stands = .head)
    (h₁ : decideWith sendByL8 p s [r₁, r₂] gs = .ok m) (h₂ : headOpenQ P m = .ok u)
    (fresh : HeadFresh s) (N : Numbers) (mm : Nat) (pIn pOut : Option Place) (O' : List Item)
    (hO : O'.filter Item.isRow = switchRowsOpen mm) (hP0 : O'.contains (.pin mm 0) = true)
    (hP1 : O'.contains (.pin mm 1) = false) (hP2 : O'.contains (.pin mm 2) = false)
    (hgrp : N.groupAt mm = p.grp) (hb : bookAt N pIn s = true)
    (D : ∀ x W lay, frontAt p s = some x → frameAt x = some W →
      layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N mm pIn pOut s.book.trees.size r₂.drawn.poss.length
        (1 + x.T.kept.size + x.own.length) x W lay) :
    rowsHeld N O' u = true ∧ membersHeld N O' u = true ∧ bookAt N pOut u = true := by
  obtain ⟨a, G₀, ha, hG₀, HG⟩ := head_place_groups hp h₁ h₂
  obtain ⟨G, hG, f1, f2, f3, f4⟩ := fresh a ha
  have GA := HG G hG f2 f3
  have hfx : frontAt p s = some (headFrontOf s a G₀.target) := by
    unfold frontAt
    rw [hp, ha]
    simp only
    rw [hG₀]
    rfl
  obtain ⟨x1, y, S3, Y, rows, GAy, c, A⟩ := yes_whole p s r₁ r₂ gs m h₁
  obtain rfl : headFrontOf s a G₀.target = x1 := Option.some.inj (hfx.symm.trans A.front)
  have hf : GAy.rows = #[] := by
    have e := A.before
    rw [show (headFrontOf s a G₀.target).st.groups[(headFrontOf s a G₀.target).f.group]? =
      some G from hG] at e
    exact (Option.some.inj e).symm.trans f1
  obtain ⟨a2, st, f, mine, L, out, yy, cov, s₁, b, q⟩ := (headOpenQ_iff P m u).1 h₂
  have hust : u.st = st := by rw [q.out']
  have hRows : ∀ i : Nat, (u.st.groups[i]?).map (·.rows) = (m.st.groups[i]?).map (·.rows) := by
    rw [hust]
    exact (first_keeps q.behind).2
  obtain ⟨G1, Gu, hG1, hGu, em, _⟩ := GA.2.2
  obtain rfl : G = G1 := Option.some.inj (hG.symm.trans hG1)
  have hRun : Gu.inRun = false := by
    obtain ⟨x4, hf4, R⟩ := yes_rs h₁
    obtain rfl : headFrontOf s a G₀.target = x4 := Option.some.inj (hfx.symm.trans hf4)
    have e := (R.trans (behind_rs q.behind)) a.fr.group
    rw [← hust, hGu, show (headFrontOf s a G₀.target).st.groups[a.fr.group]? = some G from hG] at e
    exact (Option.some.inj e).trans f4
  obtain ⟨x2, lay, hF, hlay, _, St⟩ := yes_seated h₁
  obtain rfl : headFrontOf s a G₀.target = x2 := by
    rcases hF with ⟨e, _⟩ | ⟨_, a', G', ha', hG', e⟩ | ⟨e, _⟩
    · rw [hp] at e; cases e
    · rw [ha] at ha'
      injection ha' with ha'
      subst ha'
      rw [hG₀] at hG'
      obtain rfl := Option.some.inj hG'
      exact e.symm
    · rw [hp] at e; cases e
  obtain ⟨x3, hF3, _, _, zO, _⟩ := yes_size h₁
  obtain rfl : headFrontOf s a G₀.target = x3 := by
    rcases hF3 with ⟨e, _⟩ | ⟨_, a', G', ha', hG', e⟩ | ⟨e, _⟩
    · rw [hp] at e; cases e
    · rw [ha] at ha'
      injection ha' with ha'
      subst ha'
      rw [hG₀] at hG'
      obtain rfl := Option.some.inj hG'
      exact e.symm
    · rw [hp] at e; cases e
  have hag : a.fr.group = p.grp := by
    obtain ⟨_, _, a', _, _, _, _, k⟩ := head_inv hp h₁
    have e := k.hHere
    rw [ha] at e
    injection e with e
    rw [e]
    exact k.hGrp
  have hoth : (headFrontOf s a G₀.target).others.size =
      (headFrontOf s a G₀.target).own.length + 1 := by
    simp [headFrontOf, ReqFrame.notices]
  refine core_three A hf hRows hGu hRun (n := 1 + (headFrontOf s a G₀.target).T.kept.size +
    (headFrontOf s a G₀.target).own.length) ?_ (lay :=
        lay) (by rw [(headOpenQ_book h₂).1]; exact St)
    (by rw [notices_size]; omega) (by rw [headOpenQ_size h₂, zO]; rfl) N mm pIn pOut O' hO hP0 hP1
    hP2 (by rw [hgrp, ← hag]; rfl) hb fun W hW => D _ W lay hfx hW hlay
  rw [em, f2]
  simpa using gain_numbers (headFrontOf s a G₀.target)

theorem finish_three {p : P2} {s t t' u : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hp : p.stands = .finish)
    (he : finishFrontQ s = .ok t) (h₁ : decideWith sendByL8 p t [r₁, r₂] gs = .ok t')
    (h₂ : finishBehindQ t' = .ok u) (N : Numbers) (mm : Nat) (pIn pOut : Option Place)
    (O' : List Item) (hO : O'.filter Item.isRow = switchRowsOpen mm)
    (hP0 : O'.contains (.pin mm 0) = true) (hP1 : O'.contains (.pin mm 1) = false)
    (hP2 : O'.contains (.pin mm 2) = false) (hgrp : N.groupAt mm = p.grp)
    (hb : bookAt N pIn s = true)
    (D : ∀ x W lay, frontAt p t = some x → frameAt x = some W →
      layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N mm pIn pOut s.book.trees.size r₂.drawn.poss.length (1 + x.T.kept.size) x W
        lay) :
    rowsHeld N O' u = true ∧ membersHeld N O' u = true ∧ bookAt N pOut u = true := by
  obtain ⟨a, G₀, ha, hG₀, HG⟩ := yes_finish_groups hp h₁
  obtain ⟨a0, _, ha0, _, _, _, _, _, _, _, _, hg0⟩ := finishFrontQ_fr he
  obtain rfl : a = a0 := by
    rw [ha] at ha0
    injection ha0
  have hst := finishFrontQ_st he
  obtain ⟨rb, _, _, _, _, _, _⟩ := finishFrontQ_rest he
  have hG : t.st.groups[a.fr.group]? =
      some (freshGroup s.check.frame.shape.code s.check.frame.shape.maskCode) := by
    rw [hst, hg0]
    simp [withFresh]
  have GA := HG _ hG rfl rfl
  have hfx : frontAt p t = some (finFrontOf t a G₀) := by
    unfold frontAt
    rw [hp, ha]
    simp only
    rw [hG₀]
    rfl
  obtain ⟨x1, y, S3, Y, rows, GAy, c, A⟩ := yes_whole p t r₁ r₂ gs t' h₁
  obtain rfl : finFrontOf t a G₀ = x1 := Option.some.inj (hfx.symm.trans A.front)
  have hf : GAy.rows = #[] := by
    have e := A.before
    rw [show (finFrontOf t a G₀).st.groups[(finFrontOf t a G₀).f.group]? = _ from hG] at e
    exact (Option.some.inj e).symm
  obtain ⟨af, mk, _, _, rfl⟩ := (finishBehindQ_iff t' u).1 h₂
  obtain ⟨G1, Gu, hG1, hGu, em, _⟩ := GA.2.2
  obtain rfl := Option.some.inj (hG.symm.trans hG1)
  have hRun : Gu.inRun = false := by
    obtain ⟨x4, hf4, R⟩ := yes_rs h₁
    obtain rfl : finFrontOf t a G₀ = x4 := Option.some.inj (hfx.symm.trans hf4)
    have e := R a.fr.group
    rw [hGu, show (finFrontOf t a G₀).st.groups[a.fr.group]? = _ from hG] at e
    exact Option.some.inj e
  obtain ⟨x2, lay, hF, hlay, _, St⟩ := yes_seated h₁
  obtain rfl : finFrontOf t a G₀ = x2 := by
    rcases hF with ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, a', G', ha', hG', e⟩
    · rw [hp] at e; cases e
    · rw [hp] at e; cases e
    · rw [ha] at ha'
      injection ha' with ha'
      subst ha'
      rw [hG₀] at hG'
      obtain rfl := Option.some.inj hG'
      exact e.symm
  obtain ⟨x3, hF3, _, _, zO, _⟩ := yes_size h₁
  obtain rfl : finFrontOf t a G₀ = x3 := by
    rcases hF3 with ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, a', G', ha', hG', e⟩
    · rw [hp] at e; cases e
    · rw [hp] at e; cases e
    · rw [ha] at ha'
      injection ha' with ha'
      subst ha'
      rw [hG₀] at hG'
      obtain rfl := Option.some.inj hG'
      exact e.symm
  have hag : a.fr.group = p.grp := by
    obtain ⟨_, _, a', _, _, _, _, k⟩ := finish_inv hp h₁
    have e := k.hHere
    rw [ha] at e
    injection e with e
    rw [e]
    exact k.hGrp
  have hbt : bookAt N pIn t = true := by
    unfold bookAt at hb ⊢
    rw [rb, finishFrontQ_size he]
    exact hb
  refine core_three A hf (fun _ => rfl) hGu hRun (n := 1 + (finFrontOf t a G₀).T.kept.size) ?_
    (lay := lay) St (by rw [notices_size]; omega) zO N mm pIn pOut O' hO hP0 hP1
    hP2 (by rw [hgrp, ← hag]; rfl) hbt fun W hW => by
      rw [rb]
      exact D _ W lay hfx hW hlay
  rw [em]
  simpa [freshGroup] using switch_numbers_gain (finFrontOf t a G₀)

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.head_three
#print axioms VerifiableInference.Desc.First.K2.finish_three
