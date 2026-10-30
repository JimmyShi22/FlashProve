-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
LPFK9R/SharesPt.lean: THE TWO OF OUR FOUR SHARES THAT STILL HAVE A
PREMISE ON THE VERIFIER's STATE IN FRONT (the frame's sub-protocol behind the batching: «the one sum
can be taken» behind; the one equation: hg and «no message of the link's own is the index masks'
message»), IN THE POINTWISE FORM (IMR/HandsPoint.lean: `HandsPt`: what one sub-protocol owes at
ONE state in front) AND SO IN THE FORM WITH A FENCE (IMR/HandsFence.lean: `HandsR Fk`): the
premises are asked at that one state, or where the fence holds. Definitions and theorems.

What is said.
  `pinE E k s`: E, with «the state is s» beside it at border k alone. `pin_next`, `pin_here`,
    `pin_true`, `xk_pin`, `xk_of_pin`. `handsPt_of_pin`: **a share at `pinE E k s` is the pointwise
    share at E and s**: so a theorem whose premises run over all states in front serves pointwise,
    as it stands. `behind_Pt`, `close0_Pt`: **the two shares at one state in front.** `behind_R`,
    `close0_R`: **the two shares with a fence Fk**: each premise is asked only where Fk holds.

Limits. The premises are weaker than SharesAtE.lean's, not paid; «the base's tests answer alike at
any two states» stands as there. `pinE` decides a sentence on states by the classical axiom: it is a
tool of the proof and stands in no statement's end. THIRD ISSUE: the three premises on the state in
front are asked only where that state bears no mark (and «the one sum can be taken» only where the
state behind bears none): a reader's mend: the facts along the run that are meant to pay them stand
under «no mark». Nothing on soundness.

-/
import Johnson.LPFK9R.SharesAtE
import Johnson.IMR.HandsPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFK9.HandsAt
open VerifiableInference.Desc
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.K9 (atS Where messageNow)
open VerifiableInference.Desc.Sound (moreAll)
open VerifiableInference.Desc.First (S ModelPart Numbers Pub PubData pubAll rowsAtFit)
open IM (linksW placesW nAt)

open Classical in
/-- E, with «the state is s» beside it at border k alone. -/
noncomputable def pinE (E : ℕ → S → Bool) (k : ℕ) (s : S) : ℕ → S → Bool :=
  fun j t => E j t && decide (j = k → t = s)

section
variable {N : Numbers} {links : List ModelPart} {ps : List Place} {E : ℕ → S → Bool} {ft k : ℕ}
  {b : Block S ProofFile.Cl} {s : S}

theorem pin_next (t : S) : pinE E k s (k + 1) t = E (k + 1) t := by
  simp [pinE]

theorem pin_here : pinE E k s k s = E k s := by
  simp [pinE]

theorem pin_true {t : S} (h : pinE E k s k t = true) : t = s ∧ E k t = true := by
  simp only [pinE, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.2 trivial, h.1⟩

theorem xk_pin (h : IM.XK N links ps E k s = true) : IM.XK N links ps (pinE E k s) k s = true := by
  unfold IM.XK at *
  rw [pin_here]
  exact h

theorem xk_of_pin {t : S} (h : IM.XK N links ps (pinE E k s) k t = true) :
    t = s ∧ IM.XK N links ps E k t = true := by
  unfold IM.XK at h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨e, h3⟩ := pin_true h2
  refine ⟨e, ?_⟩
  unfold IM.XK
  rw [h1, h3]
  rfl

/-- **A share at pinE E k s is the pointwise share at E and s.** -/
theorem handsPt_of_pin (H : IM.Hands N links ps (pinE E k s) ft k b) :
    IM.HandsPt N links ps E ft k b s :=
  ⟨fun s' hy => H.mark s s' hy, fun s' hy h0 h1 hx => H.shape s s' hy h0 h1 (xk_pin hx),
    fun s' hy h0 h1 hx => H.rows s s' hy h0 h1 (xk_pin hx),
    fun s' hy h0 h1 hx => H.members s s' hy h0 h1 (xk_pin hx),
    fun s' hy h0 h1 hx => H.book s s' hy h0 h1 (xk_pin hx),
    fun s' hy h0 h1 hx => by
      have h := H.more s s' hy h0 h1 (xk_pin hx)
      rwa [pin_next] at h⟩

end

variable {P : Type} (D : PubData) (base : Pub → P × S → Bool) (z : P)
variable {N : Numbers} {ft : ℕ} (hb : ∀ q (s s' : S), base q (z, s') = base q (z, s))

include hb

/-- **THE FIELD «behind», AT ONE STATE IN FRONT.** -/
theorem behind_Pt {l : ℕ} (hl : l < 25) (Lk : Link S ProofFile.Cl) (pp : Where) (h : LinkShare Lk pp)
    (hT : N.treesAt placesW[14 * l + nAt l + 3 + 1]? = N.treesAt placesW[14 * l + nAt l + 3]?)
    (hM : N.msgsAt placesW[14 * l + nAt l + 3 + 1]? = N.msgsAt placesW[14 * l + nAt l + 3]?)
    (s : S)
    (htot : ∀ s', IM.Yes ft Lk.behindB s s' → s.failed = none → s'.failed = none →
      IM.XK N linksW placesW (EW D base z) (14 * l + nAt l + 3) s = true →
      pubAll D base (.totalIn l) (z, s') = true)
    (b : Block S ProofFile.Cl) (hr : b.rounds = [])
    (hd : ∀ s rs gs, b.decide s rs gs = Lk.runBehind s) :
    IM.HandsPt N linksW placesW (EW D base z) ft (14 * l + nAt l + 3) b s := by
  obtain ⟨p, p', h1, _, h3, h4⟩ := place_W (l := l) (i := 1) hl (by omega)
  refine handsPt_of_pin (behind_W hl Lk pp h.two hT hM (fun t t' hy hf hf' hx => ?_) b hr hd)
  obtain ⟨rfl, hx'⟩ := xk_of_pin hx
  obtain ⟨rs, cols, n, hstep⟩ := hy
  rw [pin_next]
  exact e_behind D base linksW placesW z hb _ l p pubFit9_W h1 h3 h4 Lk pp h ft t rs cols t' n hstep
    (htot t' ⟨rs, cols, n, hstep⟩ hf hf' hx') (IM.xk_parts hx').2.2.2.2

/-- **THE FIELD «close» AT j = 0, AT ONE STATE IN FRONT.** -/
theorem close0_Pt {l : ℕ} (hl : l < 25) (hN : rowsAtFit N 25 = true) (pw : Where)
    (Q : First.Close.Par)
    (hT : N.treesAt placesW[14 * l + nAt l + 4 + 0 + 1]? =
      N.treesAt placesW[14 * l + nAt l + 4 + 0]?)
    (hM : N.msgsAt placesW[14 * l + nAt l + 4 + 0 + 1]? =
      N.msgsAt placesW[14 * l + nAt l + 4 + 0]?)
    (s : S)
    (hg : s.failed = none → ∀ a,
      IM.XK N linksW placesW (EW D base z) (14 * l + nAt l + 4 + 0) s = true →
      atS.get? s = some a → N.groupAt l = a.L.check.group)
    (hne : s.failed = none →
      IM.XK N linksW placesW (EW D base z) (14 * l + nAt l + 4 + 0) s = true →
      ∀ a, atS.get? s = some a → ∀ m' o,
        messageNow a.L.check.frame a.L.check.frame.link m' = some o → o ≠ s.out.indexMasks)
    (x : Block S Unit) (hx : (K9.closeOf pw Q : List (Block S Unit))[0]? = some x) :
    IM.HandsPt N linksW placesW (EW D base z) ft (14 * l + nAt l + 4 + 0)
      (x.retype : Block S ProofFile.Cl) s := by
  obtain ⟨p, p', h1, _, h3, h4⟩ := place_W (l := l) (i := 2) hl (by omega)
  by_cases hf : s.failed = none
  · refine handsPt_of_pin (close0_W hl hN pw Q hT hM (fun t a hxk ha => ?_)
      (fun t t' hy _ _ hxk => ?_) x hx)
    · obtain ⟨rfl, hx'⟩ := xk_of_pin hxk
      exact hg hf a hx' ha
    · obtain ⟨rfl, hx'⟩ := xk_of_pin hxk
      obtain ⟨rs, cols, n, hstep⟩ := hy
      rw [pin_next]
      exact e_eq D base linksW placesW z hb _ l p pubFitE_W h1 h3 h4 pw _ (fun _ _ _ _ _ e => e)
        ft t rs cols t' n hstep (hne hf hx') (IM.xk_parts hx').2.2.2.2
  · have H0 : IM.Hands N linksW placesW (fun _ _ => false) ft (14 * l + nAt l + 4 + 0)
        (x.retype : Block S ProofFile.Cl) :=
      close0_W hl hN pw Q hT hM
        (fun t a hxk _ => absurd (IM.xk_parts hxk).2.2.2.2 Bool.false_ne_true)
        (fun t t' _ _ _ hxk => absurd (IM.xk_parts hxk).2.2.2.2 Bool.false_ne_true) x hx
    exact ⟨fun s' hy hm => H0.mark s s' hy hm, fun _ _ h0 => absurd h0 hf,
      fun _ _ h0 => absurd h0 hf, fun _ _ h0 => absurd h0 hf, fun _ _ h0 => absurd h0 hf,
      fun _ _ h0 => absurd h0 hf⟩

variable (Fk : ℕ → S → Prop)

/-- **THE FIELD «behind», WITH A FENCE.** -/
theorem behind_R {l : ℕ} (hl : l < 25) (Lk : Link S ProofFile.Cl) (pp : Where) (h : LinkShare Lk pp)
    (hT : N.treesAt placesW[14 * l + nAt l + 3 + 1]? = N.treesAt placesW[14 * l + nAt l + 3]?)
    (hM : N.msgsAt placesW[14 * l + nAt l + 3 + 1]? = N.msgsAt placesW[14 * l + nAt l + 3]?)
    (htot : ∀ s s', Fk (14 * l + nAt l + 3) s → IM.Yes ft Lk.behindB s s' → s.failed = none →
      s'.failed = none → IM.XK N linksW placesW (EW D base z) (14 * l + nAt l + 3) s = true →
      pubAll D base (.totalIn l) (z, s') = true)
    (b : Block S ProofFile.Cl) (hr : b.rounds = [])
    (hd : ∀ s rs gs, b.decide s rs gs = Lk.runBehind s) :
    IM.HandsR Fk N linksW placesW (EW D base z) ft (14 * l + nAt l + 3) b :=
  IM.handsR_iff_pt.2 fun s f =>
    behind_Pt D base z hb hl Lk pp h hT hM s (fun s' => htot s s' f) b hr hd

/-- **THE FIELD «close» AT j = 0, WITH A FENCE.** -/
theorem close0_R {l : ℕ} (hl : l < 25) (hN : rowsAtFit N 25 = true) (pw : Where)
    (Q : First.Close.Par)
    (hT : N.treesAt placesW[14 * l + nAt l + 4 + 0 + 1]? =
      N.treesAt placesW[14 * l + nAt l + 4 + 0]?)
    (hM : N.msgsAt placesW[14 * l + nAt l + 4 + 0 + 1]? =
      N.msgsAt placesW[14 * l + nAt l + 4 + 0]?)
    (hg : ∀ s a, Fk (14 * l + nAt l + 4 + 0) s → s.failed = none →
      IM.XK N linksW placesW (EW D base z) (14 * l + nAt l + 4 + 0) s = true →
      atS.get? s = some a → N.groupAt l = a.L.check.group)
    (hne : ∀ s, Fk (14 * l + nAt l + 4 + 0) s → s.failed = none →
      IM.XK N linksW placesW (EW D base z) (14 * l + nAt l + 4 + 0) s = true →
      ∀ a, atS.get? s = some a → ∀ m' o,
        messageNow a.L.check.frame a.L.check.frame.link m' = some o → o ≠ s.out.indexMasks)
    (x : Block S Unit) (hx : (K9.closeOf pw Q : List (Block S Unit))[0]? = some x) :
    IM.HandsR Fk N linksW placesW (EW D base z) ft (14 * l + nAt l + 4 + 0)
      (x.retype : Block S ProofFile.Cl) :=
  IM.handsR_iff_pt.2 fun s f =>
    close0_Pt D base z hb hl hN pw Q hT hM s (fun h0 a => hg s a f h0) (hne s f) x hx

end LPFK9.HandsAt

#print axioms LPFK9.HandsAt.handsPt_of_pin
#print axioms LPFK9.HandsAt.behind_Pt
#print axioms LPFK9.HandsAt.close0_Pt
#print axioms LPFK9.HandsAt.behind_R
#print axioms LPFK9.HandsAt.close0_R
