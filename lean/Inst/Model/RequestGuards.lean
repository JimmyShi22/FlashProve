-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/RequestGuards.lean: sanity lemmas for the relation on a request (tokens, y, r, e): what
the inner relation (without `Head3`) says, that it reads r, e and the checked tokens, and
that on "the next token" it is R_inf at the reference settings. Theorems only; to audit the
relation `RinfPP` (Inst/Model/Scales.lean), nothing of this file need be read.
Inst/Model/ProgramR.lean: positions r ≤ t < e are covered; position t checks the token w_t =
x_(t+1), with x_T := y. `ModelS` (for an index: `RinfS0`) := the program runs, and at every covered
position the checked token is the least token of largest logit. At settings pp the inner relation
`RinfPP0` is the relation with a policy, at the settings' own policy `pp.pol`; at settings whose
policy is exact match it says the same as `RinfS0` (Inst/Model/Scales.lean: `rinfPP0_iff`;
Inst/Model/ProgramRExact.lean). With `Head3` (r < e ≤ T; y = 0 if e < T): `RinfS`, `RinfPP`; outside
Inst/Model/ `RinfPP` is named in Policy/Rel/LedgerRelLaws.lean (`Spec.ledger_lang`).
  1  `modelS_empty`: without a covered position (e ≤ r) the inner relation says "the program runs"
     and nothing else.
     `modelS_y`: for e < T the inner relation does not read y: it is true or false whatever y is.
     (`Head3` excludes the first and requires y = 0 in the second; neither is excluded by the inner
     relation.)
  2  `zero_iffS`, `zero_iff`: at the reference sizes, for all valid settings whose policy is exact
     match: at the all-zero index the inner relation says exactly "every checked token of a covered
     position is 0". So it reads r, e and each covered token, and y exactly where r < e = T.
     `zero_reads_y`, `zero_reads_token`, `zero_true_form`: single requests, at the all-zero index
     (that a wrong y is out for r < e = T other than "the next token": `zero_iff`, at exact match).
  3  `infR_next`: on the request "the next token after these tokens" the relation `Inf.R`
     (Inst/Model/Inf/Spec.lean: `RinfR0` at the reference scales, at exact match: without `Head3`)
     is R_inf (`Rinf ppref tbRef`).
  4  The same corner cases for the relation with a policy (`ModelR`):
     `modelR_empty` (e ≤ r: "the program runs" and nothing else, under every policy); `modelR_y`
     (for e < T it does not read y: Inst/Model/ProgramRPol.lean: `polOK_y_unread`). (That each of
     the policy's numbers is read: Inst/Model/ProgramRGuards.lean; that another policy than exact
     match admits more: Inst/Model/RequestGuards2.lean: `budget`.)
  5  The hidden numbers, the four claims (`dB4`, `dZ`, `sB2`, `sB3`) and the cells are defined in
     Inst/Model/Head/Trace.lean, the families of keys (`Fam`) in Inst/Model/Head/Index.lean.
     `hidden_last`: on "the next token" the four claims on the hidden numbers ((B4), (Z) at every
     position; (B2), (B3)) hold automatically, whatever the cells and the policy.
The all-zero index of part 2 is made up for these proofs.
-/
import Inst.Model.ScalesSanity
import Inst.Model.ScalesGuard
import Inst.Model.ProgramK
import Inst.Model.Head.TraceN

set_option autoImplicit false

namespace Inst.Model.RequestGuards

open ScalesSanity

/-! ## 1. The inner relation, without `Head3` -/

theorem modelS_empty (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables)
    (w : Weights) (x : Instance P) (h : x.e ≤ x.r) :
    ModelS P κ nf tbs w x ↔ RunsK P κ nf tbs w x.prompt :=
  ⟨fun hm => hm.1, fun hr => ⟨hr, fun _ h1 h2 => absurd (lt_of_le_of_lt h1 h2) (not_lt.2 h)⟩⟩

theorem modelS_y (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) (w : Weights)
    (x : Instance P) (y' : Fin P.V) (h : x.e < P.T) :
    ModelS P κ nf tbs w ⟨x.prompt, y', x.rF, x.eF⟩ ↔ ModelS P κ nf tbs w x := by
  have hw : ∀ t, t < x.e → (⟨x.prompt, y', x.rF, x.eF⟩ : Instance P).w t = x.w t := fun t ht => by
    unfold Instance.w Instance.tok
    rw [dif_pos (by omega), dif_pos (by omega)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun t hr he => by rw [← hw t he]; exact h2 t hr he⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun t hr he => by rw [hw t he]; exact h2 t hr he⟩

/-! ## 2. The relation reads r, e and the checked tokens -/

/-- At settings that are valid but for the clause K ≤ M (`LawfulBut`), at the all-zero index, "every
covered token is the least token of largest logit" says exactly: every checked token of a covered
position is 0. -/
theorem zero_iffS_but {pp : ScalesAndPolicy} (h : LawfulBut pp) (x : Instance ppref) :
    RinfS0 ppref pp.kap pp.nf (fun _ => tbRef) iZero x ↔ ∀ t, x.r ≤ t → t < x.e → x.w t = 0 := by
  have hrun : RunsK ppref pp.kap pp.nf (fun _ => tbRef) iZero.val x.prompt :=
    (zero_true_but h x.prompt).1
  have hl : ∀ t v, lgK ppref pp.kap pp.nf (fun _ => tbRef) iZero.val x.prompt t v = 0 :=
    fun t v => by simp [lgK, iZero, iW, dot_zero]
  have hg : ∀ t,
      gapOf ppref.V (lgK ppref pp.kap pp.nf (fun _ => tbRef) iZero.val x.prompt t) (x.w t) = 0 ↔
      x.w t = 0 := fun t => by
    rw [gapOf_eq_zero_iff _ _ (x.w_lt t)]
    constructor
    · rintro ⟨-, h2⟩
      by_contra hne
      have := h2 0 (Nat.pos_of_ne_zero hne)
      rw [hl, hl] at this
      exact lt_irrefl _ this
    · intro e
      refine ⟨fun v _ => by rw [hl, hl], fun v hv => ?_⟩
      rw [e] at hv
      exact absurd hv (Nat.not_lt_zero v)
  constructor
  · rintro ⟨-, h2⟩ t hr he
    exact (hg t).1 (h2 t hr he)
  · intro h2
    exact ⟨hrun, fun t hr he => (hg t).2 (h2 t hr he)⟩
theorem zero_iffS {pp : ScalesAndPolicy} (h : Lawful pp) (x : Instance ppref) :
    RinfS0 ppref pp.kap pp.nf (fun _ => tbRef) iZero x ↔ ∀ t, x.r ≤ t → t < x.e → x.w t = 0 :=
  zero_iffS_but h.toLawfulBut x

/-- At the all-zero index, at settings that are valid but for the clause K ≤ M (`LawfulBut`) and
whose policy is exact match, the inner relation says exactly: every checked token of a covered
position is 0. -/
theorem zero_iff_but {pp : ScalesAndPolicy} (h : LawfulBut pp) (hp : pp.pol = AcceptancePolicy.exact) (x : Instance ppref) :
    RinfPP0 pp iZero x ↔ ∀ t, x.r ≤ t → t < x.e → x.w t = 0 :=
  (rinfPP0_iff hp iZero x).trans (zero_iffS_but h x)
theorem zero_iff {pp : ScalesAndPolicy} (h : Lawful pp) (hp : pp.pol = AcceptancePolicy.exact) (x : Instance ppref) :
    RinfPP0 pp iZero x ↔ ∀ t, x.r ≤ t → t < x.e → x.w t = 0 :=
  zero_iff_but h.toLawfulBut hp x

/-- At the all-zero index, on the request "the next token", a wrong y is out: at all valid settings,
whatever their policy -/
theorem zero_reads_y {pp : ScalesAndPolicy} (h : Lawful pp)
    (prompt : Fin ppref.T → Fin ppref.V) (y : Fin ppref.V) :
    RinfPP0 pp iZero (Instance.nextOf prompt y) ↔ y.val = 0 := by
  refine (ModelR_congr_noCnt ppref _ _ _ pp.pol AcceptancePolicy.exact iZero.val _ (cnt_nextOf prompt y)).trans
    ((RinfS0_iff_exact ppref (by decide) _ _ _ iZero _).symm.trans ?_)
  rw [zero_iffS h]
  have hw : (Instance.nextOf prompt y).w (ppref.T - 1) = y.val :=
    (Instance.nextOf prompt y).w_last (by decide)
  constructor
  · intro h2
    rw [← hw]
    exact h2 (ppref.T - 1) (le_refl _) (show ppref.T - 1 < ppref.T by decide)
  · intro e t hr he
    have h1 : ppref.T - 1 ≤ t := hr
    have h2 : t < ppref.T := he
    obtain rfl : t = ppref.T - 1 := by omega
    rw [hw, e]

/-- At the all-zero index, valid settings and exact match a wrong token inside the stretch is out -/
theorem zero_reads_token {pp : ScalesAndPolicy} (h : Lawful pp) (hp : pp.pol = AcceptancePolicy.exact) (x : Instance ppref)
    {t : ℕ} (hr : x.r ≤ t) (he : t < x.e) (hw : x.w t ≠ 0) : ¬ RinfPP0 pp iZero x :=
  fun hx => hw ((zero_iff h hp x).1 hx t hr he)

/-- At the all-zero index and valid settings, the request "the next token" with y = 0 is in the
relation with `Head3`. -/
theorem zero_true_form {pp : ScalesAndPolicy} (h : Lawful pp) (prompt : Fin ppref.T → Fin ppref.V) :
    RinfPP pp iZero (Instance.nextOf prompt ⟨0, by decide⟩) :=
  (RinfPP_iff pp iZero _).2 ⟨head3_nextOf (by decide) prompt _, zero_true h prompt⟩

/-! ## 3. On "the next token" it is R_inf at the reference settings -/

theorem infR_next (i : Index ppref) (prompt : Fin ppref.T → Fin ppref.V) (y : Fin ppref.V) :
    Inf.R i (Instance.nextOf prompt y) ↔ Rinf ppref tbRef i (Instance.nextOf prompt y) :=
  (RinfS0_iff_exact ppref (by decide) _ _ _ i _).symm.trans <|
  (ModelS_nextOf ppref (by decide) _ _ _ i.val prompt y).trans
    (iff_of_eq (congrFun (congrFun (RinfK_const ppref tbRef) i) (Instance.nextOf prompt y)))

/-! ## 4. The corner cases, for the relation with a policy -/

theorem modelR_empty (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) (pol : AcceptancePolicy)
    (w : Weights) (x : Instance P) (h : x.e ≤ x.r) :
    ModelR P κ nf tbs pol w x ↔ RunsK P κ nf tbs w x.prompt :=
  ⟨fun hm => hm.1, fun hr => ⟨hr, polOK_of_le _ pol h⟩⟩

theorem modelR_y (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) (pol : AcceptancePolicy)
    (w : Weights) (x : Instance P) (y' : Fin P.V) (h : x.e < P.T) :
    ModelR P κ nf tbs pol w ⟨x.prompt, y', x.rF, x.eF⟩ ↔ ModelR P κ nf tbs pol w x :=
  ⟨fun hm => ⟨hm.1, polOK_y_unread _ pol ⟨x.prompt, y', x.rF, x.eF⟩ x.y h hm.2⟩,
    fun hm => ⟨hm.1, polOK_y_unread _ pol x y' h hm.2⟩⟩

/-! ## 5. On "the next token" the four claims on the hidden numbers hold automatically, and the
policy is not read -/

theorem hidden_last {K : Type} [CommRing K] (t : Head.Cells K) (pol : AcceptancePolicy)
    (prompt : Fin ppref.T → Fin ppref.V) (y : Fin ppref.V) :
    (∀ i,
      Head.dB4 t (Head.Req.of pol (Instance.nextOf prompt y)) i = 0 ∧
      Head.dZ t (Head.Req.of pol (Instance.nextOf prompt y)) i = 0) ∧
    Head.sB2 t (Head.Req.of pol (Instance.nextOf prompt y)) = 0 ∧
    Head.sB3 t (Head.Req.of pol (Instance.nextOf prompt y)) = 0 := by
  have hc : ∀ i, (Head.Req.of pol (Instance.nextOf prompt y)).rhoC i = 0 := fun i =>
    Head.Req.rhoC_last y.val i
  have hN : (Head.Req.of pol (Instance.nextOf prompt y)).NB = 0 := Head.Req.NB_of_rhoC _ hc
  refine ⟨fun i => ⟨?_, ?_⟩, ?_, ?_⟩
  · unfold Head.dB4
    rw [hc]; simp
  · unfold Head.dZ
    rw [hc]; simp
  · unfold Head.sB2
    simp [hc, hN]
  · unfold Head.sB3
    simp [hc, hN]

end Inst.Model.RequestGuards
