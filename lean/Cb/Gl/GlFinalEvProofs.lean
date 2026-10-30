-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/Gl/GlFinalEvProofs.lean: the proofs of the statements of
Cb/Gl/GlFinalEv.lean (`Cb.fmtPlain_fmt`;
`glEv_msgs` to `glEv_hyp` in `Cb.Gl`).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

In `fmtPlain_fmt`, `glEv_msgs` and `glEv_std` to `glEv_runJ` a record with forms in the place of
properties gives the record that it stands for; for `LayGlEv`, `ReqRefGlEv`, `FinalEv` no such
theorem is stated (the head of Cb/Gl/GlFinalEv.lean). By `Cb.evForm_ok` (an `Evader` of one of the
forms `Evader.Form` has `Evader.OK`), `Cb.bldSw_fill`, `Cb.smpForm_cf` (the row with a pad, or no
answer), `Cb.fmtPlain_fmt` (the plain format); inductions along towers and along the list of
segments. `glEv_hyp`: the proof of `Cb.Gl.glAt_finalHyp` with these in front. BCHKS46At F E is a
hypothesis by name of glEv_hyp alone, no axiom.

Terms: lean/GLOSSARY.md.
-/
import Cb.Gl.GlFinalEv

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- at the plain format the format's encoder is the code's -/
theorem plain_zk {E P : Type} [Field E] [Fintype E] [Fintype P] (C : LdCode E P) (Z : Sample E C.J)
    (e : ℕ) (rk : (C.J → E) × (C.Q → E) → ℕ) (x : Σ o : OMsg E, Hiop.Enc o.nat)
    (h : x = ⟨OMsg.plain C Z e rk, C.Nn⟩) (t : ℕ) :
    x.1.C.Zk t → x.2.Hides (x.1.C.budT t) := by
  subst h
  exact fun h => h

theorem fmtPlain_fmt : Spec.fmtPlain_fmt := fun _ _ _ _ _ _ _ N Y h =>
  ⟨h.enc, h.lay,
    fun a t =>
      plain_zk (N.om a).C (N.om a).Z (N.om a).e (N.om a).rank ⟨N.om a, Y.En a⟩ (h.plain a) t⟩

end Cb

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR IOR.Chain Cb.Ood
open scoped ENNReal

theorem glEv_msgs : Spec.glEv_msgs := fun Fp _ _ _ N Y _ _ _ h =>
  ⟨fmtPlain_fmt Fp E N Y h.fmt, h.smp, h.code, h.near⟩

theorem glEv_lay : Spec.glEv_lay := fun N t Fp _ _ _ Y h =>
  let ⟨d, hd⟩ := h.2.2
  gl_stdL_ok Fp N Y d t (fmtPlain_fmt Fp E N Y h.1) h.2.1 hd

theorem glEv_std : Spec.glEv_std := by
  rintro Kc a d ⟨Fp, i1, i2, i3, Y, dat, rst, bk₀, w0, dd, e, hb, hf, hM⟩
  exact ⟨Fp, i1, i2, i3, Y, dat, rst, bk₀, w0, dd, e, hb, hf, glEv_msgs Fp d.N Y d.L d.t dd hM⟩

theorem glEv_grp : Spec.glEv_grp := by
  rintro Kc D l ⟨iB, iP, Sh, Hd, Z, hc, dw, d, t, bC, bZ, bW, e, h1, hH, h2, h3, hZ, hF⟩
  exact ⟨iB, iP, Sh, Hd, Z, hc, dw, d, t, bC, bZ, bW, e, h1, hH, h2, h3, evForm_ok E _ Z hZ, hF⟩

theorem glEv_body : Spec.glEv_body := fun Kc _ A pp h =>
  { front := evRec_front E Kc _ A.V pp h.front, ok := h.ok, places := h.places, uniq := h.uniq,
    send1 := glEv_std Kc _ _ h.send1, send3 := glEv_std Kc _ _ h.send3, tabQ := h.tabQ,
    tabH := h.tabH, keys := h.keys, tags := h.tags, inj := h.inj, named := h.named, adm := h.adm,
    bits := h.bits, reads := h.reads, deg := h.deg, ev := evForm_ok E _ _ h.ev }

theorem glEv_seg : Spec.glEv_seg := fun Kc I _ _ pp h =>
  ⟨glEv_body Kc I _ pp h.body, evForm_ok E _ _ h.ev, h.named,
    glEv_grp Kc _ _ h.fold, glEv_std Kc _ _ h.snd⟩

theorem glEv_list : Spec.glEv_list := by
  intro Kc I a b L pp
  induction L with
  | nil => intro _; rw [ProtoGlL]; trivial
  | snoc L S ih =>
      intro h
      rw [ProtoGlLEv] at h
      rw [ProtoGlL]
      exact ⟨ih h.1, glEv_seg Kc I _ S pp h.2⟩

theorem glEv_tow3 : Spec.glEv_tow3 := by
  intro a T
  induction T with
  | base a t cov d => exact fun h => h
  | step Y sl e S d e' d' rest ih =>
    rintro ⟨h1, ⟨hN, hJ, hZo, hZb⟩, hr⟩
    exact ⟨h1,
      ⟨hN, hJ, (bldSw_fill E _ _ _ hZo).1, evForm_ok E _ _ hZb, (bldSw_fill E _ _ _ hZo).2⟩,
      ih hr⟩

theorem glEv_towG3 : Spec.glEv_towG3 := by
  intro B _ S G _ Sb sl Z T h
  cases T with
  | plain T => exact glEv_tow3 _ T h
  | shaped Sh Sw d e' d' rest =>
    obtain ⟨h1, h2, ⟨hN, hJ, hZo, hZb⟩, hr⟩ := h
    exact ⟨h1, h2,
      ⟨hN, hJ, (bldSw_fill E _ _ _ hZo).1, evForm_ok E _ _ hZb, (bldSw_fill E _ _ _ hZo).2⟩,
      glEv_tow3 _ rest hr⟩

theorem glEv_towJ : Spec.glEv_towJ := by
  intro a T
  induction T with
  | base a t cov d b => exact fun h => h
  | step Y sl e S d bC bZ bW e' d' rest ih =>
    rintro ⟨h1, ⟨hN, hJ, hZo, hZb⟩, hr⟩
    exact ⟨h1,
      ⟨hN, hJ, (bldSw_fill E _ _ _ hZo).1, evForm_ok E _ _ hZb, (bldSw_fill E _ _ _ hZo).2⟩,
      ih hr⟩

theorem glEv_towGJ : Spec.glEv_towGJ := by
  intro B _ S G _ Sb sl Z T h
  cases T with
  | plain T => exact glEv_towJ _ T h
  | shaped Sh Sw d bC bZ bW e' d' rest =>
    obtain ⟨h1, h2, ⟨hN, hJ, hZo, hZb⟩, hr⟩ := h
    exact ⟨h1, h2,
      ⟨hN, hJ, (bldSw_fill E _ _ _ hZo).1, evForm_ok E _ _ hZb, (bldSw_fill E _ _ _ hZo).2⟩,
      glEv_towJ _ rest hr⟩

theorem glEv_run3 : Spec.glEv_run3 := by
  rintro S D Tw d ⟨h1, h2, h3, hG, hlt, hF, hZ, hT⟩
  exact ⟨h1, h2, h3, hG, hlt, hF, evForm_ok E _ _ hZ, glEv_towG3 _ S D.G D.Sb D.sl D.Z Tw hT⟩

theorem glEv_runJ : Spec.glEv_runJ := by
  rintro S D Tw d ⟨h1, h2, h3, hG, hJ, hF, hZ, hT⟩
  exact ⟨h1, h2, h3, hG, hJ, hF, evForm_ok E _ _ hZ, glEv_towGJ _ S D.G D.Sb D.sl D.Z Tw hT⟩

theorem glEv_hyp : Spec.glEv_hyp := fun H X _ Fp _ _ _ _ _ _ a k msg r e mca h =>
  have mW := fun {Fq : Type} [Field Fq] [Fintype Fq] [Algebra Fq E] {N : Sig E} {Y : N.StdL Fq}
    {L t d : N.O → ℕ} (hm : MsgsGlEv N Y L t d) =>
      glReqJohn_msgs Fq N Y L t d (glEv_msgs Fq N Y L t d hm)
  { wfIs := h.wfIs
    sndIs := h.sndIs
    reqIs := h.reqIs
    onIs := h.onIs
    wfJ :=
      { isStd := h.wfStd, ok := (mW h.wfM).1, body := h.wfBody, bdDat := h.wfBd, plL := h.wfAtL,
        plB := h.wfAtB, noPad := h.wfNoPad, rest2 := evRec_rest2 F E X.Z.Zw p h.wfRest2
        conf3 := gl3_conf X.Z.Zw.W.Cf a k msg r e mca h.code h.ha h.hk h.hp h.h3
          (smpForm_cf F E _ _ _ h.smp) h.model
        near := (mW h.wfM).2 }
    sOff :=
      { places := h.plS, okW := (mW h.sW).1, okU := (mW h.sU).1, okO := (mW h.sO).1, fairW := h.fW,
        fairU := h.fU, fairO := h.fO
        nearW := (mW h.sW).2, nearU := (mW h.sU).2, nearO := (mW h.sO).2 }
    sLink := { ok := (mW h.sK).1, reads := h.rdK, fair := h.fK, near := (mW h.sK).2 }
    sOn :=
      { places := h.plB, okW := (mW h.sWB).1, okU := (mW h.sUB).1, okO := (mW h.sOB).1,
        fairW := h.fWB, fairU := h.fUB, fairO := h.fOB
        nearW := (mW h.sWB).2, nearU := (mW h.sUB).2, nearO := (mW h.sOB).2 }
    own₀ := h.own₀
    req :=
      { duty := h.req.duty
        std := ⟨glReqJohn_send X.Kc _ _ (glEv_std X.Kc _ _ h.req.std.1),
          glAt_reqList H X.Kc _ _ _ X.Ls p (glEv_list X.Kc _ _ _ X.Ls p h.req.std.2.1),
          glReqJohn_body X.Kc _ X.T.A p (glEv_body X.Kc _ X.T.A p h.req.std.2.2)⟩
        deg := h.req.deg, ev := evForm_ok E _ _ h.req.ev, tie := h.req.tie, own := h.req.own,
          layD := h.req.layD, fmt := h.req.fmt
        bFirst := h.req.bFirst, bSegs := h.req.bSegs, bTail := h.req.bTail, bLast := h.req.bLast }
    places := h.places
    pl₁ := h.pl₁
    pK := gl3_runAt _ _ _ (glEv_run3 _ _ _ _ h.tK)
    p₁ := gl3_runAt _ _ _ (glEv_run3 _ _ _ _ h.t₁)
    p₂ := gl3_runAt _ _ _ (glEv_run3 _ _ _ _ h.t₂)
    p₃ := gl3_runAt _ _ _ (glEv_run3 _ _ _ _ h.t₃)
    p₁B := glAt_runAt H _ _ _ _ (glEv_runJ _ _ _ _ h.t₁B)
    p₂B := glAt_runAt H _ _ _ _ (glEv_runJ _ _ _ _ h.t₂B)
    p₃B := glAt_runAt H _ _ _ _ (glEv_runJ _ _ _ _ h.t₃B) }

end Cb.Gl
