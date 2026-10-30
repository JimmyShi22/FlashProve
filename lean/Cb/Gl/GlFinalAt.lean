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
Cb/Gen/CodeListRS.lean.) Cb/Gl/GlFinalAt.lean: the conditions `Final` (Cb/Gl/GlFinal.lean) over p =
2^64 - 2^32 + 1 give the generic hypotheses on the protocol object, under the hypothesis
`Cb.BCHKS46At F E` on mutual correlated agreement, which is stated at one field.

Exactly: the record of conditions over p
(`Cb.Gl.Final`: Cb/Gl/GlFinal.lean) gives the generic record Z.HypRefJU under the statement on codes
(`Cb.BCHKS46At`, Cb/Gen/CodeListRSAt.lean) at one field.

Statements (`Cb.Gl.Spec.glAt_reqFold`, `glAt_reqSeg`, `glAt_reqList`, `glAt_finalReq`,
`glAt_finalHyp`) and proofs. They are the analogues of `Spec.glReqJohn_fold`, `Spec.glReqJohn_seg`,
`Spec.glReqJohn_list` (Cb/GlVal/GlReqJohn.lean) and `glFinal_req`, `glFinal_hyp`
(Cb/Gl/GlFinal.lean), with BCHKS46At F E in the place of BCHKS46F F; the proofs rest on
Cb/Gl/GlLdJAt.lean. No notion is defined here: `IsGrpGl`, `ProtoGlS`, `ProtoGlL`, `ReqRefGlU`,
`Final`, `LayGl` are those files'.

The hypothesis. Cb.BCHKS46At F E (Cb/Gen/CodeListRSAt.lean): mutual correlated agreement of
Reed-Solomon codes below the Johnson radius, for two words, over E alone, points in F: by reading,
the write-up's own restatement of the assumed theorem. It follows from BCHKS46F F
(`Cb.bchks46At_of_F`), so it is the weaker hypothesis. Stated, as a case, in the source named at the
head of this comment, with an outline of a proof; NOT proved here; NO axiom: it stands in the text
of each statement.

Limits: what the heads of Cb/GlVal/GlReqJohn.lean, Cb/Gl/GlFinJ.lean and Cb/Gl/GlFinal.lean list as
not said is not said here either. This file does not say that `Final` can be met: no instance in
this file.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Gl.GlLdJAt
import Cb.Gl.GlFinal

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR IOR.Chain Cb.Ood
open scoped ENNReal

namespace Spec

def glAt_reqFold : Prop :=
  Cb.BCHKS46At F E →
  ∀ (Kc : Type) (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid), IsGrpGl D l → D.IsGrpJ l

def glAt_reqSeg : Prop :=
  Cb.BCHKS46At F E →
  ∀ (Kc : Type) (I : LdRefIx E) (a : LdStage E Kc) (S : LdRefS E Kc I a) (pp : ℕ),
    ProtoGlS S pp → S.ProtoJ pp

def glAt_reqList : Prop :=
  Cb.BCHKS46At F E →
  ∀ (Kc : Type) (I : LdRefIx E) (a b : LdStage E Kc) (L : LdRefL E Kc I a b) (pp : ℕ),
    ProtoGlL pp L → L.ProtoJ pp

def glAt_finalReq : Prop :=
  Cb.BCHKS46At F E →
  ∀ (Kc : Type) (pp : ℕ) (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞),
    ReqRefGlU pp R core first b L T qφ q κ → LdReqRefDJU LayGl pp R core first b L T qφ q κ

/-- The generic record, at this field, under the statement on codes (`Cb.BCHKS46At`) at one field.
(not all hypotheses are named here: see the statement below) -/
def glAt_finalHyp : Prop :=
  Cb.BCHKS46At F E →
  ∀ (X : LdFinJ F E) [∀ b, Fintype (X.Z.Zw.K.wfI X.Z.Zw.Rl b → E)] (Fp : Type) [Field Fp]
      [Fintype Fp] [Algebra Fp E] (V : X.Z.Zw.StdW Fp) (p₀ : LdLinPl X.R.O.d.ol.toC)
      (plR : X.R.Bn → X.R.S.Ent → Prop) (a k msg r e mca : ℕ),
    Final X V p₀ plR a k msg r e mca →
    X.Z.HypRefJU LayGl p X.R X.core X.first X.c X.Ls X.T X.qφ X.q X.κ V p₀ plR

end Spec

theorem glAt_reqFold : Spec.glAt_reqFold := by
  rintro H Kc D l
    ⟨iB, iP, Sh, Hd, Z, hc, dw, d, t, bC, bZ, bW, e, ⟨hv, hm1, hm2, hz, h1⟩, hH, ⟨hC, hZb, hW, hJ⟩,
      ⟨hi, hn, hp, hq⟩, hZ, hF⟩
  have hS : Sh.OK :=
    ⟨hv, (glC_code _ _ d 0 (glJ_glC _ _ d 0 D.G.e bC hC)).1, (glC_code _ _ d 0 (glJ_glC _ _ d 0 D.G.e bZ hZb)).1, fun r => by
      split
      · next b hb => exact hm1 r b hb
      · next j hj => exact hm2 r j hj, hz, h1⟩
  exact ⟨iB, iP, Sh, Hd, Z, hc, dw, d, t, bC, bZ, bW, e, hS, hH,
    glAt_groupPar H _ _ Sh d t bC bZ bW hC hZb hW hJ hi hn hp hq, hZ, hF⟩

theorem glAt_reqSeg : Spec.glAt_reqSeg := fun H Kc I _ _ pp h =>
  ⟨glReqJohn_body Kc I _ pp h.body, h.ev, h.named,
    glAt_reqFold H Kc _ _ h.fold, glReqJohn_send Kc _ _ h.snd⟩

theorem glAt_reqList : Spec.glAt_reqList := by
  intro H Kc I a b L pp
  induction L with
  | nil => intro _; rw [LdRefL.ProtoJ]; trivial
  | snoc L S ih =>
      intro h
      rw [ProtoGlL] at h
      rw [LdRefL.ProtoJ]
      exact ⟨ih h.1, glAt_reqSeg H Kc I _ S pp h.2⟩

theorem glAt_finalReq : Spec.glAt_finalReq := fun H Kc pp _ _ _ _ L T _ _ _ h =>
  { duty := h.duty,
    std := ⟨glReqJohn_send Kc _ _ h.std.1,
        glAt_reqList H Kc _ _ _ L pp h.std.2.1,
        glReqJohn_body Kc _ T.A pp h.std.2.2⟩,
    deg := h.deg, ev := h.ev, tie := h.tie, own := h.own, layD := h.layD, fmt := h.fmt
    bFirst := h.bFirst, bSegs := h.bSegs, bTail := h.bTail, bLast := h.bLast }

theorem glAt_finalHyp : Spec.glAt_finalHyp := fun H X _ Fp _ _ _ _ _ _ a k msg r e mca h =>
  { wfIs := h.wfIs
    sndIs := h.sndIs
    reqIs := h.reqIs
    onIs := h.onIs
    wfJ :=
      { isStd := h.wfStd, ok := (glReqJohn_msgs Fp _ _ _ _ _ h.wfM).1, body := h.wfBody,
        bdDat := h.wfBd, plL := h.wfAtL, plB := h.wfAtB, noPad := h.wfNoPad, rest2 := h.wfRest2
        conf3 := gl3_conf X.Z.Zw.W.Cf a k msg r e mca h.code h.ha h.hk h.hp h.h3 h.smp h.model
        near := (glReqJohn_msgs Fp _ _ _ _ _ h.wfM).2 }
    sOff :=
      { places := h.plS, okW := (glReqJohn_msgs _ _ _ _ _ _ h.sW).1,
        okU := (glReqJohn_msgs _ _ _ _ _ _ h.sU).1, okO := (glReqJohn_msgs _ _ _ _ _ _ h.sO).1,
        fairW := h.fW, fairU := h.fU, fairO := h.fO
        nearW := (glReqJohn_msgs _ _ _ _ _ _ h.sW).2,
          nearU := (glReqJohn_msgs _ _ _ _ _ _ h.sU).2,
          nearO := (glReqJohn_msgs _ _ _ _ _ _ h.sO).2 }
    sLink := { ok := (glReqJohn_msgs _ _ _ _ _ _ h.sK).1, reads := h.rdK, fair := h.fK,
               near := (glReqJohn_msgs _ _ _ _ _ _ h.sK).2 }
    sOn :=
      { places := h.plB, okW := (glReqJohn_msgs _ _ _ _ _ _ h.sWB).1,
        okU := (glReqJohn_msgs _ _ _ _ _ _ h.sUB).1, okO := (glReqJohn_msgs _ _ _ _ _ _ h.sOB).1,
        fairW := h.fWB, fairU := h.fUB, fairO := h.fOB
        nearW := (glReqJohn_msgs _ _ _ _ _ _ h.sWB).2,
          nearU := (glReqJohn_msgs _ _ _ _ _ _ h.sUB).2,
          nearO := (glReqJohn_msgs _ _ _ _ _ _ h.sOB).2 }
    own₀ := h.own₀
    req := glAt_finalReq H X.Kc p X.R X.core X.first X.c X.Ls X.T X.qφ X.q X.κ h.req
    places := h.places
    pl₁ := h.pl₁
    pK := gl3_runAt _ _ _ h.tK
    p₁ := gl3_runAt _ _ _ h.t₁
    p₂ := gl3_runAt _ _ _ h.t₂
    p₃ := gl3_runAt _ _ _ h.t₃
    p₁B := glAt_runAt H _ _ _ _ h.t₁B
    p₂B := glAt_runAt H _ _ _ _ h.t₂B
    p₃B := glAt_runAt H _ _ _ _ h.t₃B }

end Cb.Gl
