-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`AgreeJ` is proved nowhere in this library: it follows from the statement on codes
`Cb.BCHKS46At Gl.F Gl.E` (`Cb.Gl.glAg_ofAt`, this file). The predicate `IsGlJ` in its premise does
not ask a radius within half the distance (Cb/Gl/GlLdJ.lean). So `AgreeJ` is not confined to radii
within half the distance: it speaks of every e below the Johnson radius as read with mult i ≤ e for
every i.

Cb/Gl/GlFinalAg.lean: mutual correlated agreement of families of interleaved Reed-Solomon codes over
p = 2^64 - 2^32 + 1 (words over E), at a radius below the Johnson radius, stated as one proposition
(`Cb.Gl.AgreeJ`), and what follows from that proposition for a fold, a whole proximity test and a
request's part of the protocol.

A definition (no other), statements (in `Cb.Gl.Spec`) and proofs. But for `Spec.glAg_ofAt`, the
statements are the analogues of statements of Cb/Gl/GlLdJAt.lean, Cb/Gl/GlFinalAt.lean and of
`Spec.glEv_hyp` (Cb/Gl/GlFinalEv.lean), with `AgreeJ` in the place of BCHKS46At F E, each under the
hypotheses of its statement.

Why: by reading, the statement on codes (`Cb.BCHKS46At`, Cb/Gen/CodeListRSAt.lean) enters the chain
of statements at one line (Cb/Gl/GlLdJAt.lean). What that line yields is `AgreeJ`.

Main names:
  `AgreeJ`: every family of plain Reed-Solomon codes on subgroups of orders at most 2^32 whose
    message and randomness fill the dimension, each with interleaved rows, read evenly at the long
    positions P (`IsGlJ C d t e bad`:
    Cb/Gl/GlLdJ.lean), has, below the Johnson radius as read (and mult i ≤ e, 0 < k i: clauses of
    `IsGlJ`), agreement whatever the number of rows with its count: `C.MCArows e bad`
    (`LdCode.MCArows`, Cb/Ld/LdRelRows.lean).
    In Lean: `IsGlJ C d t e bad` → InJohnson |P| d e → `C.MCArows e bad`, for all C, d, t, e, bad.
    `C.MCArows e bad` says that for every finite R the interleaved code `C.il R` has mutual
    correlated agreement on lines at the radius e, with at most bad exceptional values θ
    (`LdCode.MCAat`, Cb/Ld/LdRel.lean).
  `Spec.glAg_evHyp`: `AgreeJ` → FinalEv X .. → X.Z.HypRefJU LayGlEv p ..

Notation: `C`: a code read under a transformation (`LdCode E P`, Cb/Ld/LdRel.lean); `P`: its long
positions, |P| their number; `d`, `t`, `e`, `bad`: numbers; `IsGlJ C d t e bad` (Cb/Gl/GlLdJ.lean)
asks d ≤ mult i · (2^(a i) - k i), t ≤ r i, mult i ≤ e for every i; e stands as the radius in
`InJohnson |P| d e` (Cb/Gen/JohnsonList.lean) and `C.MCArows e bad` (Cb/Ld/LdRelRows.lean), bad as
the count there.

Limits: `AgreeJ` is the joint: many statements here and above have it as a premise. Whoever proves
it from a named statement of the literature has every statement that has it as a premise:
`Spec.glAg_ofAt` (from BCHKS46At F E).
(The source of the statement on codes: the head of Cb/Gen/CodeListRS.lean.)
What is not said. Whether AgreeJ holds. What the heads of Cb/Gl/GlLdJAt.lean, Cb/Gl/GlFinalAt.lean
and Cb/Gl/GlFinalEv.lean list as not said is not said here either.

Terms: lean/GLOSSARY.md.

-/
import Cb.Gl.GlFinalEvProofs

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR IOR.Chain Cb.Ood
open scoped ENNReal

/-- The one premise on agreement that the chain of statements uses: agreement of Reed-Solomon codes
below the Johnson radius (`InJohnson`; `IsGlJ`, Cb/Gl/GlLdJ.lean, does not ask a radius within half
the distance), with the count `bad`. Proved nowhere in this library: it follows from the statement
on codes `Cb.BCHKS46At Gl.F Gl.E` (`Cb.Gl.glAg_ofAt`, this file). -/
def AgreeJ : Prop :=
  ∀ (P : Type) [Fintype P] (C : LdCode E P) (d t e bad : ℕ),
    IsGlJ C d t e bad → InJohnson (Fintype.card P) d e → C.MCArows e bad

namespace Spec

def glAg_ofAt : Prop := Cb.BCHKS46At F E → AgreeJ

/-- Agreement: from the premise `AgreeJ`. -/
def glAg_mca : Prop :=
  AgreeJ →
  ∀ (P : Type) [Fintype P] (C : LdCode E P) (d t e bad : ℕ),
    GlJ C d t e bad → InJohnson (Fintype.card P) d e → C.MCArows e bad ∧ C.MCAat e bad

def glAg_fold : Prop :=
  AgreeJ →
  ∀ (P : Type) [Fintype P] (Y : SumPar E P) (d e t bC bZ bW : ℕ), GlJ Y.C d 0 e bC →
    GlJ Y.Z d 0 e bZ → GlJ Y.Zw d t e bW → InJohnson (Fintype.card P) d e →
    Function.Injective Y.val → 2 ≤ Y.n → Y.PackOK → Y.QwDeg → Y.John d e t bC bZ bW

def glAg_tower : Prop := AgreeJ → ∀ (a : LdJoint E) (T : LdTowJ a), TowGlJ T → T.John

def glAg_towerG : Prop :=
  AgreeJ →
  ∀ (B : Type) [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P] (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (T : LdTowGJ G Sb sl Z),
    TowGGlJ T → T.John

def glAg_runAt : Prop :=
  AgreeJ → ∀ (S : Sig E) (D : LdRunD S) (Tw : D.TowJ) (d : ℕ), RunGlJAt D Tw d → D.PreJ Tw d

def glAg_groupPar : Prop :=
  AgreeJ →
  ∀ (S : Sig E) (G : Grp S) (Sh : GShape G) (d t bC bZ bW : ℕ), GlJ Sh.Cb d 0 G.e bC →
    GlJ Sh.Zb d 0 G.e bZ → GlJ Sh.par.Zw d t G.e bW →
    InJohnson (Fintype.card G.P) d G.e → Function.Injective Sh.val → 2 ≤ Sh.n →
    Sh.par.PackOK → Sh.par.QwDeg → Sh.par.John d G.e t bC bZ bW


def glAg_reqFold : Prop :=
  AgreeJ → ∀ (Kc : Type) (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid), IsGrpGl D l → D.IsGrpJ l

def glAg_reqSeg : Prop :=
  AgreeJ →
  ∀ (Kc : Type) (I : LdRefIx E) (a : LdStage E Kc) (S : LdRefS E Kc I a) (pp : ℕ),
    ProtoGlS S pp → S.ProtoJ pp

def glAg_reqList : Prop :=
  AgreeJ →
  ∀ (Kc : Type) (I : LdRefIx E) (a b : LdStage E Kc) (L : LdRefL E Kc I a b) (pp : ℕ),
    ProtoGlL pp L → L.ProtoJ pp


/-- The generic record, from forms, from the premise `AgreeJ`. -/
def glAg_evHyp : Prop :=
  AgreeJ →
  ∀ (X : LdFinJ F E) [∀ b, Fintype (X.Z.Zw.K.wfI X.Z.Zw.Rl b → E)] (Fp : Type) [Field Fp]
      [Fintype Fp] [Algebra Fp E] (V : X.Z.Zw.StdW Fp) (p₀ : LdLinPl X.R.O.d.ol.toC)
      (plR : X.R.Bn → X.R.S.Ent → Prop) (a k msg r e mca : ℕ),
    FinalEv X V p₀ plR a k msg r e mca →
    X.Z.HypRefJU LayGlEv p X.R X.core X.first X.c X.Ls X.T X.qφ X.q X.κ V p₀ plR


end Spec

theorem glAg_ofAt : Spec.glAg_ofAt := fun H P _ C d t e bad h hJ => glAt_rows0 H P C d t e bad h hJ

/-- a subcode: one more term, under the premise `AgreeJ`, which this library proves nowhere -/
theorem glAg_rowsS (H : AgreeJ) (P : Type) [Fintype P] (C : LdCode E P) (d t e bad : ℕ)
    (h : IsGlS C d t e bad) (hJ : InJohnson (Fintype.card P) d e) : C.MCArows e bad := by
  obtain ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, rfl, ha, hk0, hk,
      hp, hE, hd, ht, hm, hb⟩ := h
  have hW : IsGlJ ((⟨P, pos, mult⟩ : Reading (grp a k msg fun i => k i + 1 - msg i)).ld E R) d 0 e
      (∑ i, ⌊Cb.bchksBound (2 ^ a i) (k i) (e / mult i)⌋₊) :=
    ⟨A, iA, dA, a, k, msg, fun i => k i + 1 - msg i, pos, mult, R, fR, dR, rfl, ha, hk0, hk, fun i => by
      have := hp i
      show msg i + (k i + 1 - msg i) = k i + 1
      omega, hE, hd, fun _ => Nat.zero_le _, hm, le_rfl⟩
  have gW := glC_code P _ d 0 (.base
    ⟨A, iA, dA, a, k, msg, fun i => k i + 1 - msg i, pos, mult, R, fR, dR, rfl, ha, hk, fun i => by
      have := hp i
      show msg i + (k i + 1 - msg i) ≤ k i + 1
      omega, hE, hd, fun _ => Nat.zero_le _⟩)
  have gS := glC_code P _ d t
    (.base ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, rfl, ha, hk, hp, hE, hd, ht⟩)
  have hsub : ((⟨P, pos, mult⟩ : Reading (grp a k msg fun i => k i + 1 - msg i)).ld E R).SubOf
      ((⟨P, pos, mult⟩ : Reading (grp a k msg r)).ld E R) fun α => α :=
    ld_sub_ld F E A (grp a k msg r) (fun i => k i + 1 - msg i) P pos mult R fun i => by
      have := hp i
      show r i ≤ k i + 1 - msg i
      omega
  exact ld_rows_mono E P _ _ _ _ hb
    (ld_sub_rows E P _ _ _ d e _ _ hsub gW.1 gS.1 gW.2.2.2.1 (john_lt hJ)
      (H P _ d 0 e _ hW hJ) fun R' _ _ =>
        ld_list_johnson E P _ d e (ld_laws_il E P _ Bool (ld_laws_il E P _ R' gW.1))
          (ld_dist_il E P _ Bool d (ld_dist_il E P _ R' d gW.2.2.2.1)) hJ)

theorem glAg_rows (H : AgreeJ) (P : Type) [Fintype P] (C : LdCode E P) (d t e bad : ℕ)
    (h : GlJ C d t e bad) (hJ : InJohnson (Fintype.card P) d e) : C.MCArows e bad := by
  induction h with
  | base h => exact H P _ _ _ _ _ h hJ
  | sub h => exact glAg_rowsS H P _ _ _ _ _ h hJ
  | copy h => exact glCp_rows_of (fun P _ C d t e bad h hJ => H P C d t e bad h hJ) P _ _ _ _ _ h hJ
  | il R _ ih => exact ld_rows_il E P _ R _ _ (ih hJ)
  | pair _ _ ih₁ ih₂ => exact ld_rows_pair E P _ _ _ _ _ (ih₁ hJ) (ih₂ hJ)
  | fam _ ih => exact ld_rows_fam E P _ _ _ _ fun a => ih a hJ
  | up _ hb ih => exact ld_rows_mono E P _ _ _ _ hb (ih hJ)

theorem glAg_mca : Spec.glAg_mca := fun H P _ C d t e bad h hJ =>
  ⟨glAg_rows H P C d t e bad h hJ, ld_rows_self E P C e bad (glAg_rows H P C d t e bad h hJ)⟩

theorem glAg_fold : Spec.glAg_fold := fun H P _ Y d e t bC bZ bW hC hZ hW hJ hi hn hp hq =>
  have gC := glC_code P _ d 0 (glJ_glC P _ d 0 e bC hC)
  have gZ := glC_code P _ d 0 (glJ_glC P _ d 0 e bZ hZ)
  have gW := glC_code P _ d t (glJ_glC P _ d t e bW hW)
  { lawsC := gC.1, lawsZ := gZ.1, lawsW := gW.1, distC := gC.2.2.2.1, distZ := gZ.2.2.2.1,
    distW := gW.2.2.2.1, john := hJ
    mcaC := glAg_rows H P _ d 0 e bC hC hJ,
      mcaZ := glAg_rows H P _ d 0 e bZ hZ hJ,
      mcaW := glAg_rows H P _ d t e bW hW hJ
    inj := hi, deg := hn, pack := hp, qw := hq,
      zk := (glC_code P Y.Cw d t (.il _ (glJ_glC P _ d t e bW hW))).2.2.2.2 }

theorem glAg_tower : Spec.glAg_tower := by
  intro H a T
  induction T with
  | base a t cov d b =>
    rintro ⟨h, hJ⟩
    have g := glC_code a.P a.C d 0 (glJ_glC a.P a.C d 0 a.e b h)
    exact ⟨g.1, g.2.2.2.1, hJ, (glAg_mca H a.P a.C d 0 a.e b h hJ).2, g.2.1⟩
  | step Y sl e S d bC bZ bW e' d' rest ih =>
    rintro ⟨⟨hC, hZ, hW, hJ, hi, hn, hp, hq⟩, ⟨hN, hJ', hZo, hZb, hP⟩, hr⟩
    refine ⟨glAg_fold H _ (Y.reform sl) d e S.ts bC bZ bW hC hZ hW hJ hi hn hp hq,
      glJ_switch _ _ _ (S.D e) d' e' rest.toC.q hN ?_ hJ' hZo hZb hP,
      ih hr⟩
    exact glC_mono _ _ d 0 0 0
      (.pair (glJ_glC _ _ d 0 e bC hC)
        (.pair (glJ_glC _ _ d 0 e bZ hZ)
          (glC_mono _ _ d S.ts d 0 (glJ_glC _ _ d S.ts e bW hW) le_rfl (Nat.zero_le _))))
      (Nat.zero_le _) le_rfl

theorem glAg_towerG : Spec.glAg_towerG := by
  intro H B _ S G _ Sb sl Z T h
  cases T with
  | plain T => exact glAg_tower H _ T h
  | shaped Sh Sw d bC bZ bW e' d' rest =>
    obtain ⟨⟨hv, hm1, hm2, hz, h1⟩, ⟨hB, hZ, hW, hJ, hi, hn, hp, hq⟩,
        ⟨hN, hJ', hZo, hZb, hP⟩, hr⟩ := h
    have hC : GlJ Sh.par.C d 0 G.e bC := .il _ hB
    have hI : GlC (Sw.D G.e).Cin 0 0 :=
      glC_mono _ _ d 0 0 0
        (.pair (glJ_glC _ _ d 0 G.e bC hC)
          (.pair (glJ_glC _ _ d 0 G.e bZ hZ)
            (glC_mono _ _ d Sw.ts d 0 (glJ_glC _ _ d Sw.ts G.e bW hW) le_rfl (Nat.zero_le _))))
        (Nat.zero_le _) le_rfl
    exact ⟨⟨hv,
      (glC_code _ _ d 0 (glJ_glC _ _ d 0 G.e bC hB)).1,
      (glC_code _ _ d 0 (glJ_glC _ _ d 0 G.e bZ hZ)).1,
      fun r => by
        split
        · next b hb => exact hm1 r b hb
        · next j hj => exact hm2 r j hj, hz, h1⟩, glAg_fold H _ Sh.par d G.e Sw.ts bC bZ bW hC hZ hW hJ hi hn hp hq, glJ_switch _ _ _ (Sw.D G.e) d' e' rest.toC.q hN hI hJ' hZo hZb hP, glAg_tower H _ rest hr⟩

theorem glAg_runAt : Spec.glAg_runAt := by
  rintro H S D Tw d ⟨h1, h2, h3, hG, hJ, hF, hZ, hT⟩
  exact ⟨h1, h2, h3, fun a => (glC_code D.G.P _ d 0 (hG a)).1,
    fun a => (glC_code D.G.P _ d 0 (hG a)).2.2.2.1, hJ, hZ, hF,
    glAg_towerG H _ S D.G D.Sb D.sl D.Z Tw hT⟩

theorem glAg_groupPar : Spec.glAg_groupPar := fun H _ G Sh d t bC bZ bW hC hZ hW hJ hi hn hp hq =>
  glAg_fold H G.P Sh.par d G.e t bC bZ bW (.il _ hC) hZ hW hJ hi hn hp hq


theorem glAg_reqFold : Spec.glAg_reqFold := by
  rintro H Kc D l
    ⟨iB, iP, Sh, Hd, Z, hc, dw, d, t, bC, bZ, bW, e, ⟨hv, hm1, hm2, hz, h1⟩, hH, ⟨hC, hZb, hW, hJ⟩,
      ⟨hi, hn, hp, hq⟩, hZ, hF⟩
  have hS : Sh.OK :=
    ⟨hv, (glC_code _ _ d 0 (glJ_glC _ _ d 0 D.G.e bC hC)).1, (glC_code _ _ d 0 (glJ_glC _ _ d 0 D.G.e bZ hZb)).1, fun r => by
      split
      · next b hb => exact hm1 r b hb
      · next j hj => exact hm2 r j hj, hz, h1⟩
  exact ⟨iB, iP, Sh, Hd, Z, hc, dw, d, t, bC, bZ, bW, e, hS, hH,
    glAg_groupPar H _ _ Sh d t bC bZ bW hC hZb hW hJ hi hn hp hq, hZ, hF⟩

theorem glAg_reqSeg : Spec.glAg_reqSeg := fun H Kc I _ _ pp h =>
  ⟨glReqJohn_body Kc I _ pp h.body, h.ev, h.named,
    glAg_reqFold H Kc _ _ h.fold, glReqJohn_send Kc _ _ h.snd⟩

theorem glAg_reqList : Spec.glAg_reqList := by
  intro H Kc I a b L pp
  induction L with
  | nil => intro _; rw [LdRefL.ProtoJ]; trivial
  | snoc L S ih =>
      intro h
      rw [ProtoGlL] at h
      rw [LdRefL.ProtoJ]
      exact ⟨ih h.1, glAg_reqSeg H Kc I _ S pp h.2⟩


theorem glAg_evHyp : Spec.glAg_evHyp := fun H X _ Fp _ _ _ _ _ _ a k msg r e mca h =>
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
          glAg_reqList H X.Kc _ _ _ X.Ls p (glEv_list X.Kc _ _ _ X.Ls p h.req.std.2.1),
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
    p₁B := glAg_runAt H _ _ _ _ (glEv_runJ _ _ _ _ h.t₁B)
    p₂B := glAg_runAt H _ _ _ _ (glEv_runJ _ _ _ _ h.t₂B)
    p₃B := glAg_runAt H _ _ _ _ (glEv_runJ _ _ _ _ h.t₃B) }


end Cb.Gl
