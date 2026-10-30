-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaPpLeast.lean: a guard for Cb/Ld/LdKappaPp.lean, for every object at the technical
report's plan at once. Under `Z.HypRefPP` (for the request's record: `Z.HypRefPJ` at any κ'), the
records "at
most κ, counting work" hold, for all four numbers of bits, at every κ above all round errors, as
probabilities, of the five lists without work.

Statements (`Cb.Spec.ldKappaPp_back`, `Cb.Spec.ldKappaPp_least`) and proofs: the way back of
Cb/Ld/LdKappaConvObj.lean, Cb/Ld/LdKappaConv.lean through the two closings at this plan, then "work
only helps" (Cb/Ld/LdKappaWMono.lean). The analogue of Cb/Ld/LdKappaLeast.lean with
Cb/Ld/LdKappaWMono.lean. Nothing assumed beyond the hypotheses of the statements and whatever the
arguments hold as proofs.
"Work" is proof of work. A round's error e is a count of values of its verifier message: how many
may let a prover that has lost escape (`Err`, Iop/Rbr.lean); as a probability it is at most κ if e ≤
κ · v, and it is at most κ counting b bits of work if e ≤ κ · (2^b · v), with v the number of all
values of that message (`Err.Below`, Iop/InteractiveOracleProof.lean; `Err.BelowB`, Cb/Ld/LdKappaBits.lean). These
errors are numbers that the object lists (`obj.nums`, Cb/Obj/LdObject.lean: a `SubsR.Nums`,
Hiop/RecBuild.lean, whose five entries each have the data field `err`): that a sub-protocol is sound
at the numbers that are listed for it is no statement of this file (the premise `Z.HypRefPP` asks it
of the links of the request's sub-protocol moves and of the link that each of its fold moves holds
(`LdFoldD.Hyp.good`, Cb/Req1/LdSegKit.lean): `core.req.rHyp : P.r.Hyp`); for the object that tie is
`Spec.ldObj_hyp` (Cb/Obj/LdObject.lean), under `Obj.OK L`, in the sense of `SubsR.HypK`
(Hiop/RecBuild.lean) (that condition itself asks soundness of the parts one level down: the tie
carries soundness, it does not found it).

Main names:
  `Spec.ldKappaPp_back`: generic in the request: `Z.HypRefPP`, every round's error of the five
    lists, as a probability, at most κ (no work) ⇒ for all ws: `Z.KapW ws κ`; and `P.r.Below κ` (the
    request's preamble, move by move).
  `Spec.ldKappaPp_least`: the request `ldReqRef` (Cb/Req1/LdReqRef.lean): `Z.HypRefPJ` at any κ',
    every round's error, as a probability, at most κ ⇒ for all ws: `Z.KapW ws κ` ∧ `LdReqKapW` at
    ws.ins, κ.

Why: each clause of `Z.KapW` speaks of rounds that do occur in the five lists. So the record can be
met wherever the object's hypothesis (`Z.HypRefPJ`) can, at κ := the first count without work
(`Nums.maxAll` at no work, Cond/ObjQuote.lean). This file does not say that that count is below
⊤. The record excludes no object.

Notation: `Z.HypRefPP` (Cb/Obj/LdObjectPpDataP.lean): the object's hypothesis, the request a
parameter; `Z.HypRefPJ` (Cb/Obj/LdObjectPpData.lean): the object's hypothesis at the reference
request; `ws`: bits of work, by the class of the round that draws locations (`LdWk4`,
Cb/Ld/LdKappaW.lean: off, lk, sh, ins); `Z.KapW ws κ`: the record of Cb/Ld/LdKappaPp.lean.

Limits: it is not tight: at a κ above all errors without work no work is needed. That the records
hold at the largest error with work (the way back with work) is not proved here. This file goes
back only without work: a swap of two classes of rounds (`LdWk4`, Cb/Ld/LdKappaW.lean, has one of
the four numbers of bits for each class) would pass it. This file does not show the size of κ.

Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Cb.Ld.LdKappaPpProofs
import Cb.Ld.LdKappaConvObj
import Cb.Ld.LdKappaWMono
import Cb.Ld.LdKappaLeastProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain IOR.ChainA
open scoped ENNReal

namespace Spec

def ldKappaPp_back : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (Kc : Type) (p : ℕ) (Z : LdObjZp F E)
      [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (P : LdReqPack F E) (Rq : LdORE F E Kc)
      (V : Z.Zw.StdW Fp) (p₀ : LdLinPp Rq.O.d.ol.toC) (plR : Rq.Bn → Rq.S.Ent → Prop) (κ : ℝ≥0∞),
    Z.HypRefPP p P Rq V p₀ plR → Z.R.toPp.toT.obj.nums.Below κ →
    (∀ ws : LdWk4, Z.KapW ws κ) ∧ P.r.Below κ

def ldKappaPp_least : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (Kc : Type) (p : ℕ) (Z : LdObjZp F E)
      [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (Rq : LdORE F E Kc)
      (core : Rq.Cf.conf.PIdx × Rq.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (Rq.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc Rq.ix first.tgt b) (T : LdRefT Rq b)
      (qφ : Finset (LdStage.start E Kc (Rq.O.jReq core)).J.E.Pos → Prop)
      (q : Finset Rq.z.J.E.Pos → Prop) (κ' κ : ℝ≥0∞) (V : Z.Zw.StdW Fp)
      (p₀ : LdLinPp Rq.O.d.ol.toC) (plR : Rq.Bn → Rq.S.Ent → Prop),
    Z.HypRefPJ p Rq core first b Ls T qφ q κ' V p₀ plR → Z.R.toPp.toT.obj.nums.Below κ →
    ∀ ws : LdWk4, Z.KapW ws κ ∧ LdReqKapW ws.ins κ Rq first (.nil first.tgt) Ls T

end Spec

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The way back through the two closings at the report's plan: from
`P.toT.obj.nums.Below κ` to the records of the parts. -/
theorem ldKappaPpConv_objP (P : LdObjPp F E) (κ : ℝ≥0∞) (h : P.toT.obj.nums.Below κ) :
    P.Bw.Kap κ ∧ P.W.O.toC.P.KapC P.D.Sn P.εf κ ∧ P.TP.D₁.Kap κ ∧ P.TP.D₂.Kap κ ∧
    P.TP.D₃.Kap κ ∧ P.TP.Q'.c.ErrBelow κ ∧ P.K.P.KapC P.D.Sl P.ε₀ P.ε₁ κ ∧ P.Kc.run.Kap κ ∧
    P.r.Below κ ∧ P.on.ol.toC.P.KapCB P.D.SnB P.εfB P.N κ ∧ P.TB.D₁.Kap κ ∧ P.TB.D₂.Kap κ ∧
    P.TB.D₃.Kap κ ∧ P.cA'.ErrBelowA κ := by
  obtain ⟨hW, hL, hQ, hK, hKc, hR, hB, hZ⟩ := ldKappaConv_objT P.toT κ h
  have q0 : P.TP.Q.c.ErrBelow κ :=
    ((errBelow_append Unit _ _ _ (LdTc.frontC P.TP.front) P.TP.Q.c κ).1 hQ).2
  obtain ⟨q1, q'⟩ := ldKappaConv_cons P.TP.D₁ _ _ _ κ q0
  obtain ⟨q2, q''⟩ := ldKappaConv_cons P.TP.D₂ _ _ _ κ q'
  obtain ⟨q3, q4⟩ := ldKappaConv_cons P.TP.D₃ _ _ _ κ q''
  have e := (ldLinV_cZ_same E _ _ _ _ P.on.ol.toC P.N (P.TB.QA P.cA' P.same')
    (P.on.ol.toC.fqP P.TB.fa) (P.on.ol.toC.P.V6 P.D.SnB P.qaB P.N) (P.TB.tieF P.tie' P.x₀ P.y₀)
    (P.TB.qB₀ P.N P.q₀B P.bB')
    (P.TB.QV P.N P.q₀B P.bB' P.tie' P.x₀ P.y₀ P.cA' P.same' P.xB P.xC P.QV')).1
  have z1 := ldKappaConv_linZA
    P.on.ol.toC (P.TB.QA P.cA' P.same') (P.on.ol.toC.fqP P.TB.fa) κ (errBelowA_to_eq e κ hZ)
  have z2 : (P.TB.QAt P.cA' P.same').cA.ErrBelowA κ :=
    ((errBelowA_append (P.TB.front.cA true) (P.TB.QAt P.cA' P.same').cA κ).1 z1).2
  obtain ⟨b1, b'⟩ := ldKappaConv_consSh P.TB.D₁ _ _ _ κ z2
  obtain ⟨b2, b''⟩ := ldKappaConv_consSh P.TB.D₂ _ _ _ κ b'
  obtain ⟨b3, b4⟩ := ldKappaConv_consLo P.TB.D₃ ⟨P.TB.Q', P.cA', P.same'⟩ _ _ κ b''
  exact ⟨hW, hL, q1, q2, q3, q4, hK, hKc, hR, hB, b1, b2, b3, b4⟩

theorem ldKappaPpConv_objR (R : LdObjRp F E) (κ : ℝ≥0∞) (h : R.toPp.toT.obj.nums.Below κ) :
    R.Bw.Kap κ ∧ R.W.O.toC.P.KapC (R.toLdObjD.std R.Y).Sn R.εf κ ∧ R.TP₀.D₁.Kap κ ∧ R.TP₀.D₂.Kap κ ∧
    R.TP₀.D₃.Kap κ ∧ R.X.run.Kap κ ∧ R.K.P.KapC (R.toLdObjD.std R.Y).Sl R.ε₀ R.ε₁ κ ∧
    R.Kc.run.Kap κ ∧ R.r.Below κ ∧ R.on.ol.toC.P.KapCB (R.toLdObjD.std R.Y).SnB R.εfB R.N κ ∧
    R.TB₀.D₁.Kap κ ∧ R.TB₀.D₂.Kap κ ∧ R.TB₀.D₃.Kap κ ∧ R.XB.run.Kap κ := by
  obtain ⟨hW, hL, h1, h2, h3, h4, hK, hKc, hR, hB, b1, b2, b3, b4⟩ := ldKappaPpConv_objP R.toPp κ h
  exact ⟨hW, hL, h1, h2, h3, (ldKappaConv_cons R.X.run _ _ _ κ h4).1, hK, hKc, hR, hB, b1, b2, b3,
    (ldKappaConv_consLo R.XB.run _ _ _ κ b4).1⟩

/-- One whole test: from its list back to the record with its tower, with any work.
(not all hypotheses are named here: see the statement below) -/
theorem ldKappaPp_test {S : Sig E} (D : LdRunD S) (T : D.Tow) (w : ℕ) (κ : ℝ≥0∞)
    (e : D.T = T.toEnd) (h : D.Kap κ) : D.KapTW T w κ :=
  ldKappaW_of_test D T w κ ⟨(ldKappaConv_pre D T κ e h).1, (ldKappaConv_pre D T κ e h).2⟩

theorem ldKappaPp_backOf (Z : LdObjZp F E) (κ : ℝ≥0∞)
    (pK : Z.R.Kc.run.Pre3 Z.twK Z.dK) (p₁ : Z.R.TP₀.D₁.Pre3 Z.tw₁ Z.d₁)
    (p₂ : Z.R.TP₀.D₂.Pre3 Z.tw₂ Z.d₂) (p₃ : Z.R.TP₀.D₃.Pre3 Z.tw₃ Z.d₃)
    (p₄ : Z.R.X.run.Pre3 Z.tw₄ Z.d₄) (p₁B : Z.R.TB₀.D₁.PreJ Z.tw₁B Z.d₁B)
    (p₂B : Z.R.TB₀.D₂.PreJ Z.tw₂B Z.d₂B) (p₃B : Z.R.TB₀.D₃.PreJ Z.tw₃B Z.d₃B)
    (p₄B : Z.R.XB.run.PreJ Z.tw₄B Z.d₄B) (h : Z.R.toPp.toT.obj.nums.Below κ) :
    (∀ ws : LdWk4, Z.KapW ws κ) ∧ Z.R.r.Below κ := by
  obtain ⟨hW, hL, h1, h2, h3, h4, hK, hKc, hR, hB, b1, b2, b3, b4⟩ := ldKappaPpConv_objR Z.R κ h
  refine ⟨fun ws => ?_, hR⟩
  exact
    { wf := hW, lin := ldKappaW_of_linC _ _ _ _ κ hL
      t₁ := ldKappaPp_test _ (Z.R.TP₀.D₁.up3 Z.tw₁) _ κ p₁.isT h1,
        t₂ := ldKappaPp_test _ (Z.R.TP₀.D₂.up3 Z.tw₂) _ κ p₂.isT h2
      t₃ := ldKappaPp_test _ (Z.R.TP₀.D₃.up3 Z.tw₃) _ κ p₃.isT h3,
        t₄ := ldKappaPp_test _ (Z.R.X.run.up3 Z.tw₄) _ κ p₄.isT h4
      link := ldKappaW_of_linkC _ _ _ _ _ κ hK,
        tK := ldKappaPp_test _ (Z.R.Kc.run.up3 Z.twK) _ κ pK.isT hKc
      linB := ldKappaW_of_linCB _ _ _ _ _ κ hB
      t₁B := ldKappaPp_test _ (Z.R.TB₀.D₁.upJ Z.tw₁B) _ κ p₁B.isT b1,
        t₂B := ldKappaPp_test _ (Z.R.TB₀.D₂.upJ Z.tw₂B) _ κ p₂B.isT b2
      t₃B := ldKappaPp_test _ (Z.R.TB₀.D₃.upJ Z.tw₃B) _ κ p₃B.isT b3,
        t₄B := ldKappaPp_test _ (Z.R.XB.run.upJ Z.tw₄B) _ κ p₄B.isT b4 }

end

theorem ldKappaPp_back :
    Spec.ldKappaPp_back := fun _ _ _ _ _ _ _ _ _ _ _ _ _ Z _ P _ _ _ _ κ h hB =>
  have g := ldKappaPp_backOf Z κ h.pK h.p₁ h.p₂ h.p₃ h.p₄ h.p₁B h.p₂B h.p₃B h.p₄B hB
  ⟨g.1, ldKappa_packTo Z.R.toLdObjD.pack P h.core.reqIs κ g.2⟩

theorem ldKappaPp_least :
    Spec.ldKappaPp_least := fun _ _ _ _ _ _ _ _ _ _ _ _ _ Z _ Rq _ first b Ls T _ _ _ κ _ _ _ h hB ws =>
  have g := ldKappaPp_backOf Z κ h.pK h.p₁ h.p₂ h.p₃ h.p₄ h.p₁B h.p₂B h.p₃B h.p₄B hB
  have r := ldKappaConv_req Rq _ first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _) b Ls T κ
    (ldKappa_packTo Z.R.toLdObjD.pack _ h.core.reqIs κ g.2)
  ⟨g.1 ws, ldKappaW_of_req ws.ins κ Rq first (.nil first.tgt)
      Ls T r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2⟩

end Cb
