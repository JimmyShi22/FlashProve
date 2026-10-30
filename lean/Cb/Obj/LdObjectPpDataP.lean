-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPpDataP.lean: assembly of the holographic IOP from its sub-protocols: this file
defines `Z.HypRefPP`, a record on the object on data (`LdObjZp`) at the plan of this protocol's
technical report (lean/CREDITS.md) for the linear test, generic in the request.

A definition, statements and proofs. The object on data is the record `LdObjZp`, with nine towers
and their distances. The record `Z.HypRefPP` is `Z.HypRefPJ` (Cb/Obj/LdObjectPpData.lean, which says
what the object on data and its towers are) with the request a parameter and, in the place of the
request's record `LdReqRefDJ`, the clause req : `P.Good`. Generic. No assumed theorem beyond the
hypotheses of its statements.

Main names:
  `Z.HypRefPP p P Rq V p₀ plR`: its field core is `D.CoreP` .. P V at D := `Z.R.toLdObjD`
    (Cb/Obj/LdObjectPpCoreP.lean), where reqIs asks `D.pack = P` and req asks `P.Good`
    (`LdReqPack.Good`, Cb/Obj/LdObjectDataRef.lean: `rHyp : P.r.Hyp`, `rZk : P.r.ZkS`, `rFmt`,
    `rEnd`: properties of a term). The fields on the plan are as in `Z.HypRefPJ`: onIs and places,
    at the data `Rq : LdORE` of a request's end (any: the request says which), and
    pl₁. The fields pK, p₁ .. p₄ are `Pre3`; p₁B .. p₄B are `PreJ`, in whose towers `MCAat` /
    `MCArows` are premises on agreement.


  `Spec.ldObjZpP_hyp`: E of characteristic p (`CharP E p`), `Z.HypRefPP` .. ⇒ `Z.R.Hyp 1`
    (`LdObjRp.Hyp`: all hypotheses, Cb/Obj/LdObjectPpRows.lean).
  `Spec.ldObjZpP_ctb`: `Z.HypRefPP` .., countability on data (`Z.FinZp`,
    Cb/Obj/LdObjectPpData.lean) ⇒ `Z.R.toPp.CtbPp` (`LdObjPp.CtbPp`: what is left to show at an
    object, Cb/Obj/LdObjectCtbPaper.lean).
  `Spec.ldObjZpP_ofJ`: E of characteristic p, `Z.HypRefPJ` .. ⇒ `Z.HypRefPP` .. at the
    reference request's pack (`ldRefPack` ..): `Z.HypRefPJ` is an instance of this record.

Notation: the `1` in `Z.R.Hyp 1`: the argument `L` of `LdObjRp.Hyp`: a natural number (`LdCf.OK L`,
Cb/Obj/LdObjectConf.lean, says that it bounds the lists at the radius of decoding); `P`: what the
object's data hold of a request (`LdReqPack`, Cb/Obj/LdObjectDataRef.lean); `V`: the standard sender
of weights-formedness: the data beside `Z.Zw` (`LdWfE.StdW`, Cb/Obj/LdObjectDataSnd.lean); `Fp`: a
finite field, with `Algebra Fp E`; `p₀`: the plan: the data (`LdLinPp`, Cb/Ld/LdLinClosePlanP.lean);
`plR`: for each row that stays open (`Rq.Bn`: `LdORE`, Cb/Obj/LdObjectReqEnd.lean), a set of
entries.

Limits: nothing ties P to Rq in this record but through the object: `D.pack = P` fixes `D.on`, and
onIs fixes the plan over `D.on` to be the one at Rq's end.
No theorem of this library states that the hypotheses of `ldObjZpP_hyp` can be met together.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectPpCoreP
import Cb.Obj.LdObjectPpData

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

/-- The record, the request a parameter. -/
structure LdObjZp.HypRefPP {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (Z : LdObjZp F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (p : ℕ) (P : LdReqPack F E)
    {Kc : Type} (Rq : LdORE F E Kc) {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E]
    (V : Z.Zw.StdW Fp) (p₀ : LdLinPp Rq.O.d.ol.toC) (plR : Rq.Bn → Rq.S.Ent → Prop) : Prop where
  core   : Z.R.toLdObjD.CoreP Z.Zw Z.R.Y Z.δ p P V
  onIs   : Z.R.onPack = ldRefOnP Rq p₀
  places : Rq.PlacesOKP p₀ plR
  pl₁    : Z.R.HypPl₁
  /-- the link's test and the offline test's four: within a third -/
  pK     : Z.R.Kc.run.Pre3 Z.twK Z.dK
  p₁     : Z.R.TP₀.D₁.Pre3 Z.tw₁ Z.d₁
  p₂     : Z.R.TP₀.D₂.Pre3 Z.tw₂ Z.d₂
  p₃     : Z.R.TP₀.D₃.Pre3 Z.tw₃ Z.d₃
  p₄     : Z.R.X.run.Pre3 Z.tw₄ Z.d₄
  /-- the batch test's four: below the Johnson radius -/
  p₁B    : Z.R.TB₀.D₁.PreJ Z.tw₁B Z.d₁B
  p₂B    : Z.R.TB₀.D₂.PreJ Z.tw₂B Z.d₂B
  p₃B    : Z.R.TB₀.D₃.PreJ Z.tw₃B Z.d₃B
  p₄B    : Z.R.XB.run.PreJ Z.tw₄B Z.d₄B

namespace Spec
section
variable (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
  [Fintype Fp] [Algebra Fp E]

def ldObjZpP_hyp : Prop :=
  ∀ (Kc : Type) (p : ℕ) [CharP E p] (Z : LdObjZp F E)
      [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (P : LdReqPack F E) (Rq : LdORE F E Kc)
      (V : Z.Zw.StdW Fp) (p₀ : LdLinPp Rq.O.d.ol.toC) (plR : Rq.Bn → Rq.S.Ent → Prop),
    Z.HypRefPP p P Rq V p₀ plR → Z.R.Hyp 1

def ldObjZpP_ctb : Prop :=
  ∀ (Kc : Type) (p : ℕ) (Z : LdObjZp F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)]
      (P : LdReqPack F E) (Rq : LdORE F E Kc) (V : Z.Zw.StdW Fp)
      (p₀ : LdLinPp Rq.O.d.ol.toC) (plR : Rq.Bn → Rq.S.Ent → Prop),
    Z.HypRefPP p P Rq V p₀ plR → Z.FinZp → Z.R.toPp.CtbPp

def ldObjZpP_ofJ : Prop :=
  ∀ (Kc : Type) (p : ℕ) [CharP E p] (Z : LdObjZp F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)]
      (Rq : LdORE F E Kc) (core : Rq.Cf.conf.PIdx × Rq.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (Rq.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc Rq.ix first.tgt b) (T : LdRefT Rq b)
      (qφ : Finset (LdStage.start E Kc (Rq.O.jReq core)).J.E.Pos → Prop)
      (q : Finset Rq.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (V : Z.Zw.StdW Fp)
      (p₀ : LdLinPp Rq.O.d.ol.toC) (plR : Rq.Bn → Rq.S.Ent → Prop),
    Z.HypRefPJ p Rq core first b Ls T qφ q κ V p₀ plR →
    Z.HypRefPP p
      (ldRefPack Rq core first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _) b Ls T qφ q)
      Rq V p₀ plR

end
end Spec

section
variable (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
  [Fintype Fp] [Algebra Fp E]

theorem ldObjZpP_hyp : Spec.ldObjZpP_hyp F E Fp := by
  intro Kc p _ Z _ P Rq V p₀ plR h
  obtain ⟨c1, c2⟩ := ldObjPpCoreP F E Fp p Z.R.toLdObjD Z.Zw Z.R.Y Z.δ P V h.core
  exact
    { rest0 := h.core.sndIs ▸ c1
      sndOK := c2
      pl := ldRefPlanP_hyp F E Kc Z.R Rq p₀ plR h.onIs h.places h.pl₁
      close := h.pK.ok
      test₁ := h.p₁.ok, test₂ := h.p₂.ok, test₃ := h.p₃.ok, test₄ := h.p₄.ok
      test₁B := (ldTowGJ_run E _ _ Z.tw₁B Z.d₁B h.p₁B).2,
        test₂B := (ldTowGJ_run E _ _ Z.tw₂B Z.d₂B h.p₂B).2
      test₃B := (ldTowGJ_run E _ _ Z.tw₃B Z.d₃B h.p₃B).2,
        test₄B := (ldTowGJ_run E _ _ Z.tw₄B Z.d₄B h.p₄B).2 }

theorem ldObjZpP_ctb : Spec.ldObjZpP_ctb F E Fp := fun _ _ Z _ _ _ _ _ _ h c =>
  { inst := c.inst
    wf := ldObjZ_ctbWf Z.Zw c.sP ⟨Z.R.W, Z.R.Bw⟩ h.core.wfIs
    nW := c.nW, nU := c.nU, nO := c.nO
    t₁ := h.p₁.pre.ctb c.t₁, t₂ := h.p₂.pre.ctb c.t₂, t₃ := h.p₃.pre.ctb c.t₃
    rest := ctb_cons Z.R.X.run _ Z.R.X.d Z.R.X.d' (h.p₄.pre.ctb c.t₄) (ctb_nil _ _ _ _)
    nK := c.nK
    tK := h.pK.pre.ctb c.tK
    req := ctb_req Z.R.r c.req
    nWB := c.nWB, nUB := c.nUB, nOB := c.nOB
    t₁B := (ldTowGJ_run E _ _ Z.tw₁B Z.d₁B h.p₁B).1.ctb c.t₁B,
      t₂B := (ldTowGJ_run E _ _ Z.tw₂B Z.d₂B h.p₂B).1.ctb c.t₂B,
      t₃B := (ldTowGJ_run E _ _ Z.tw₃B Z.d₃B h.p₃B).1.ctb c.t₃B
    restB := ctbA_consLo Z.R.XB.run _ Z.R.XB.d Z.R.XB.d'
      ((ldTowGJ_run E _ _ Z.tw₄B Z.d₄B h.p₄B).1.ctb c.t₄B) (ctbA_tcNil _ _ _ _) }

theorem ldObjZpP_ofJ :
    Spec.ldObjZpP_ofJ F E Fp := fun Kc p _ Z _ Rq core first b Ls T qφ q κ V _ _ h =>
  { core := ldObjPpCoreP_ofJ F E Fp Kc p Z.R.toLdObjD Z.Zw Z.R.Y Z.δ Rq core
      first b Ls T qφ q κ V h.core
    onIs := h.onIs, places := h.places, pl₁ := h.pl₁, pK := h.pK, p₁ := h.p₁, p₂ := h.p₂,
      p₃ := h.p₃, p₄ := h.p₄, p₁B := h.p₁B, p₂B := h.p₂B, p₃B := h.p₃B, p₄B := h.p₄B }

end
end Cb
