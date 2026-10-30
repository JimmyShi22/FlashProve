-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectDataRefT.lean: book-keeping for the hypotheses of a holographic IOP: a record of
hypotheses about the object's data (`Z.HypRefT`). It asks, beside other clauses, that the request is
the reference request, that the sender of weights-formedness is a standard sender, and that the plan
of the linear test on a batch is tied to the request's end by conditions on places.

A record, statements and proofs: an assembly; no top theorem of its own.
`Z : LdObjZ F E` (Cb/Obj/LdObjectData.lean) is the object's data. The reference request is the term
`ldReqRef` (Cb/Req1/LdReqRef.lean). `R : LdORE F E Kc` (Cb/Obj/LdObjectReqEnd.lean) is the data of
a request's end and of the test that follows.

Main names:
  `Z.HypRefT ..`, compared with the record `Z.HypRefS` (Cb/Obj/LdObjectDataRefS.lean):
    That record's `wfOK` (the conditions of weights-formedness) is replaced by `V` and
      `wfS : V.Hyp p L` (Cb/Obj/LdObjectDataSnd.lean: `ldWfE_okStd`; its head tells the fields of
      `V.Hyp`). One of them is the equation "(Zw.D, Zw.X) is (the standard sender, its record of
      mask places)".
      (The statements also take, as an instance, that each block's masks are finitely many.)
    That record's `rowsIs` and `pl₀` are replaced by `onIs`, an equation that says which plan and
      rows stand in `Z.R`; `places`; and `pl₁`, which is `Z.R.HypPl` (Cb/Obj/LdObjectPlanRows.lean)
      without six of its clauses: these six are theorems, from `onIs` and `places`
      (Cb/Obj/LdObjectRefPlan.lean: `ldRefPlan_hyp`); for the online phase `pl₁` asks only choices
      of the plan and numbers.
    The other fields are as there.
  `Spec.ldObjRefT_hyp`: `Z.HypRefT ..` → `Z.HypRef ..` (at more := the empty list).
  `Spec.ldObjRefT_langs`: `Z.HypRefT ..` → "the two languages agree" at the object's configuration
    (`∀ i x w, Z.R.W.Cf.conf.Rno i x w → ∃ w', Z.R.W.Cf.conf.Ryes i x w'`): from the model's duty
    inside `req`.

Limits: five equations are among the hypotheses (`wfIs`, `sndIs`, `reqIs`, `onIs`; `isStd` inside
`wfS`), beside the two of each test (`isT`, `isQ`) and `q₀is`, `restIs` inside `pl₁`: each says
which terms stand in the record; whoever builds it from these terms has them by definition. `reqIs`
and `onIs` both fix "on": they overlap there.
`req : LdReqRefDS ..` still speaks of more than data: the head of Cb/Req1/LdReqRefStd.lean lists
where.
So does "off" in `R.PlacesOK`: it is a condition on `R.sl`, a free field of the request's end.
That `Z.HypRefT` can be met is not shown in this file. No instance that meets the hypotheses of
`ldObjRefT_hyp` or `ldObjRefT_langs` is part of this library; as far as the library shows, these
theorems may hold of nothing.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectDataRefS
import Cb.Obj.LdObjectRefPlanProofs
import Cb.Obj.LdObjectDataSnd

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- `Z.Hyp` at the reference request; `V` is the standard sender's data, `p₀` the plan, `plR` the
places. -/
structure LdObjZ.HypRefT (Z : LdObjZ F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (p L : ℕ)
    {Kc : Type} (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
    (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
    (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
    (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E]
    (V : Z.Zw.StdW Fp) (p₀ : LdLinPl R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop) : Prop where
  /-- which terms stand in `Z.R` -/
  wfIs   : (⟨Z.R.W, Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Z.Zw.W, Z.Zw.G.B⟩
  sndIs  : Z.R.toLdObjD = Z.R.toLdObjD.std Z.Y
  reqIs  : Z.R.toLdObjD.pack =
    ldRefPack R core first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _) b Ls T qφ q
  onIs   : Z.R.onPack = ldRefOn R p₀
  /-- conditions: weights-formedness, the standard senders, the object's own clauses that are not
  the request's -/
  wfS    : V.Hyp p L
  sndOK  : Z.Y.Hyp
  own₀   : Z.R.toLdObjD.HypOwn₀
  /-- the request -/
  req    : LdReqRefDS p R core first b Ls T qφ q κ
  places : R.PlacesOK p₀ plR
  pl₁    : Z.R.HypPl₁
  /-- the seven tests -/
  pK     : Z.R.Kc.run.Pre Z.twK
  p₁     : Z.R.TP₀.D₁.Pre Z.tw₁
  p₂     : Z.R.TP₀.D₂.Pre Z.tw₂
  p₃     : Z.R.X.run.Pre Z.tw₃
  p₁B    : Z.R.TB₀.D₁.Pre Z.tw₁B
  p₂B    : Z.R.TB₀.D₂.Pre Z.tw₂B
  p₃B    : Z.R.XB.run.Pre Z.tw₃B

end

namespace Spec
section
variable (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
  [Fintype Fp] [Algebra Fp E]

def ldObjRefT_hyp : Prop :=
  ∀ (Kc : Type) (p : ℕ) (Z : LdObjZ F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (L : ℕ)
      (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (V : Z.Zw.StdW Fp)
      (p₀ : LdLinPl R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop),
    Z.HypRefT p L R core first b Ls T qφ q κ V p₀ plR →
    Z.HypRef p L R core first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _) b Ls T qφ q κ

def ldObjRefT_langs : Prop :=
  ∀ (Kc : Type) (p : ℕ) (Z : LdObjZ F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (L : ℕ)
      (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (V : Z.Zw.StdW Fp)
      (p₀ : LdLinPl R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop),
    Z.HypRefT p L R core first b Ls T qφ q κ V p₀ plR →
    ∀ i x w, Z.R.W.Cf.conf.Rno i x w → ∃ w', Z.R.W.Cf.conf.Ryes i x w'

end
end Spec

section
variable (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
  [Fintype Fp] [Algebra Fp E]

theorem ldObjRefT_hyp :
    Spec.ldObjRefT_hyp F E Fp := fun Kc p Z _ L R core first b Ls T qφ q κ V p₀ plR h =>
  { wfIs := h.wfIs, sndIs := h.sndIs, reqIs := h.reqIs, wfOK := ldWfE_okStd F E Fp Z.Zw V p L h.wfS,
    sndOK := h.sndOK, own₀ := h.own₀, req := ldReqRefStd F E Kc p R core first b Ls T qφ q κ h.req,
    pl := ldRefPlan_hyp F E Kc Z.R R p₀ plR h.onIs h.places h.pl₁, pK := h.pK, p₁ := h.p₁,
    p₂ := h.p₂, p₃ := h.p₃, p₁B := h.p₁B, p₂B := h.p₂B, p₃B := h.p₃B }

theorem ldObjRefT_langs : Spec.ldObjRefT_langs F E Fp := fun _ _ Z _ _ R _ _ _ _ _ _ _ _ _ _ _ h =>
  ldLangs_at Z.R.W.Cf R.Cf (congrArg LdReqPack.Cf h.reqIs) h.req.duty.langs

end
end Cb
