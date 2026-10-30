-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectDataRefJAny.lean: book-keeping for the hypotheses of a holographic IOP: hypotheses on
the object's data at the reference request, with the request's pads' field chosen sending by
sending.

Its main statements, `Cb.Spec.ldObjRefA_hyp` and `Cb.Spec.ldObjRefA_ofT`, are implications between
records of hypotheses.
A record, three statements and proofs: an assembly; no top theorem of its own.
The object's data Z, the reference request and a request's end R: the head of
Cb/Obj/LdObjectDataRefT.lean.

Main names:
  `Z.HypRefA p L R core first b Ls T qφ q κ V p₀ plR`: `Z.HypRefT ..`
    (Cb/Obj/LdObjectDataRefT.lean), letter for letter, but for `req : LdReqRefDSA ..`
    (Cb/Req1/LdReqStdAny.lean) in the place of `LdReqRefDS ..`.
  `Spec.ldObjRefA_hyp`: `Z.HypRefA ..` → `Z.HypRef ..` (at more := the empty list).
  `Spec.ldObjRefA_langs`: `Z.HypRefA ..` → "the two languages agree" at the object's configuration
    (`∀ i x w, Z.R.W.Cf.conf.Rno i x w → ∃ w', Z.R.W.Cf.conf.Ryes i x w'`): from the model's duty
    inside `req`.
  `Spec.ldObjRefA_ofT`: `Z.HypRefT ..` → `Z.HypRefA ..`: the record is the wider one.

Why: the head of Cb/Req1/LdReqStdAny.lean.

Notation: `p`: a natural number (`Spec.ldObjZ_hyp`, Cb/Obj/LdObjectData.lean, asks `CharP E p`);
`L`: a natural number (`LdCf.OK L`, Cb/Obj/LdObjectConf.lean, says that it bounds the lists at the
radius of decoding); `first`: the first sending: the data (`LdSendD`, Cb/Req1/LdSegKit.lean); `Ls`:
a list of reference segments, up to the stage `b` (`LdRefL`, Cb/Req1/LdReqRef.lean); `T`: the last
segment: the data (`LdRefT`, the same file); `κ`: a number in `ℝ≥0∞` (the request's record `req`
asks, in `bFirst` to `bLast`, that its errors are below it, in the sense of `Err.Below`,
Iop/InteractiveOracleProof.lean); `V`: the standard sender of weights-formedness: the data beside `Z.Zw`
(`LdWfE.StdW`, Cb/Obj/LdObjectDataSnd.lean); `Fp`: a finite field, with `Algebra Fp E`; `p₀`: the
plan without a splitting: the data (`LdLinPl`, Cb/Ld/LdLinClosePlan.lean); `plR`: for each row that
stays open (`R.Bn`: `LdORE`, Cb/Obj/LdObjectReqEnd.lean), a set of entries.

Limits: all that the head of Cb/Obj/LdObjectDataRefT.lean says on equations and on what still speaks
of more than data holds here.
No instance that meets the hypotheses of `ldObjRefA_hyp` or `ldObjRefA_langs` is part of this
library; as far as the library shows, these theorems may hold of nothing. No instance with two
different pads' fields. Within one sending the pads' field is one.
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectDataRefT
import Cb.Req1.LdReqStdAny

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- `Z.Hyp` at the reference request (`Z.HypRefT`), the request's pads' field chosen sending by
sending. -/
structure LdObjZ.HypRefA (Z : LdObjZ F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (p L : ℕ)
    {Kc : Type} (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
    (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
    (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
    (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E]
    (V : Z.Zw.StdW Fp) (p₀ : LdLinPl R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop) : Prop where
  /-- which terms are in `Z.R` -/
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
  req    : LdReqRefDSA p R core first b Ls T qφ q κ
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

def ldObjRefA_hyp : Prop :=
  ∀ (Kc : Type) (p : ℕ) (Z : LdObjZ F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (L : ℕ)
      (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (V : Z.Zw.StdW Fp)
      (p₀ : LdLinPl R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop),
    Z.HypRefA p L R core first b Ls T qφ q κ V p₀ plR →
    Z.HypRef p L R core first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _) b Ls T qφ q κ

def ldObjRefA_langs : Prop :=
  ∀ (Kc : Type) (p : ℕ) (Z : LdObjZ F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (L : ℕ)
      (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (V : Z.Zw.StdW Fp)
      (p₀ : LdLinPl R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop),
    Z.HypRefA p L R core first b Ls T qφ q κ V p₀ plR →
    ∀ i x w, Z.R.W.Cf.conf.Rno i x w → ∃ w', Z.R.W.Cf.conf.Ryes i x w'

/-- the record is the wider one -/
def ldObjRefA_ofT : Prop :=
  ∀ (Kc : Type) (p : ℕ) (Z : LdObjZ F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (L : ℕ)
      (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (V : Z.Zw.StdW Fp)
      (p₀ : LdLinPl R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop),
    Z.HypRefT p L R core first b Ls T qφ q κ V p₀ plR →
    Z.HypRefA p L R core first b Ls T qφ q κ V p₀ plR

end
end Spec

section
variable (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
  [Fintype Fp] [Algebra Fp E]

theorem ldObjRefA_hyp :
    Spec.ldObjRefA_hyp F E Fp := fun Kc p Z _ L R core first b Ls T qφ q κ V p₀ plR h =>
  { wfIs := h.wfIs, sndIs := h.sndIs, reqIs := h.reqIs, wfOK := ldWfE_okStd F E Fp Z.Zw V p L h.wfS,
    sndOK := h.sndOK, own₀ := h.own₀, req := ldReqStdAny F E Kc p R core first b Ls T qφ q κ h.req,
    pl := ldRefPlan_hyp F E Kc Z.R R p₀ plR h.onIs h.places h.pl₁, pK := h.pK, p₁ := h.p₁,
    p₂ := h.p₂, p₃ := h.p₃, p₁B := h.p₁B, p₂B := h.p₂B, p₃B := h.p₃B }

theorem ldObjRefA_langs : Spec.ldObjRefA_langs F E Fp := fun _ _ Z _ _ R _ _ _ _ _ _ _ _ _ _ _ h =>
  ldLangs_at Z.R.W.Cf R.Cf (congrArg LdReqPack.Cf h.reqIs) h.req.duty.langs

theorem ldObjRefA_ofT :
    Spec.ldObjRefA_ofT F E Fp := fun Kc p _ _ _ R core first b Ls T qφ q κ _ _ _ h =>
  { wfIs := h.wfIs, sndIs := h.sndIs, reqIs := h.reqIs, onIs := h.onIs, wfS := h.wfS,
    sndOK := h.sndOK, own₀ := h.own₀,
    req := ldReqStdAny_ofDS F E Kc p R core first b Ls T qφ q κ h.req, places := h.places,
    pl₁ := h.pl₁, pK := h.pK, p₁ := h.p₁, p₂ := h.p₂, p₃ := h.p₃, p₁B := h.p₁B,
    p₂B := h.p₂B, p₃B := h.p₃B }

end
end Cb
