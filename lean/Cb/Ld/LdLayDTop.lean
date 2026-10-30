-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLayDTop.lean: the records of the reference request and of the object around it, with the
three clauses on masks (`lay`, `layT`, `layB`) replaced by the record `LdReqRefLayD`
(Cb/Ld/LdLayD.lean).

In standard terms: two records of hypotheses on a request's sub-protocol and on the protocol object,
with three fields on honest provers replaced by the record `LdReqRefLayD` of Cb/Ld/LdLayD.lean; two
statements that lead from the new records to older ones (`LdReqRefDSA`, `Z.HypRef`), for a field E
of the given characteristic, and one, from `Z.HypRefU`, that the two languages agree.

Two records and three statements; the proofs, applications, are in Cb/Ld/LdLayDTopProofs.lean.

Main names:
  `LdReqRefDU`: Cb/Req1/LdReqStdAny.lean's record `LdReqRefDSA` (the reference request with one
    first sending, standard senders with the pads' field chosen sending by sending, the groups' own
    links), field for field, but: the fields `lay`, `layT`, `layB` are gone; in their place:
    `layD : LdReqRefLayD LdLayQ.ok ..` (Cb/Ld/LdLayD.lean; of each layout its own conditions are
    asked as they stand).
  `Spec.ldReqRefU`: `LdReqRefDU ..` → `LdReqRefDSA ..` (the characteristic of E is pp: the rules
    that carry a fact through a body take it).
  `Spec.ldObjRefU_hyp`: the characteristic of E is p; `Z.HypRefU ..` → `Z.HypRef ..` (conditions on
    the object, at the empty list of further first moves).
  `Spec.ldObjRefU_langs`: `Z.HypRefU ..` → the two languages agree (a field of the model's duty).

Why: it lets a hypothesis be stated
without a clause that unfolds to a property of an honest prover (one writer's reading, not a
theorem: Limits of Cb/Ld/LdLayD.lean).


Limits: packaging: all content is `Cb.ldReqRefLay_data` (and applications of `Cb.ldReqStdAny` and
of the lemmas under `Cb.ldObjRefT_hyp` and `Cb.ldObjRefT_langs`: Cb/Ld/LdLayDTopProofs.lean). Not
said here: all that the heads of Cb/Ld/LdLayD.lean, Cb/Req1/LdReqStdAny.lean and
Cb/Req1/LdReqRefStd.lean list.
`Z.HypRefU` does not give `Z.HypRefT` (that record has one pads' field for the whole request).
What still speaks of more than data in `LdReqRefDU` (not all is named here):
  the model's duty;
  in `std`, and in `layD` at `LdLayQ.ok`: `Sig.StdL.OK` (its fields `priv`, `hides`);
  in `std` also `Laws`, `Fair`, `ListLE`, `Evades` (`LdSendD.IsStd`, Cb/Req1/LdReqProtoStd.lean);
  at `ev`, and in `std`: `Evader.OK` (Cb/Gen/BatEvader.lean);
  in `std` also `LdFoldD.IsGrp` (Cb/Req1/LdReqProtoStd.lean: `Laws`, `ListAt`);
  in `fmt` and the numbers: each closing's link's format and list of errors;
  the entry and exit steps are free moves, and the conditions `LdPend.StepD` inside `LdReqRefLayD`
    are conditions on their honest maps: beside the model's duty (of which they are no field) the
    model owes them: its steps' honest maps neither read a pending mask nor drop it; in the form of
    this protocol's technical report (lean/CREDITS.md; neighbours' relations are equal; no steps)
    there is nothing to owe.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLayD
import Cb.Obj.LdObjectDataRefT

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

section
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The record of the reference request, the masks by the record `LdReqRefLayD`. -/
structure LdReqRefDU (pp : ℕ) (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
    (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
    (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
    (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) : Prop where
  duty   : LdModelDuty R L T
  std    : first.IsStdAny ∧ L.ProtoSA pp ∧ T.A.ProtoSA pp
  deg    : 2 ≤ R.n
  ev     : R.Z.OK
  tie    : R.Tie
  own    : R.X.Own
  layD   : LdReqRefLayD LdLayQ.ok pp R first b L T
  fmt    : ∃ (px' : first.Wp' → R.Cf.conf.PIdx)
        (φb : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx b.J),
      (∀ w, px' (first.D.rest w).2 = w.2.1) ∧
      L.FmtP (first.tgt.fmt (⟨id, id⟩ : IxAt R.Cf.conf.E0 R.Cf.conf.E0) Prod.snd px'
          ((LdStage.start E Kc (R.O.jReq core)).S.qSum first.N qφ first.t)) φb ∧
      T.FmtAt φb q
  bFirst : (ldSendFamErr first.N first.Sd first.L : ℝ≥0∞) ≤ κ * (Fintype.card first.Sd.D : ℝ≥0∞)
  bSegs  : L.Nums κ
  bTail  : T.A.Nums κ
  bLast  : Err.Below (R.X.bt.nums R.Cf.conf.E0 Kc).err κ

end

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- `Z.Hyp` at the reference request: `Z.HypRefT` (Cb/Obj/LdObjectDataRefT.lean), field for field,
with `req` at `LdReqRefDU`. -/
structure LdObjZ.HypRefU (Z : LdObjZ F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (p L : ℕ)
    {Kc : Type} (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
    (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
    (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
    (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E]
    (V : Z.Zw.StdW Fp) (p₀ : LdLinPl R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop) : Prop where
  /-- which terms stand in Z.R -/
  wfIs   : (⟨Z.R.W, Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Z.Zw.W, Z.Zw.G.B⟩
  sndIs  : Z.R.toLdObjD = Z.R.toLdObjD.std Z.Y
  reqIs  : Z.R.toLdObjD.pack =
    ldRefPack R core first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _) b Ls T qφ q
  onIs   : Z.R.onPack = ldRefOn R p₀
  /-- the hypotheses of `V.Hyp`, `Z.Y.Hyp` and `HypOwn₀` -/
  wfS    : V.Hyp p L
  sndOK  : Z.Y.Hyp
  own₀   : Z.R.toLdObjD.HypOwn₀
  /-- the request -/
  req    : LdReqRefDU p R core first b Ls T qφ q κ
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

def ldReqRefU : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ) [CharP E pp]
      (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞),
    LdReqRefDU pp R core first b L T qφ q κ → LdReqRefDSA pp R core first b L T qφ q κ

def ldObjRefU_hyp : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (Kc : Type) (p : ℕ) [CharP E p] (Z : LdObjZ F E)
      [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (L : ℕ) (R : LdORE F E Kc)
      (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (V : Z.Zw.StdW Fp)
      (p₀ : LdLinPl R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop),
    Z.HypRefU p L R core first b Ls T qφ q κ V p₀ plR →
    Z.HypRef p L R core first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _) b Ls T qφ q κ

def ldObjRefU_langs : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (Kc : Type) (p : ℕ) (Z : LdObjZ F E)
      [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (L : ℕ) (R : LdORE F E Kc)
      (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (V : Z.Zw.StdW Fp)
      (p₀ : LdLinPl R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop),
    Z.HypRefU p L R core first b Ls T qφ q κ V p₀ plR →
    ∀ i x w, Z.R.W.Cf.conf.Rno i x w → ∃ w', Z.R.W.Cf.conf.Ryes i x w'

end Spec
end Cb
