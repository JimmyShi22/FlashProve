-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectDataRefS.lean: book-keeping for the hypotheses of a holographic IOP: hypotheses on
the object's data at the reference request with standard senders and the groups' own links.

Its main statement, `Cb.Spec.ldObjRefS_hyp`, is an implication between two records of hypotheses.
A record, two statements and proofs: an assembly.
`Z : LdObjZ F E` (Cb/Obj/LdObjectData.lean) is the object's data. The reference request is the term
`ldReqRef` (Cb/Req1/LdReqRef.lean). `R : LdORE F E Kc` (Cb/Obj/LdObjectReqEnd.lean) is the data of a
request's end and of the test that follows.

Main names:
  `Z.HypRefS ..`, compared with `Z.HypRef` (Cb/Obj/LdObjectDataRef.lean):
    `req`: `LdReqRefDS` (Cb/Req1/LdReqRefStd.lean) in place of `LdReqRefD`: one first sending; every
      sender the standard one; every closing's link the group's own; the model's duty named
      (`LdModelDuty`: with "the two languages agree").
    `pl` is replaced by one more equation (which rows, targets and mask form stand in Z.R: those
      read off the reference request's end R) and `Z.R.HypPl₀ plB` (Cb/Obj/LdObjectDataRefPl.lean):
      the four clauses that tie the batch test's plan to the request's last claims are theorems,
      from `rowsIs` and `pl₀`.
  `Spec.ldObjRefS_hyp`: `Z.HypRefS ..` → `Z.HypRef ..` (at more := the empty list).
  `Spec.ldObjRefS_langs`: `Z.HypRefS ..` → the model's "the two languages agree", stated at R's
    configuration, holds at the object's
    (`∀ i x w, Z.R.W.Cf.conf.Rno i x w → ∃ w', Z.R.W.Cf.conf.Ryes i x w'`): the equation `reqIs`
    says that they are one.

Notation: `p`: a natural number (`Spec.ldObjZ_hyp`, Cb/Obj/LdObjectData.lean, asks `CharP E p`);
`L`: a natural number (`LdCf.OK L`, Cb/Obj/LdObjectConf.lean, says that it bounds the lists at the
radius of decoding); `first`: the first sending: the data (`LdSendD`, Cb/Req1/LdSegKit.lean); `Ls`:
a list of reference segments, up to the stage `b` (`LdRefL`, Cb/Req1/LdReqRef.lean); `T`: the last
segment: the data (`LdRefT`, the same file); `κ`: a number in `ℝ≥0∞` (the request's record `req`
asks, in `bFirst` to `bLast`, that its errors are below it, in the sense of `Err.Below`,
Iop/InteractiveOracleProof.lean); `plB`: a set of entries (`Z.R.on.ol.toC.Sa.Ent → Prop`).

Limits: four equations are among the hypotheses (`wfIs`, `sndIs`, `reqIs`, `rowsIs`): each says
which terms stand in Z.R; whoever builds Z.R from these terms has them by definition.
`req : LdReqRefDS ..` still speaks of more than data: the head of Cb/Req1/LdReqRefStd.lean lists
where.
Six clauses on the sender `Zw.D` of weights-formedness are not on data: it is a free value with laws
(Cb/Ld/LdWfEnd.lean: `Rest0`, `Rest1`).
No instance that meets the hypotheses of `ldObjRefS_hyp` or `ldObjRefS_langs` is part of this
library; as far as the library shows, these theorems may hold of nothing.
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectDataRef
import Cb.Obj.LdObjectDataRefPlProofs
import Cb.Req1.LdReqRefStd

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- `Z.Hyp` at the reference request, with standard senders in the request and the rows read off its
end (`plB`: a set of entries). -/
structure LdObjZ.HypRefS (Z : LdObjZ F E) (p L : ℕ) {Kc : Type} (R : LdORE F E Kc)
    (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
    (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
    (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
    (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (plB : Z.R.on.ol.toC.Sa.Ent → Prop) : Prop where
  /-- which terms are in `Z.R` -/
  wfIs   : (⟨Z.R.W, Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Z.Zw.W, Z.Zw.G.B⟩
  sndIs  : Z.R.toLdObjD = Z.R.toLdObjD.std Z.Y
  reqIs  : Z.R.toLdObjD.pack =
    ldRefPack R core first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _) b Ls T qφ q
  rowsIs : Z.R.rowsPack plB = ldRefRows R
  /-- conditions: weights-formedness, the standard senders, the object's own clauses that are not
  the request's -/
  wfOK   : Z.Zw.OK p L
  sndOK  : Z.Y.Hyp
  own₀   : Z.R.toLdObjD.HypOwn₀
  /-- the request -/
  req    : LdReqRefDS p R core first b Ls T qφ q κ
  pl₀    : Z.R.HypPl₀ plB
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
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldObjRefS_hyp : Prop :=
  ∀ (Kc : Type) (p : ℕ) (Z : LdObjZ F E) (L : ℕ) (R : LdORE F E Kc)
      (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (plB : Z.R.on.ol.toC.Sa.Ent → Prop),
    Z.HypRefS p L R core first b Ls T qφ q κ plB →
    Z.HypRef p L R core first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _) b Ls T qφ q κ

def ldObjRefS_langs : Prop :=
  ∀ (Kc : Type) (p : ℕ) (Z : LdObjZ F E) (L : ℕ) (R : LdORE F E Kc)
      (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (plB : Z.R.on.ol.toC.Sa.Ent → Prop),
    Z.HypRefS p L R core first b Ls T qφ q κ plB →
    ∀ i x w, Z.R.W.Cf.conf.Rno i x w → ∃ w', Z.R.W.Cf.conf.Ryes i x w'

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldObjRefS_hyp : Spec.ldObjRefS_hyp F E := fun Kc p Z _ R core first b Ls T qφ q κ plB h =>
  { wfIs := h.wfIs, sndIs := h.sndIs, reqIs := h.reqIs, wfOK := h.wfOK, sndOK := h.sndOK,
    own₀ := h.own₀, req := ldReqRefStd F E Kc p R core first b Ls T qφ q κ h.req,
    pl := ldObjRefPl_hyp F E Kc Z.R plB R h.rowsIs h.pl₀, pK := h.pK, p₁ := h.p₁, p₂ := h.p₂,
    p₃ := h.p₃, p₁B := h.p₁B, p₂B := h.p₂B, p₃B := h.p₃B }

/-- "the two languages agree", carried along an equation of configurations; used at `R`'s -/
theorem ldLangs_at {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (Cf Cf' : LdCf F E) (e : Cf = Cf')
    (h : ∀ i x w, Cf'.conf.Rno i x w → ∃ w', Cf'.conf.Ryes i x w') :
    ∀ i x w, Cf.conf.Rno i x w → ∃ w', Cf.conf.Ryes i x w' := e ▸ h

theorem ldObjRefS_langs : Spec.ldObjRefS_langs F E := fun _ _ Z _ R _ _ _ _ _ _ _ _ _ h =>
  ldLangs_at Z.R.W.Cf R.Cf (congrArg LdReqPack.Cf h.reqIs) h.req.duty.langs

end
end Cb
