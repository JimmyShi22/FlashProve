-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqRefFinal.lean: the reference request meets the object's list: from the model's side,
the protocol's side, where the masks come from, readers and demands, and numbers (`LdReqRefD`; pp
the characteristic of E).

Two records, a definition, two statements (`Cb.Spec.ldReqRefFinal_nums`, `Cb.Spec.ldReqRefFinal`)
and their proofs.
The object's list is `PreListR` (its docstring: the parameter list of a preamble: all items but
knowledge soundness) with `PreKnowR` (round-by-round knowledge soundness of a preamble):
Hiop/RecSubs.lean. The reference request is the term `ldReqRef R first a₁ more hm b L T`, with its
list L of segments S and its last segment T (Cb/Req1/LdReqRef.lean).
Each reference segment's own zero-knowledge clause (`L.segs.ZkJ base`), format (`L.Fmt φ ψ`) and
error bound (`L.Below κ`) are theorems, each under the hypotheses of its statement
(`Spec.ldReqRefLayJ_segs`, `Spec.ldReqRefFmtL_segs`, `Spec.ldReqRefFinal_nums`). In the record
`LdReqRefD` they are put in (its fields `lay`, `fmt`, `bSegs` have their premises `L.LayJ`,
`L.FmtP`, `L.Nums κ`): no clause speaks of a block's link, honest prover, simulator or extractor,
but for these: the other lot's link bridge-to-fold of each closing (its hypotheses, format and
errors: Cb/Ld/LdGroup*.lean show them from codes); the sendings (first, the two of each body, the
one of each closing): their seven hypotheses speak of the sender (Cb/Obj/LdObjectSenders.lean shows
them for the standard sender), "does not look" and "Fresh" in lay too; the moves of "more" (further
sendings and steps behind the first: `Hyp`, format, errors are asked of the list as it is); the
entry and exit steps, as moves (the model's side); in lay, layT, layB: what is fresh after the moves
of "more" (`base₀`), after an entry step, after a segment (`S.Carries`), after the last segment's
moves (a property of moves); in fmt: the format of each link bridge-to-fold; in fmt: what the first
sender and each closing's sender hand on (`rest`); in bSegs, bTail, bLast: the lists of errors of
the front's moves, of the digits' lookup and of the batchings of tensor rows (`A.Nums κ`: front, lk,
batt; `bLast`); in fmt: what the locations' link of each closing needs (`S.Qc.loc.link.R.need`).

Main names:
  `S.NumsAt κ`, `L.Nums κ`: the numbers of a reference segment, of the list: the body's
    (Cb/Req1/LdSegRefBelow.lean: `A.Nums κ`); the batching's evader; the link's list of errors; the
    one sending's number; the locations'. `Spec.ldReqRefFinal_nums`: `L.Nums κ → L.Below κ`
    (`L.Below`: Cb/Req1/LdReqRefZk.lean).
  `LdReqRefD ..`: the record:
    `model`: `LdReqModel L T` (Cb/Req1/LdReqModel.lean): M1 .. M6: the steps between segments and
      between blocks; `Link`, `Back`; degrees; multiplicities; what else is claimed is carried.
    `proto`: `LdReqProto ..` (the same file): codes, samples, evaders, senders, places, numbers; the
      final batching's degree, evader, `R.Tie`.
    `own`: the places of the final batching's own masks.
    `lay`, `layT`, `layB` (Cb/Req1/LdReqRefLay.lean, Cb/Req1/LdReqRefLayJ.lean): where the masks
      come from, in the closed sets (`L.LayJ`, `L.LaidJ`: at each stage between segments the set of
      facts laid is closed under join at one reading, a coarser reading, another type for the same
      masks: so own masks of one block may come from several sendings, as this protocol's technical
      report (lean/CREDITS.md) has it for a later segment's sumcheck that ends at a map of the
      index; `L.Laid` gives `L.LaidJ`
      (`Spec.ldReqRefLayJ_of`)): for each segment, what zero knowledge asks of its body, beside its
      hypotheses, at facts that are handed on from facts laid before it; the same for the last
      segment; the wide fact of the final batching's own masks.
    `fmt` (Cb/Req1/LdReqRefFmtL.lean): the first sender hands the prover encoded index on; readers
      of the record and of the prover encoded index; demands on positions, backwards; the model's
      maps between segments keep record and prover encoded index (M7).
    `bFirst`, `bMore`, `bSegs`, `bTail`, `bLast`: every round's error is at most κ times the number
      of verifier messages: block by block.
  `Spec.ldReqRefFinal`: for pp the characteristic of E (`[CharP E pp]`): `LdReqRefD ..` gives:
    `PreListR R.O.left ..` ∧ `PreKnowR R.O.left ..` ∧ every round's error of the request as one
    reduction, as a probability, is at most κ.

Limits: this file does not say that the fields of the record hold together at one value. Seams that
no toy in this library crosses: the front's lookup's rows through the last step of the front at a
closing; what rides must give the tensor rows (`Rest`); the pending row's places lie in kept
messages (`Ends`); the exit step, past which nothing rides; the ghost together with "the core is
handed on" from the request's first stage; the wide fact of the final batching's masks behind the
last segment. The smallest guard that crosses all: one segment with a closing and the last one, a
tensor row in each: one pending row crosses a closing and meets a second one in the final batching.
This file does not say that the record can be met: toys of the parts stand (a segment; the front
joined to the body; the end: Cb/Req1/LdSegToy.lean, Cb/GlVal/GlJ3SegFrontToySeam.lean,
Cb/Obj/LdObjectReqEndToy.lean). No theorem of this library states that the hypotheses of
`ldReqRefFinal` can be met together. Segments with two groups are not in the list L. No model is
given.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqModel
import Cb.Req1.LdReqRefLayJ
import Cb.Obj.LdObjectReqEndAtS
import Cb.Req1.LdReqRefFmtL
import Cb.Req1.LdSegRefAllSeg

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

/-- the numbers of a reference segment -/
structure LdRefS.NumsAt {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {a : LdStage E Kc}
    (S : LdRefS E Kc I a) (κ : ℝ≥0∞) : Prop where
  body : S.A.Nums κ
  bat  : (S.K.Z.err : ℝ≥0∞) ≤ κ * (Fintype.card S.K.Z.D : ℝ≥0∞)
  fold : Err.Below S.l.P.err κ
  snd  : (ldSendFamErr S.Qc.N S.Qc.Sd S.Qc.L : ℝ≥0∞) ≤ κ * (Fintype.card S.Qc.Sd.D : ℝ≥0∞)
  loc  : (((Fintype.card S.K.Pf - S.K.e - 1) ^ S.Qc.t : ℕ) : ℝ≥0∞) ≤
    κ * (Fintype.card (Fin S.Qc.t → S.K.Pf) : ℝ≥0∞)

def LdRefL.Nums {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {a : LdStage E Kc} (κ : ℝ≥0∞) :
    {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => L.Nums κ ∧ S.NumsAt κ

section
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The record. -/
structure LdReqRefD (pp : ℕ) (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (a₁ : LdStage E Kc)
    (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
    (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b)
    (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
    (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) : Prop where
  model  : LdReqModel L T
  proto  : LdReqProto pp R first more L T
  own    : R.X.Own
  lay    : L.LayJ pp (ldReqRef R first a₁ more hm b L T).base₀
  layT   : T.A.ZkAt pp (fun f =>
    ∃ g,
      L.LaidJ (ldReqRef R first a₁ more hm b L T).base₀ g ∧
      ∀ Y : MaskFact b.J.W → Prop, Y g → T.entry.After Y f)
  layB   : ∃ (Rd : R.S.Ent → Prop) (Rr : R.S.O → Prop),
    (∀ n, R.Rd n → Rd n) ∧
    ∃ g,
      L.LaidJ (ldReqRef R first a₁ more hm b L T).base₀ g ∧
      ∀ Y : MaskFact b.J.W → Prop, Y g →
        T.tail.After Y
          (R.X.src.wideFact Rd Rr (R.X.atOwn R.X.wAt) R.X.mask.Mk fun M => R.X.atVal R.X.wAt M)
  fmt    : ∃ (px' : first.Wp' → R.Cf.conf.PIdx)
        (φ₁ : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx a₁.J)
        (φb : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx b.J),
      (∀ w, px' (first.D.rest w).2 = w.2.1) ∧
      more.Fmt (first.tgt.fmt (⟨id, id⟩ : IxAt R.Cf.conf.E0 R.Cf.conf.E0) Prod.snd px'
          ((LdStage.start E Kc (R.O.jReq core)).S.qSum first.N qφ first.t)) φ₁ ∧
      L.FmtP φ₁ φb ∧ T.FmtAt φb q
  bFirst : (ldSendFamErr first.N first.Sd first.L : ℝ≥0∞) ≤ κ * (Fintype.card first.Sd.D : ℝ≥0∞)
  bMore  : more.Below κ
  bSegs  : L.Nums κ
  bTail  : T.A.Nums κ
  bLast  : Err.Below (R.X.bt.nums R.Cf.conf.E0 Kc).err κ

end

namespace Spec

def ldReqRefFinal_nums : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (a b : LdStage E Kc)
      (L : LdRefL E Kc I a b) (κ : ℝ≥0∞),
    L.Nums κ → L.Below κ

/-- Under the hypotheses below, the reference request meets the object's list. -/
def ldReqRefFinal : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ) [CharP E pp]
      (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (a₁ : LdStage E Kc)
      (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (w₀ : R.Cf.conf.PIdx × R.Cf.conf.Cells)
      (z0 : R.Cf.conf.PIdx × R.G) (r0 : R.S.Rnd),
    LdReqRefD pp R core first a₁ more hm b L T qφ q κ →
    (PreListR R.O.left
        (R.O.termAt (B := R.bEnd) (ldReqRef R first a₁ more hm b L T) Prod.fst w₀).req
        (R.O.termAt (B := R.bEnd) (ldReqRef R first a₁ more hm b L T) Prod.fst w₀).hReq
        Prod.snd Prod.fst R.Cf.conf.Rreq
        (R.O.termAt (B := R.bEnd) (ldReqRef R first a₁ more hm b L T) Prod.fst w₀).nums ∧
      PreKnowR R.O.left
        (R.O.termAt (B := R.bEnd) (ldReqRef R first a₁ more hm b L T) Prod.fst w₀).req
        (fun a => (R.Cf.conf.D a.2 a.1.2).isSome) R.Cf.conf.RreqR
        ((R.O.termAt (B := R.bEnd) (ldReqRef R first a₁ more hm b L T) Prod.fst w₀).cellsOf z0 r0)
        (R.O.termAt (B := R.bEnd) (ldReqRef R first a₁ more hm b L T) Prod.fst w₀).nums.err) ∧
    Err.Below ((ldReqRef R first a₁ more hm b L T).FP w₀).err κ

end Spec

theorem ldReqRefFinal_nums : Spec.ldReqRefFinal_nums := by
  intro E Kc _ _ I a b L κ
  induction L with
  | nil => intro _; rw [LdRefL.Below]; trivial
  | snoc L S ih =>
      intro h
      rw [LdRefL.Nums] at h
      rw [LdRefL.Below]
      exact ⟨ih h.1,
        ldSegRefAll_one_below E Kc _ S.A S.K S.l S.Qc κ h.2.body h.2.bat h.2.fold h.2.snd h.2.loc⟩

theorem ldReqRefFinal : Spec.ldReqRefFinal := by
  intro F E Kc _ _ _ _ _ pp _ R core first a₁ more hm b L T qφ q κ w₀ z0 r0 h
  have hL : L.OK pp := (ldReqModel_list E Kc _ _ _ L pp).2 ⟨h.model.segs, h.proto.segs⟩
  have hT : T.OK pp := (ldReqModel_tail F E Kc R b T pp).2 ⟨h.model.tail, h.proto.tail⟩
  obtain ⟨Rd, Rr, hRd, hB⟩ := h.layB
  obtain ⟨px', φ₁, φb, f1, f2, f3, f4⟩ := h.fmt
  refine ⟨ldOREAtS_object F E Kc R core (ldReqRef R first a₁ more hm b L T) w₀ qφ q z0 r0
      (ldReqModel_hyp F E Kc pp R _ first a₁ more hm b L T h.model h.proto)
      (ldReqRefLayJ F E Kc pp R _ first a₁ more hm b L T Rd Rr hL hT h.proto.deg h.proto.ev
        h.proto.tie h.own hRd h.lay h.layT hB)
      (ldReqRefFmtL_req F E Kc pp R _ first a₁ more hm b L T q _ _ φ₁ φb
        (ldFmt_send E Kc _ _ _ (LdStage.start E Kc (R.O.jReq core)) first ⟨id, id⟩
          Prod.snd Prod.fst px' qφ h.proto.hFirst f1)
        f2 hL f3 hT f4),
    ?_⟩
  exact (ldReq_below E Kc).2 _ _ _ _ _ (ldReqRef R first a₁ more hm b L T) w₀ κ
    (ldReqRefK_reqBelow F E Kc R _ first a₁ more hm b L T κ
      (((ldSeg_below_named E Kc κ).1 _ first).2 h.bFirst) h.bMore
      (ldReqRefFinal_nums E Kc _ _ _ L κ h.bSegs)
      (ldSegRefAll_below E Kc _ T.A T.St₁ T.fz T.Az κ h.bTail) h.bLast)

end Cb
