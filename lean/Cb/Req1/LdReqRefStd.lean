-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqRefStd.lean: the reference request with one first sending, standard senders and the
groups' own links: its record; and the model's duty, named.

Definitions, one statement (`Cb.Spec.ldReqRefStd`) and its proof: an assembly.
The reference request is the term `ldReqRef R first a₁ more hm b L T`, with its first sending
`first` (`LdSendD`, Cb/Req1/LdSegKit.lean), its list L of segments, its last segment T and its end R
(Cb/Req1/LdReqRef.lean; `LdORE`, Cb/Obj/LdObjectReqEnd.lean).
Cb/Req1/LdReqRefFinal.lean's record `LdReqRefD` still takes (1) a list "more" of further first
sendings and steps, as it is; (2) hypotheses on senders and on each closing's link bridge-to-fold.
Here: (1) the list is empty: this narrows the record to requests with one first sending (the wider
form stays in Cb/Req1/LdReqRefFinal.lean). That a request has one first prover message, which holds
the first segment's first messages and the index-mask message, restates this protocol's technical
report in our own words (lean/CREDITS.md); (2) every sender is the
standard sender, every such link the group's own (Cb/Req1/LdReqProtoStd.lean).

Main names:
  `ldReqRef1 R first b L T`: the request: first; the segments of L, each with its closing; the last
    segment T; the final batching.
  `LdModelDuty R L T`: the model's duty: what whoever supplies a model (the computation that a
    request claims, arithmetized) has to prove:
    `model`: `LdReqModel L T` (Cb/Req1/LdReqModel.lean): M1 the steps between segments (the first
      one holds the arithmetization proper), M2 the steps between blocks, M3 `Link` and `Back`, M4
      the degrees, M5 the multiplicities, M6 what else is claimed is carried.
    `langs`: the two languages agree: whatever instance has a witness in the relaxed relation `Rno`
      has one in the exact relation `Ryes`. With an approximate range check (honest bound smaller
      than the relaxed one) this is a theorem on the model: "whatever passes with the slack also has
      an honest witness"; it can be false for a model in which the slack can move an output. By the
      technical report the relaxed relation is the same set of conditions with the larger bound on
      cells, and the two relations have one language if the conditions admit the reply (cells below
      the strict bound exist), force it (over the integers, for all cells below the relaxed bound),
      and nothing wraps around the characteristic: these three are what "langs" comes to for a
      supplier.
    On M1: in the technical report there are no such steps: the relation behind segment s is
      defined to hold the next segment's conditions on the cell messages just sent and all later
      segments' conditions on cells that are a further part of the witness until sent; consecutive
      blocks have equal relations. What a model supplies and proves there is one definition (a
      partition of the conditions into segments: cells, the earlier matrices still read, summands,
      key maps with tables, over maps of three kinds, of bounded degree, with public coefficients
      that the verifier evaluates) and one equivalence (the constraints hold if and only if for all
      segments the zero and lookup predicates hold). That the steps are free moves with hypotheses
      here is this library's form; Cb/Req1/LdSegNext.lean goes towards the report's.
    (M7, "the model's maps between segments keep the record and the prover encoded index", stands
      inside "fmt": the formats of the entry and exit steps.)
  `LdReqRefDS ..`: the record: duty | std: for some pads' field Fp (it need not be the
    configuration's base field): `first.IsStd Fp`, `L.ProtoS Fp pp`, `T.A.ProtoS Fp pp` | the final
    batching's degree, evader, `R.Tie` | own | lay, layT, layB (in the closed sets:
    Cb/Req1/LdReqRefLayJ.lean) | fmt | numbers.
  `Spec.ldReqRefStd`: `LdReqRefDS .. → LdReqRefD ..` (at more := the empty list).

Limits: what still speaks of more than data, among them: in std, inside `IsStd` and `IsGrp`:
`Y.OK t` (`priv`, `hides`), `ListLE`, `Evades`, `Sh.par.Hyp` (`errs`, `zk`), `ListAt`; the evaders'
`OK` (the head of Cb/Req1/LdReqProtoStd.lean); in lay: `Fresh`, "does not look" of senders and
links; in fmt and the numbers: each closing's link's format and list of errors; the entry and exit
steps as moves (the model's duty).
No instance that meets the hypotheses of `ldReqRefStd` is part of this library; as far as the
library shows, this theorem may hold of nothing.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqProtoStd
import Cb.Req1.LdReqRefFinal
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

section
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The request with one first sending. -/
def ldReqRef1 (R : LdORE F E Kc) {a : LdStage E Kc} (first : LdSendD a)
    (b : LdStage E Kc) (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b) : LdReq a R.z :=
  ldReqRef R first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _) b L T

/-- The model's duty. -/
structure LdModelDuty (R : LdORE F E Kc) {a₁ b : LdStage E Kc}
    (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b) : Prop where
  model : LdReqModel L T
  langs : ∀ i x w, R.Cf.conf.Rno i x w → ∃ w', R.Cf.conf.Ryes i x w'

/-- The record. -/
structure LdReqRefDS (pp : ℕ) (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
    (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
    (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
    (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) : Prop where
  duty   : LdModelDuty R L T
  std    : ∃ (Fp : Type) (_ : Field Fp) (_ : Fintype Fp) (_ : Algebra Fp E),
    first.IsStd Fp ∧ L.ProtoS Fp pp ∧ T.A.ProtoS Fp pp
  deg    : 2 ≤ R.n
  ev     : R.Z.OK
  tie    : R.Tie
  own    : R.X.Own
  lay    : L.LayJ pp (ldReqRef1 R first b L T).base₀
  layT   : T.A.ZkAt pp (fun f =>
    ∃ g,
      L.LaidJ (ldReqRef1 R first b L T).base₀ g ∧
      ∀ Y : MaskFact b.J.W → Prop, Y g → T.entry.After Y f)
  layB   : ∃ (Rd : R.S.Ent → Prop) (Rr : R.S.O → Prop),
    (∀ n, R.Rd n → Rd n) ∧
    ∃ g,
      L.LaidJ (ldReqRef1 R first b L T).base₀ g ∧
      ∀ Y : MaskFact b.J.W → Prop, Y g →
        T.tail.After Y
          (R.X.src.wideFact Rd Rr (R.X.atOwn R.X.wAt) R.X.mask.Mk fun M => R.X.atVal R.X.wAt M)
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

def Spec.ldReqRefStd : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ)
      (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞),
    LdReqRefDS pp R core first b L T qφ q κ →
    LdReqRefD pp R core first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _) b L T qφ q κ

theorem ldReqRefStd : Spec.ldReqRefStd := by
  intro F E Kc _ _ _ _ _ pp R core first b L T qφ q κ h
  obtain ⟨px', φb, f1, f2, f3⟩ := h.fmt
  obtain ⟨Fp, _, _, _, s1, s2, s3⟩ := h.std
  exact
    { model := h.duty.model
      proto := ldReqProtoStd Fp F E Kc pp R _ _ _ first (.nil first.tgt) L T
        ⟨s1, LdProg.hyp_nilK _, s2, s3, h.deg, h.ev, h.tie⟩
      own := h.own
      lay := h.lay
      layT := h.layT
      layB := h.layB
      fmt := ⟨px', _, φb, f1, (LdProg.fmt_nil _ _ _).2 rfl, f2, f3⟩
      bFirst := h.bFirst
      bMore := LdProg.below_nil _ κ
      bSegs := h.bSegs
      bTail := h.bTail
      bLast := h.bLast }

end Cb
