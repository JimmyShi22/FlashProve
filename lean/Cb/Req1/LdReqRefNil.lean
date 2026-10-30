-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqRefNil.lean: the reference request with one segment (the last): its record, written
out.

A definition, a record, one statement (`Cb.Spec.ldReqRefNil`) and its proof. Bookkeeping, for
whoever builds an instance.
The reference request is the term `ldReqRef R first a₁ more hm b L T` (Cb/Req1/LdReqRef.lean):
`first` is a sending (`LdSendD`, Cb/Req1/LdSegKit.lean), `more` a list of moves (`LdProg`,
Cb/Req1/LdSeg.lean), L the list of segments with a closing, T the last segment (`LdRefT`), R the end
(`LdORE`, Cb/Obj/LdObjectReqEnd.lean).
The reference request with the empty list of segments with a closing is: first sendings; the last
segment (entry step, body, exit step); the final batching. The record `LdReqRefD`
(Cb/Req1/LdReqRefFinal.lean) then loses all clauses on the list. What is left is under Main names
(with the facts of layT, layB in `ldReqBase` itself, not in its closure `MaskFact.JCl`
(Cb/Req1/LdSegFreshS.lean): `LdReqRefD0` gives the record; the converse is not stated).

Main names:
  `ldReqBase first more`: the facts that are fresh behind the first sendings (it is `r.base₀`,
    whatever follows: by definition).
  `LdReqRefD0 ..`: `tail : T.Model`; hFirst, hMore, protoT, deg, ev, tie; own; layT: what zero
    knowledge asks of the body, beside its hypotheses, at facts that the entry step hands on from
    facts fresh behind the first sendings; layB: one such fact that the last segment's moves hand on
    as the wide fact of the final batching's own masks; fmt: the first sender hands the prover
    encoded index on; more's format; `T.FmtAt`; the numbers.
  `Spec.ldReqRefNil`: `LdReqRefD0 .. → LdReqRefD ..` at L := the empty list.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqRefFinal

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

section
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- the facts that are fresh behind the first sendings -/
def ldReqBase {a a₁ : LdStage E Kc} (first : LdSendD a) (more : LdProg first.tgt a₁) :
    MaskFact a₁.J.W → Prop :=
  more.After fun f => first.link.H.Fresh a.J.rels.rel first.link.P.bud f.kc f.Mk f.put

/-- The record at the empty list. -/
structure LdReqRefD0 (pp : ℕ) (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (a₁ : LdStage E Kc)
    (more : LdProg first.tgt a₁) (T : LdRefT R a₁)
    (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
    (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) : Prop where
  tail   : T.Model
  hFirst : first.Hyp
  hMore  : more.Hyp
  protoT : T.A.Proto pp
  deg    : 2 ≤ R.n
  ev     : R.Z.OK
  tie    : R.Tie
  own    : R.X.Own
  layT   : T.A.ZkAt pp
    (fun f => ∃ g, ldReqBase first more g ∧ ∀ Y : MaskFact a₁.J.W → Prop, Y g → T.entry.After Y f)
  layB   : ∃ (Rd : R.S.Ent → Prop) (Rr : R.S.O → Prop),
    (∀ n, R.Rd n → Rd n) ∧
    ∃ g,
      ldReqBase first more g ∧
      ∀ Y : MaskFact a₁.J.W → Prop, Y g →
        T.tail.After Y
          (R.X.src.wideFact Rd Rr (R.X.atOwn R.X.wAt) R.X.mask.Mk fun M => R.X.atVal R.X.wAt M)
  fmt    : ∃ (px' : first.Wp' → R.Cf.conf.PIdx)
        (φ₁ : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx a₁.J),
      (∀ w, px' (first.D.rest w).2 = w.2.1) ∧
      more.Fmt (first.tgt.fmt (⟨id, id⟩ : IxAt R.Cf.conf.E0 R.Cf.conf.E0) Prod.snd px'
          ((LdStage.start E Kc (R.O.jReq core)).S.qSum first.N qφ first.t)) φ₁ ∧
      T.FmtAt φ₁ q
  bFirst : (ldSendFamErr first.N first.Sd first.L : ℝ≥0∞) ≤ κ * (Fintype.card first.Sd.D : ℝ≥0∞)
  bMore  : more.Below κ
  bTail  : T.A.Nums κ
  bLast  : Err.Below (R.X.bt.nums R.Cf.conf.E0 Kc).err κ

end

def Spec.ldReqRefNil : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ)
      (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (a₁ : LdStage E Kc)
      (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (T : LdRefT R a₁)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞),
    LdReqRefD0 pp R core first a₁ more T qφ q κ →
    LdReqRefD pp R core first a₁ more hm a₁ .nil T qφ q κ

theorem ldReqRefNil : Spec.ldReqRefNil := by
  intro F E Kc _ _ _ _ _ pp R core first a₁ more hm T qφ q κ h
  obtain ⟨px', φ₁, f1, f2, f3⟩ := h.fmt
  exact
    { model := ⟨by rw [LdRefL.Model]; trivial, h.tail⟩
      proto := ⟨h.hFirst, h.hMore, by rw [LdRefL.Proto]; trivial, h.protoT, h.deg, h.ev, h.tie⟩
      own := h.own
      lay := by simp only [LdRefL.LayJ]
      layT := ldReqRefLay_mono E Kc _ T.A pp _ _
        (fun f ⟨g, hg, he⟩ => ⟨g, by simp only [LdRefL.LaidJ]; exact .base g hg, he⟩) h.layT
      layB := by
        obtain ⟨Rd, Rr, hRd, g, hg, hB⟩ := h.layB
        exact ⟨Rd, Rr, hRd, g, by simp only [LdRefL.LaidJ]; exact .base g hg, hB⟩
      fmt := ⟨px', φ₁, φ₁, f1, f2, by rw [LdRefL.FmtP], f3⟩
      bFirst := h.bFirst
      bMore := h.bMore
      bSegs := by rw [LdRefL.Nums]; trivial
      bTail := h.bTail
      bLast := h.bLast }

end Cb
