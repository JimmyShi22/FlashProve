-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/StoredArms.lean: THE THREE CLAUSES ON THE KEPT MEMBERS' STORED SAMPLE
ROWS AT THE TWO OTHER PLACES OF A SWITCH, IN THE GOALS' SCOPE: AT A STATE REACHED IN FRONT OF THE
OUTPUT HEAD's SWITCH (NUMBER 339), AND BEHIND THE FINISH's WAY IN AT A STATE REACHED IN FRONT OF THE
FINISH's SWITCH (NUMBER 353). As at a link (Returns/StoredReached.lean, Returns/StoredTables.lean):
`OldFits.stored` holds with no premise more; `FrontCore.reads` follows from `FrontCore.check`;
`TablesFit.stored` follows from four other clauses of the law. Statements with their proofs: calls.

  `head_goodS_reached`, `fin_goodS_reached` the front's statement has `SampleGoodS`
  `head_stored_reached`, `fin_stored_reached` `OldFits.stored`, in its own letters
  `head_reads_reached`, `fin_reads_reached` `FrontCore.reads`, from `FrontCore.check`
  `head_tables_reached`, `fin_tables_reached` `TablesFit.stored`, from `FrontCore.check` · `keptPos`
                    · `OldFits.keptCode` · `TablesFit.bitsKept`

The fronts are the library's own terms `headFrontOf s a T` and `finFrontOf t a Q`
(Johnson/Top/H0/Tw/K2C/Closed.lean), at which `HeadBehind` and `FinBehind` (Returns/ArmsBehind.lean)
ask these clauses; a, T and Q are free, since the front's statement reads none of them.

By, all the library's: `sw_head`, `sw_finish` (Johnson/P1K2R/HstReached.lean) · `finishFrontQ_st`
(Johnson/Top/H0/Tw/K2C/FinFront.lean). A near relative, not called: `both_at_front`
(Johnson/Top/H0/Tw/K2C/DebtsState.lean): `SampleGoodS` at a front that the library's `frontAt`
returns.

Limits. The clauses that are spent are premises here; under three named tests on the public part
Returns/PinArms.lean pays `check`, `keptCode` and `bitsKept` at both places. At the finish: h25, the
public part's shape has 25 links, and the way in's yes are premises. "Reached" is: over the list of
the wrapped sub-protocols. THE PREMISES IN FRONT ARE SHOWN MET TOGETHER BY NOBODY HERE: NO MEMBER.
This file's imports are heavy. Nothing on any property.


-/
import Johnson.Desc.K2.Honest.Returns.StoredTables
import Johnson.Top.H0.Tw.K2C.FinFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (SampleGoodS headFrontOf finFrontOf finishFrontQ
  finishFrontQ_st)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open P1K2 (Prep Nums numsAt prepOf sw_head sw_finish)
open _root_.Tw.K2 (readsMainOf)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-! ## In front of the output head's switch -/

theorem head_goodS_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some 24) = some n)
    {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    (a : HeadOwn) (T : SwitchTarget) : SampleGoodS (headFrontOf s a T).st :=
  (sw_head hS hR O hF hpl default "" hP hn hr).1.good

theorem head_stored_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some 24) = some n)
    {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    (a : HeadOwn) (T : SwitchTarget) :
    ∀ o ∈ (switchKept (headFrontOf s a T).f.rows).toList,
      ∀ r ∈ ((headFrontOf s a T).st.oracles.getD o default).sampleRows.toList,
        r.runs.size = 0 ∧ r.forms.size = 0 :=
  oldFits_stored (head_goodS_reached hS hR O hF hpl hP hn hr a T).good _

theorem head_reads_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some 24) = some n)
    {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    (a : HeadOwn) (T : SwitchTarget)
    (check : switchTargetCheck (headFrontOf s a T).st (headFrontOf s a T).f.rows
      (headFrontOf s a T).T = true) :
    ∀ o ∈ (switchKept (headFrontOf s a T).f.rows).toList,
      ∀ r ∈ ((headFrontOf s a T).st.oracles.getD o default).sampleRows.toList,
        readsMainOf o r = true :=
  reads_stored (head_goodS_reached hS hR O hF hpl hP hn hr a T).good check

theorem head_tables_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some 24) = some n)
    {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    (a : HeadOwn) (T : SwitchTarget)
    (check : switchTargetCheck (headFrontOf s a T).st (headFrontOf s a T).f.rows
      (headFrontOf s a T).T = true)
    (keptPos : ∀ k ∈ (headFrontOf s a T).T.kept.toList, 0 < k.shape.mainRows)
    (keptCode : ∀ o ∈ (switchKept (headFrontOf s a T).f.rows).toList,
      ((headFrontOf s a T).st.oracles.getD o default).shape.code = (headFrontOf s a T).f.rows.code)
    (bitsKept : ∀ u ∈ (sizesAt (headFrontOf s a T).st (headFrontOf s a T).f.rows
        (headFrontOf s a T).T).kept,
      ceilLog2 u.mainRows + ((headFrontOf s a T).st.codes.base.getD
        (headFrontOf s a T).f.rows.code default).logEll ≤ 63) :
    ∀ o ∈ (switchKept (headFrontOf s a T).f.rows).toList,
      ∀ r ∈ ((headFrontOf s a T).st.oracles.getD o default).sampleRows.toList,
        (∀ v ∈ r.terms.toList,
          v.v.pairs.length = (headFrontOf s a T).st.tableBits o .main ∧ Own.InOrder v.v) ∧
          ∀ u ∈ r.units.toList, u.index < 2 ^ (headFrontOf s a T).st.tableBits o .main :=
  tables_stored (head_goodS_reached hS hR O hF hpl hP hn hr a T) check keptPos keptCode bitsKept

/-! ## Behind the finish's way in -/

theorem fin_goodS_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (h25 : Z.first.shape.link.length = 25) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s)) (he : finishFrontQ s = .ok t)
    (a : FinOwn) (Q : ReqGroup) : SampleGoodS (finFrontOf t a Q).st := by
  show SampleGoodS t.st
  rw [finishFrontQ_st he]
  exact fun o x hx hs => (sw_finish hS hR O hF hpl h25 default "" hP hn hr he).1.good o x hx hs

theorem fin_stored_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (h25 : Z.first.shape.link.length = 25) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s)) (he : finishFrontQ s = .ok t)
    (a : FinOwn) (Q : ReqGroup) :
    ∀ o ∈ (switchKept (finFrontOf t a Q).f.rows).toList,
      ∀ r ∈ ((finFrontOf t a Q).st.oracles.getD o default).sampleRows.toList,
        r.runs.size = 0 ∧ r.forms.size = 0 :=
  oldFits_stored (fin_goodS_reached hS hR O hF hpl h25 hP hn hr he a Q).good _

theorem fin_reads_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (h25 : Z.first.shape.link.length = 25) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s)) (he : finishFrontQ s = .ok t)
    (a : FinOwn) (Q : ReqGroup)
    (check : switchTargetCheck (finFrontOf t a Q).st (finFrontOf t a Q).f.rows
      (finFrontOf t a Q).T = true) :
    ∀ o ∈ (switchKept (finFrontOf t a Q).f.rows).toList,
      ∀ r ∈ ((finFrontOf t a Q).st.oracles.getD o default).sampleRows.toList,
        readsMainOf o r = true :=
  reads_stored (fin_goodS_reached hS hR O hF hpl h25 hP hn hr he a Q).good check

theorem fin_tables_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (h25 : Z.first.shape.link.length = 25) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s)) (he : finishFrontQ s = .ok t)
    (a : FinOwn) (Q : ReqGroup)
    (check : switchTargetCheck (finFrontOf t a Q).st (finFrontOf t a Q).f.rows
      (finFrontOf t a Q).T = true)
    (keptPos : ∀ k ∈ (finFrontOf t a Q).T.kept.toList, 0 < k.shape.mainRows)
    (keptCode : ∀ o ∈ (switchKept (finFrontOf t a Q).f.rows).toList,
      ((finFrontOf t a Q).st.oracles.getD o default).shape.code = (finFrontOf t a Q).f.rows.code)
    (bitsKept : ∀ u ∈ (sizesAt (finFrontOf t a Q).st (finFrontOf t a Q).f.rows
        (finFrontOf t a Q).T).kept,
      ceilLog2 u.mainRows + ((finFrontOf t a Q).st.codes.base.getD
        (finFrontOf t a Q).f.rows.code default).logEll ≤ 63) :
    ∀ o ∈ (switchKept (finFrontOf t a Q).f.rows).toList,
      ∀ r ∈ ((finFrontOf t a Q).st.oracles.getD o default).sampleRows.toList,
        (∀ v ∈ r.terms.toList,
          v.v.pairs.length = (finFrontOf t a Q).st.tableBits o .main ∧ Own.InOrder v.v) ∧
          ∀ u ∈ r.units.toList, u.index < 2 ^ (finFrontOf t a Q).st.tableBits o .main :=
  tables_stored (fin_goodS_reached hS hR O hF hpl h25 hP hn hr he a Q) check keptPos keptCode
    bitsKept

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_goodS_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_stored_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_reads_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_tables_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_goodS_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_stored_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_reads_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_tables_reached
