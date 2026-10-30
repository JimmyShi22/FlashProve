-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/AttentionBookAtBase.lean: the structure AttentionBookAt (Honest/K5/Law/AttentionBookAtAFilling.lean)
at a return of baseMaker (E2E/BaseMaker.lean), under the library's head, with no other premise. This is
the return of the filling that the online filling reads through, not the online maker's return.

  switchLotAtBase, switchLotAtBase_mem   the code switch's lot in that filling
  base_lays_switch    that filling lays the switch
  attention_book_at_base   conditional: h; hA: the structure

h, the library's head, and hA, that the maker returns, are hypotheses here. The files argument of
baseFilling enters nowhere. No property is
claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import E2E.BaseMaker
import Johnson.Desc.ProofFile.Honest.K5.Law.AttentionBookAtAFilling
import Johnson.Desc.ProofFile.Honest.Law.FillPairs

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm.Attention
open ProofFile.Honest ProofFile.Honest.K5
open ProofFile.Honest.Term (baseFilling baseMaker matrixInput)
open VerifiableInference.Desc (Chain KindName)
open P5J (AtMgA TS)

/-- The code switch's lot in the filling that the online filling reads through. -/
abbrev switchLotAtBase : HLot (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit :=
  HLot.byPub matrixInput.weights fun wt => HLot.byRows (widerRows OnBytes.HonestTrace.Sz.ref) fun D =>
    K2.switchLot D fun w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells => ⟨w.trace, wt w.w₀, w.rc⟩

/-- That lot is a lot of the filling. -/
theorem switchLotAtBase_mem (files : VerifierAndGoals.PublicFiles) : switchLotAtBase ∈ (baseFilling files).lots := by
  show _ ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).lots
  rw [fillPairs_lots]
  exact List.mem_map.2 ⟨(switchLotAtBase, KindName.K2),
    List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩

/-- **That filling lays the code switch.** -/
theorem base_lays_switch (files : VerifierAndGoals.PublicFiles) : LaysTheSwitch (baseFilling files) := by
  intro Z G p hp
  obtain ⟨y, hy, e1, e2⟩ : ∃ y ∈ switchLotAtBase.halves Z G, y.place = p.place ∧ y.parts ≠ [] :=
    switchHalves_has _ _ _ _ _ _ p hp
  exact ⟨switchLotAtBase, switchLotAtBase_mem files, y, hy, e1, e2⟩

/-- **The book at a return of baseMaker.** CONDITIONAL: h; hA. -/
theorem attention_book_at_base {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    {places : H2U.Places4} {firstChain : Chain TS ProofFile.Cl} {description : OnBytes.Maker.WholeD}
    {run : LPFD.Full.RunPF} {x : VerifiableInference.Desc.First.Look.Place} {Zp : ProofFile.Pub}
    (hA : baseMaker files = .ok A)
    (h : AtMgA OnBytes.secondHashFunction files description run Zp places firstChain x) :
    AttentionBookAt A :=
  attention_book_at h hA (base_lays_switch files)

end AtPublicFiles.AtFiles.HonestTerm.Attention

#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.switchLotAtBase_mem
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.base_lays_switch
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.attention_book_at_base
