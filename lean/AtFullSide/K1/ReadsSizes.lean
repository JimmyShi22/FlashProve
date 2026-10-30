-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/ReadsSizes.lean: under the head the plan's number of reads at a segment is the columns
of the written layout's array "U3" there. Public data alone.

  nReads_at_head   nReads G.W l = colsW l, l < 25

Limits. Nothing on a run. Nothing on soundness, completeness or hiding.
-/
import AtFullSide.K1.ReadsCount
import Johnson.HonestTrace.U3Fit.HeadAtHead
import Johnson.HonestTrace.U3Fit.LayersLaid
import Johnson.Desc.ProofFile.Honest.K5.Law.AttValsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open OnBytes.HonestTrace.U3.Fit (colsW layersLaid_at_head nU_at_head)
open OnBytes.HonestTrace.U3.Att (nW_at_head)
open P5J (AtMgA TS)
open VerifiableInference.Desc (Chain)

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

set_option maxRecDepth 1000000 in
theorem head_cols : Johnson.G.xShapeFull.2.1.getD 2 0 = colsW 24 := by decide +kernel

/-- **THE PLAN's NUMBER OF READS IS THE ARRAY's COLUMNS.** -/
theorem nReads_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l < 25) :
    nReads G.W l = colsW l := by
  unfold nReads
  by_cases h24 : l = 24
  · subst h24
    rw [if_pos rfl, nU_at_head h hG]
    exact head_cols
  · rw [if_neg h24]
    obtain ⟨hT, -⟩ := IM.ground_tails h.scope h.reads h.laid.pub hG
    by_cases he : l % 2 = 0
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
      obtain ⟨hp, a, -, -, eG, -⟩ := hT g (by omega)
      rw [if_pos he, show 2 * g / 2 = g by omega, eG]
      obtain ⟨y, -, hn, hc, -⟩ := layersLaid_at_head h hG (by omega) eG
      exact hn.symm.trans hc
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
      obtain ⟨hp, a, -, -, -, eA, -⟩ := hT g (by omega)
      rw [if_neg he, show (2 * g + 1) / 2 = g by omega, eA]
      exact nW_at_head h hG (by omega) eA

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.nReads_at_head
