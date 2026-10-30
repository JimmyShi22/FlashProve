-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/FitGated.lean: CONDITIONAL.

What is here. The honest side's functions for the two product layers of the gated products return,
and what each returns has the public shape of its call (`gated_fit`, `gated2_fit`): two of the
fifteen clauses of the public test `k4MakersFit` (Johnson/Desc/ProofFile/Honest/K4/Part.lean), as
laws: at every input w and at all sampled values p whose fields have the sizes named; from the
plan's nine public facts (`K4Plan`). The tables' sizes and the test on a product layer's cube are
Law/SumLevels.lean's, the size of a turned stretch of challenges Law/SumPaid.lean's; the tensors and
the nine variables Johnson/Road/K4/C/ReadsNine.lean's; the numbers
Johnson/Road/K4/C/GatedNums.lean's and PlanLens.lean's.

  `gated_fit`   the first gated product's job.
  `gated2_fit`   the second's.

Not shown here. K4Plan (ITS FIELD sw BARS EVERY SHAPE BUT THOSE WITH THE LIBRARY's ELEVEN SWITCHES);
the sizes of the sampled values that each function reads: hypotheses. That the sampled values at the
zero challenges, at which k4MakersFit asks, have these sizes. The other thirteen clauses of
k4MakersFit. What the jobs' tables hold. By a walk of import lines the closure holds no module under
Johnson/RecCompile/, Johnson/Goal/ or Johnson/D/. Nothing on soundness, on completeness or on any
other property. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SumPaid
import Johnson.Road.K4.C.ReadsNine
import Johnson.Road.K4.C.GatedNums
import Johnson.Road.K4.C.PlanLens

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Model (HTailF2 Layer.Shape)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Road.K4.C (reads_nine tens_su gatedNums_of_plan planLens_of_plan)
open OnBytes.Desc.First.K4.Honest
open Inst.Model.FFSeg (Dim lF lFe)

variable {Q : K4Pub} {hS : OnBytes.Model.Layer.Shape} {pc : List (List String)} {tl : HTailF2}
  {D : Dim}

/-- **THE FIRST GATED PRODUCT's JOB IS MADE AND HAS ITS CALL's SHAPE.** CONDITIONAL: on A and the
two sizes. -/
theorem gated_fit (A : K4Plan hS pc Q.P Q.g tl D) (w : K4In) (p : Pts)
    (hrs : D.lL + lF D ≤ p.rs.size) (hzt : (ztOf Q p).size = D.lT) :
    ∃ j, jobGated Q w p = some j ∧ k4JobFits (k4LevelShape Q.P.rd.muH) j = true := by
  obtain ⟨ts, tu, hts, htu⟩ := tens_su A
  obtain ⟨hll, hPf, _, _, _, _⟩ := planLens_of_plan A
  have N := gatedNums_of_plan A
  obtain ⟨_, h9, _⟩ := reads_nine A.reads
  have ht : ∃ t, gatedTabs Q w = some t := by
    unfold gatedTabs
    dsimp only
    rw [hts, htu]
    exact ⟨_, rfl⟩
  obtain ⟨t, ht⟩ := ht
  refine ⟨_, by unfold jobGated; rw [ht]; rfl, levelJob_jobFits _ _ _ _
    (levelJob_fits _ _ t h9 ?_ (gatedTabs_size Q w t ht).1 (gatedTabs_size Q w t ht).2)⟩
  rw [Array.size_append, downFrom_size _ _ (by rw [hll, hPf]; exact hrs), hzt, hll, hPf, N.muH]

/-- **THE SECOND GATED PRODUCT's JOB IS MADE AND HAS ITS CALL's SHAPE.** CONDITIONAL: on A and the
three sizes. -/
theorem gated2_fit (A : K4Plan hS pc Q.P Q.g tl D) (w : K4In) (p : Pts)
    (hM : p.rhoM.size = D.lL - 1) (hrs : lFe D ≤ p.rs.size) (hrt : p.rt.size = D.lT) :
    ∃ j, jobGated2 Q w p = some j ∧ k4JobFits (k4LevelShape Q.P.rd.muH2) j = true := by
  obtain ⟨ts, tu, hts, htu⟩ := tens_su A
  have N := gatedNums_of_plan A
  have Ad := OnBytes.Road.admitted_of_layout A.lay A.sw.p3
  obtain ⟨_, _, h9⟩ := reads_nine A.reads
  have ht : ∃ t, gatedTabs2 Q w = some t := by
    unfold gatedTabs2
    dsimp only
    rw [hts, htu]
    exact ⟨_, rfl⟩
  obtain ⟨t, ht⟩ := ht
  refine ⟨_, by unfold jobGated2; rw [ht]; rfl, levelJob_jobFits _ _ _ _
    (levelJob_fits _ _ t (h9 (by rw [Ad.shape]; exact A.sw.p3)) ?_ (gatedTabs2_size Q w t ht).1
      (gatedTabs2_size Q w t ht).2)⟩
  rw [Array.size_append, Array.size_append, hM,
    downFrom_size _ _ (by rw [N.lfe]; exact hrs), hrt, N.lfe, N.muH2]

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.gated_fit
#print axioms ProofFile.Honest.K4.W.gated2_fit
