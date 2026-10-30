-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ReadsLiveAtBatch.lean: the proof of the statement of
Johnson/P1K8R/ReadsLiveAtBatchStatement.lean, to the letter. A lemma; none of the library's goals.

How. A joining of other files' theorems. `readsLive_of_laid`: `readsLive_of`
(Johnson/Desc/K8/Honest/ReadsLiveOf.lean: one live table a matrix) at `head_liveTables`
(Johnson/Desc/K8/Honest/HeadLiveTables.lean); that lemma's public premises as closed numbers: the
matrices are the written list and their number is 8 (`plan_in_scope`,
Johnson/Desc/Kinds/Law/HeadPlanWritten.lean); five numbers of the head's shape (`hS_in_scope`,
Johnson/Goal/Meaning/HeadShapeScope.lean). THE IMPORTS STAND AS THEY STOOD: nothing here calls
HeadListAtBatch.lean, TiesAtBatch.lean or Johnson/Desc/First/Link/Law/FitsMsBuilt.lean;
ReadsLiveAlongFold.lean of this folder, which imports this file, calls theorems of the last two
through it.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.P1K8R.ReadsLiveAtBatchStatement
import Johnson.P1K8R.HeadListAtBatch
import Johnson.P1K8R.TiesAtBatch
import Johnson.Desc.K8.Honest.HeadLiveTables
import Johnson.Desc.K8.Honest.ReadsLiveOf
import Johnson.Desc.Kinds.Law.HeadPlanWritten
import Johnson.Goal.Meaning.HeadShapeScope
import Johnson.Desc.First.Link.Law.FitsMsBuilt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.K8.Honest (tiesLaid readsLive readsLive_of head_liveTables)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (matsW plan_in_scope)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **From the closed list to the test's yes.** -/
theorem readsLive_of_laid : ReadsLiveOfLaid := by
  intro P pp lay W cov x t tl hS hR hpub e hf hm hn hT hF
  obtain ⟨f1, f2, f3, f4, z1, z2, z3⟩ := hF
  have PW := plan_in_scope hS hR hpub
  have eS := _root_.Meaning.HeadS.hS_in_scope hS hR hpub
  have eN : W.hS.NHf = 4 := by rw [eS]; rfl
  have eA : W.hS.la = 16 := by rw [eS]; rfl
  have eT : W.hS.T = 1024 := by rw [eS]; rfl
  have eB : W.hS.lmbH = 15 := by rw [eS]; rfl
  have eL : W.hS.lt = 10 := by rw [eS]; rfl
  have d0 : ∀ q, q < 4 → (matsW.getD q {}).m % 2 ^ 16 = 0 := by decide
  refine readsLive_of tl hT fun mu hmu => ?_
  rw [hn, PW.nm] at hmu
  refine head_liveTables W.hS W.HLy W.H cov x t tl e hf hm f1 f2 f3 f4 z1 z2 z3 ?_ ?_ ?_ ?_ ?_ ?_ mu
    (by rw [eN]; exact hmu)
  · rw [eT, eL]
    decide
  · intro q hq
    rw [eN] at hq
    rw [PW.mats, eA]
    exact d0 q hq
  · rw [PW.mats, eN, eT]
    decide
  · rw [PW.mats, eN, eT]
    decide
  · rw [PW.mats, eN, eB]
    decide
  · rw [PW.mats, eN, eA]
    decide

end P1K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms P1K8.readsLive_of_laid
