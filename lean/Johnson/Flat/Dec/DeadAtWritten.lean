-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Dec/DeadAtWritten.lean: THE BRANCH THAT REFUSES, WHERE THE ENTRY FILE's ROUNDS STAY PINNED AT THE WRITTEN ONES: the one test on
numbers (`sizeNumbersFitAtFullSize`, Johnson/Flat/Dec/FailsClosed.lean) says yes at two whole files WITHOUT A ROUND, both depths 0, ds := `dsFull`,
xs := `frD.xs`, at every K from 140 on with K + 2 < 2^40 and every v from 13555 on.
  `entryFitB_dsFull_140`: the entry's four tests at K := 140, by Lean's kernel. `entryFitB_dsFull_139`: A CONTROL: at 139 the test says NO: the
    entry's greatest round needs just 140 blocks. `entryFitB_mono`: more blocks do no harm.
  `deadW`: the data made of three empty lists by the library's own maker (`WholeD.of 0 (Three.Whole.of [] [] [])`).
  `frameFitFullD_dead`: the test's yes there.
Why. A description that pins the entry's rounds closes the two whole files' data, the plan's depths and the three decisions alone: at its branch that
refuses the count still holds the entry's 13541 queries and K has to bear the entry's rounds.
Limits: a test on numbers. OF THE WRITTEN ROUNDS. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Dec.FailsClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice OnBytes.Maker _root_.Run

set_option maxRecDepth 1000000 in
theorem entryFitB_dsFull_140 : entryFitB 140 dsFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control. -/
theorem entryFitB_dsFull_139 : entryFitB 139 dsFull = false := by decide +kernel

theorem entryFitB_mono {K K' : ℕ} (h : K ≤ K') {ds : List TypedOracleCompiler.Run.PQ.RD}
    (hf : entryFitB K ds = true) : entryFitB K' ds = true := by
  unfold entryFitB at hf ⊢
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hf ⊢
  exact fun d hd => ⟨⟨⟨(hf d hd).1.1.1.trans h, (hf d hd).1.1.2⟩, (hf d hd).1.2⟩, (hf d hd).2⟩

/-- The data of three empty lists, by the library's own maker. -/
def deadW : WholeD := OnBytes.Maker.WholeD.of 0 (OnBytes.Three.Whole.of [] [] [])

set_option maxRecDepth 1000000 in
/-- The count there: 14 for the two whole files, 13541 for the entry. -/
theorem cntFrameFullD_dead : cntFrameFullD deadW deadW dsFull frD.xs 0 0 = 13555 := by
  rw [cntFrameFullD_landed]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kThree_dead : kThree .two deadW [] deadW = 0 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem fits_dead : deadW.workFit = true ∧ deadW.depthFit = true := by decide +kernel

/-- **The test says yes at the branch that refuses.** -/
theorem frameFitFullD_dead {K v : ℕ} (hK : 140 ≤ K) (hK2 : K + 1 + 1 < 2 ^ 40) (hv : 13555 ≤ v) :
    sizeNumbersFitAtFullSize K v 0 0 deadW deadW dsFull frD.xs = true := by
  unfold sizeNumbersFitAtFullSize
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨kThree_dead.le.trans (Nat.zero_le _), entryFitB_mono hK entryFitB_dsFull_140⟩,
    fits_dead.1⟩, fits_dead.2⟩, fits_dead.1⟩, fits_dead.2⟩, cntFrameFullD_dead.le.trans hv⟩, hK2⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.entryFitB_dsFull_140
#print axioms VerifiableInference.OnPublicFiles.entryFitB_dsFull_139
#print axioms VerifiableInference.OnPublicFiles.frameFitFullD_dead
