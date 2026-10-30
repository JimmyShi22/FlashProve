-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/TreesAtKey.lean: THE KEY FILE's THREE CHAINS' TREES, AT THE WRITTEN VALUES,
AS TERMS THAT THE KERNEL RUNS. Three equations by calls alone; seven tests by the kernel.

  `runA`, `runB`, `runC`: `treesRun` (TreesOfTags.lean) at the written sendings, with the tags
    that `tags_keySends0`, `1`, `2` (Johnson/AtFull/KeyBack/SentKey.lean) prove of
    their labels.
  `trees_A`, `trees_B`, `trees_C`: `treesOf …` at the three chains is `runA`, `runB`, `runC`. No
    premise.
  `runA_rounds`, `runB_rounds`, `runC_rounds`: the evaluated trees' rounds: the lists of
    `rounds_A`, `rounds_B`, `rounds_C`, which are had by another road, without tags.
    `runC_length`, `runA_tags`.
  `runC_length_bent`, `runA_tags_bent`: negative tests: at a bent value the kernel finds «false».
Limits. It names no m and no public file: that the written values are the planner's at any public
files is not said here. Of the trees' depths, widths and classes no test stands here.
Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.TreesOfTags
import Johnson.AtFull.KeyBack.FitsB
import Johnson.AtFull.KeyBack.SentKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open Johnson.G.OfPlan
open Johnson.G (keySends0 keySends1 keySends2)

/-- The key file's three chains' trees, each as a term that the kernel can evaluate. -/
def runA : List (Sent × Nat) :=
  treesRun keySends0 [some .indexMask, some .multiplicities, some (.stage .ranges 1),
    some (.stage .ranges 2), some (.stage .ranges 3), some .w] 1 []
def runB : List (Sent × Nat) :=
  treesRun keySends1 [some .foldedRow, some .omega, some (.stage .folded 1),
    some (.stage .folded 2), some (.stage .folded 3), some (.stage .folded 4),
    some (.stage .omega 1), some (.stage .omega 2), some (.stage .omega 3)] 0 masksB
def runC : List (Sent × Nat) :=
  treesRun keySends2 [some (.stage .own 1), some (.stage .own 2), some (.stage .own 3),
    some (.stage .own 4)] 0 []

/-- (EA) -/
theorem trees_A : treesOf keySends0 1 [] = runA :=
  treesOf_eq _ _ _ _ tags_keySends0 (sent_keySends0 "" 1)
/-- (EB) -/
theorem trees_B : treesOf keySends1 0 masksB = runB :=
  treesOf_eq _ _ _ _ tags_keySends1 (sent_keySends1 "" 0)
/-- (EC) -/
theorem trees_C : treesOf keySends2 0 [] = runC :=
  treesOf_eq _ _ _ _ tags_keySends2 (sent_keySends2 "" 0)

/-! ## Does the kernel run them? -/

theorem runC_rounds : runC.map (·.1.round) = [7, 14, 20, 26] := by decide +kernel
theorem runC_length : runC.length = 4 := by decide +kernel
theorem runC_length_bent : ¬ (runC.length = 5) := by decide +kernel
theorem runB_rounds : runB.map (·.1.round) = [1, 4, 4, 17, 25, 32, 39, 44, 49, 56, 63] := by
  decide +kernel
theorem runA_rounds : runA.map (·.1.round) = [0, 2, 18811, 18818, 18824, 18848] := by
  decide +kernel
theorem runA_tags : runA.map (·.1.tag) = [.indexMask, .multiplicities, .stage .ranges 1,
    .stage .ranges 2, .stage .ranges 3, .w] := by decide +kernel
theorem runA_tags_bent : ¬ (runA.map (·.1.tag) = [.multiplicities, .indexMask, .stage .ranges 1,
    .stage .ranges 2, .stage .ranges 3, .w]) := by decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.trees_A
#print axioms Johnson.AtFull.KeyBack.trees_B
#print axioms Johnson.AtFull.KeyBack.trees_C
#print axioms Johnson.AtFull.KeyBack.runC_rounds
#print axioms Johnson.AtFull.KeyBack.runC_length
#print axioms Johnson.AtFull.KeyBack.runC_length_bent
#print axioms Johnson.AtFull.KeyBack.runB_rounds
#print axioms Johnson.AtFull.KeyBack.runA_rounds
#print axioms Johnson.AtFull.KeyBack.runA_tags
#print axioms Johnson.AtFull.KeyBack.runA_tags_bent
