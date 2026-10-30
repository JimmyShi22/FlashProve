-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/DryProofBlocks.lean: the test on the numbers of blocks (`blocksFitB`,
OnBytes/Flat/BlocksBelow.lean) at the data of the written dry lists of a proof file
(Johnson/G/DryProofLit.lean), at the full-size and at the small example: as theorems by an
evaluation in Lean's kernel.

Statements and proofs, after Johnson/G/DryKeyBlocks.lean. `OnBytes.Three.Whole.of` is rewritten to
its eager twin (`whole_eqE`, Johnson/G/WholeEager.lean); then `decide +kernel`. The greatest number
is had from two tests: no round asks more, and some round asks as many (`blocksT_eq`).

Main names (the small example has Small for Full, and the depth 23 for 32):
  `blocksFit_wholePFull`: blocksFitB .two (WholeD.of 32 (Three.Whole.of ..)) = true, at the three
    lists of `dryProofFull`.
  `most_PFull`, `some_PFull`, `blocksT_wholePFull`: the greatest number of blocks that a round of
    these data asks is 24086; at the small example 3099. It serves as a control: with 2 ^ 14 |
    2 ^ 11 for 2 ^ 48 the test would say no.

Limits: the theorems speak of the written lists, which were made at ONE made-up request. That these
are what `OnBytes.Maker.dryProof` returns at the planner's answer at the shipped public files, the
key of zeros and the first block at that request is no theorem. AT THE FULL SIZE NO TEST THAT THE
BUILD RUNS HOLDS IT: whoever uses these theorems takes that equation as a premise. That the dry runs
state the same rounds at another request is not said. Nothing on soundness.


-/
import Johnson.G.DryProofLit
import Johnson.G.WholeEager
import Johnson.G.DryKeyBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes OnBytes.Maker OnBytes.Flat _root_.Run _root_.Run.PQ

/-! ## The full-size example -/

/-- The rounds of the data of the written lists, over the eager twin. -/
def rdsPFull : List RDT :=
  (WholeD.of 32 (wholeE dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2)).ds₁ ++
    ((WholeD.of 32 (wholeE dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2)).ds₂ ++
      (WholeD.of 32 (wholeE dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2)).ds₃)

set_option maxRecDepth 1000000 in
/-- No round of the data of the written lists asks 2 ^ 48 - 1 blocks or more. -/
theorem blocksFit_wholePFull : blocksFitB .two
    (WholeD.of 32 (Three.Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2)) = true := by
  rw [whole_eqE]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- No round asks more than 24086 blocks. -/
theorem most_PFull :
    (rdsPFull.all fun d => decide ((bsRound .two d.entry d.kind).b ≤ 24086)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Some round asks 24086 blocks. -/
theorem some_PFull :
    (rdsPFull.any fun d => decide ((bsRound .two d.entry d.kind).b = 24086)) = true := by
  decide +kernel

/-- The greatest number of blocks that a round of these data asks. -/
theorem blocksT_wholePFull : blocksT .two
    ((WholeD.of 32 (Three.Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2)).ds₁ ++
      ((WholeD.of 32 (Three.Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2)).ds₂ ++
        (WholeD.of 32
          (Three.Whole.of dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2)).ds₃)) = 24086 := by
  rw [whole_eqE]
  exact blocksT_eq .two rdsPFull 24086 most_PFull some_PFull

/-! ## The small example -/

/-- The rounds of the data of the written lists, over the eager twin. -/
def rdsPSmall : List RDT :=
  (WholeD.of 23 (wholeE dryProofSmall.1 dryProofSmall.2.1 dryProofSmall.2.2)).ds₁ ++
    ((WholeD.of 23 (wholeE dryProofSmall.1 dryProofSmall.2.1 dryProofSmall.2.2)).ds₂ ++
      (WholeD.of 23 (wholeE dryProofSmall.1 dryProofSmall.2.1 dryProofSmall.2.2)).ds₃)

set_option maxRecDepth 1000000 in
/-- No round of the data of the written lists asks 2 ^ 48 - 1 blocks or more. -/
theorem blocksFit_wholePSmall : blocksFitB .two
    (WholeD.of 23 (Three.Whole.of dryProofSmall.1 dryProofSmall.2.1 dryProofSmall.2.2)) = true := by
  rw [whole_eqE]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- No round asks more than 3099 blocks. -/
theorem most_PSmall :
    (rdsPSmall.all fun d => decide ((bsRound .two d.entry d.kind).b ≤ 3099)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Some round asks 3099 blocks. -/
theorem some_PSmall :
    (rdsPSmall.any fun d => decide ((bsRound .two d.entry d.kind).b = 3099)) = true := by
  decide +kernel

/-- The greatest number of blocks that a round of these data asks. -/
theorem blocksT_wholePSmall : blocksT .two
    ((WholeD.of 23 (Three.Whole.of dryProofSmall.1 dryProofSmall.2.1 dryProofSmall.2.2)).ds₁ ++
      ((WholeD.of 23 (Three.Whole.of dryProofSmall.1 dryProofSmall.2.1 dryProofSmall.2.2)).ds₂ ++
        (WholeD.of 23
          (Three.Whole.of dryProofSmall.1 dryProofSmall.2.1 dryProofSmall.2.2)).ds₃)) = 3099 := by
  rw [whole_eqE]
  exact blocksT_eq .two rdsPSmall 3099 most_PSmall some_PSmall

end Johnson.G

#print axioms Johnson.G.blocksFit_wholePFull
#print axioms Johnson.G.blocksFit_wholePSmall
#print axioms Johnson.G.blocksT_wholePFull
#print axioms Johnson.G.blocksT_wholePSmall
