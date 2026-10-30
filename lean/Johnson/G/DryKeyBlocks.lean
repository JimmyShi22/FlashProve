-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/DryKeyBlocks.lean: the test on the numbers of blocks (`blocksFitB`,
OnBytes/Flat/BlocksBelow.lean) at the data of the written dry lists of a key file
(Johnson/G/DryKeyLit.lean), at the full-size and at the small example: as theorems by an evaluation
in Lean's kernel.

Statements and proofs. `OnBytes.Three.Whole.of` is rewritten to its twin (`whole_eq`,
Johnson/G/WholeTwin.lean); then `decide +kernel`. The greatest number is a fold by the greater, at
which the kernel runs out of stack at some thousands of rounds: so it is had from two tests that the
kernel does evaluate: no round asks more, and some round asks as many (`blocksT_eq`).

Main names (the small example has Small for Full, and the depth 23 for 32):
  `blocksFit_wholeFull`: blocksFitB .two (WholeD.of 32 (Three.Whole.of ..)) = true, at the three
    lists of `dryKeyFull`.
  `most_Full`, `some_Full`, `blocksT_wholeFull`: the greatest number of blocks that a round of
    these data asks is 140; at the small example 99. It serves as a control: with 2 ^ 7 | 2 ^ 6
    for 2 ^ 48 the test would say no.

Limits: the theorems speak of the written lists. That these are what `OnBytes.Maker.dryKey` returns
at the planner's answer at the shipped public files and the key of zeros is no theorem. AT THE FULL
SIZE NO TEST THAT THE BUILD RUNS HOLDS IT: whoever uses these theorems takes that equation as a
premise. Nothing on a proof file. Nothing on soundness.


-/
import Johnson.G.DryKeyLit
import Johnson.G.WholeTwin
import OnBytes.Flat.BlocksBelow
import OnBytes.Maker.WholeOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes OnBytes.Maker OnBytes.Flat _root_.Run _root_.Run.PQ

/-- The greatest number of blocks of a list of rounds is n, if no round asks more and some round
asks n. -/
theorem blocksT_eq (f : Fmt.Fld) (l : List RDT) (n : ℕ)
    (h1 : (l.all fun d => decide ((bsRound f d.entry d.kind).b ≤ n)) = true)
    (h2 : (l.any fun d => decide ((bsRound f d.entry d.kind).b = n)) = true) :
    blocksT f l = n := by
  have hle : blocksT f l < n + 1 :=
    foldl_max_lt (fun d : RDT => (bsRound f d.entry d.kind).b) (n + 1) l 0 (Nat.succ_pos n)
      fun d hd => by
        have h3 := of_decide_eq_true (List.all_eq_true.1 h1 d hd)
        show (bsRound f d.entry d.kind).b < n + 1
        omega
  obtain ⟨d, hd, he⟩ := List.any_eq_true.1 h2
  have h4 := le_blocksT f l d hd
  have h5 := of_decide_eq_true he
  omega

/-! ## The full-size example -/

/-- The rounds of the data of the written lists, over the twin. -/
def rdsFull : List RDT :=
  (WholeD.of 32 (wholeTwin dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2)).ds₁ ++
    ((WholeD.of 32 (wholeTwin dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2)).ds₂ ++
      (WholeD.of 32 (wholeTwin dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2)).ds₃)

set_option maxRecDepth 1000000 in
/-- No round of the data of the written lists asks 2 ^ 48 - 1 blocks or more. -/
theorem blocksFit_wholeFull : blocksFitB .two
    (WholeD.of 32 (Three.Whole.of dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2)) = true := by
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- No round asks more than 140 blocks. -/
theorem most_Full :
    (rdsFull.all fun d => decide ((bsRound .two d.entry d.kind).b ≤ 140)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Some round asks 140 blocks. -/
theorem some_Full :
    (rdsFull.any fun d => decide ((bsRound .two d.entry d.kind).b = 140)) = true := by
  decide +kernel

/-- The greatest number of blocks that a round of these data asks. -/
theorem blocksT_wholeFull : blocksT .two
    ((WholeD.of 32 (Three.Whole.of dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2)).ds₁ ++
      ((WholeD.of 32 (Three.Whole.of dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2)).ds₂ ++
        (WholeD.of 32 (Three.Whole.of dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2)).ds₃)) =
      140 := by
  rw [whole_eq]
  exact blocksT_eq .two rdsFull 140 most_Full some_Full

/-! ## The small example -/

/-- The rounds of the data of the written lists, over the twin. -/
def rdsSmall : List RDT :=
  (WholeD.of 23 (wholeTwin dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2)).ds₁ ++
    ((WholeD.of 23 (wholeTwin dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2)).ds₂ ++
      (WholeD.of 23 (wholeTwin dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2)).ds₃)

set_option maxRecDepth 1000000 in
/-- No round of the data of the written lists asks 2 ^ 48 - 1 blocks or more. -/
theorem blocksFit_wholeSmall : blocksFitB .two
    (WholeD.of 23 (Three.Whole.of dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2)) = true := by
  rw [whole_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- No round asks more than 99 blocks. -/
theorem most_Small :
    (rdsSmall.all fun d => decide ((bsRound .two d.entry d.kind).b ≤ 99)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Some round asks 99 blocks. -/
theorem some_Small :
    (rdsSmall.any fun d => decide ((bsRound .two d.entry d.kind).b = 99)) = true := by
  decide +kernel

/-- The greatest number of blocks that a round of these data asks. -/
theorem blocksT_wholeSmall : blocksT .two
    ((WholeD.of 23 (Three.Whole.of dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2)).ds₁ ++
      ((WholeD.of 23 (Three.Whole.of dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2)).ds₂ ++
        (WholeD.of 23 (Three.Whole.of dryKeySmall.1 dryKeySmall.2.1 dryKeySmall.2.2)).ds₃)) =
      99 := by
  rw [whole_eq]
  exact blocksT_eq .two rdsSmall 99 most_Small some_Small

end Johnson.G

#print axioms Johnson.G.blocksFit_wholeFull
#print axioms Johnson.G.blocksFit_wholeSmall
#print axioms Johnson.G.blocksT_wholeFull
#print axioms Johnson.G.blocksT_wholeSmall
