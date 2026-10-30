-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingClosed.lean: closed lines on the written place of the
first chain's closing proximity test: the kernel's word on public numbers.

  `termLen_L`   the term lists as many rounds as the block declares
  `zip_L`       the block's rounds with their oracle messages, in all as many as the two parts' moves
  `sends_L`     one oracle message a stage but the first
  `hk_L`        h ≤ k at each stage
  `opensFit_L`  what the first reading round opens of older trees: one tree, own number 76, at depth
                23, behind 77 trees; `opensFit_L_sent`, `opensFit_L_depth`, `opensFit_L_src`: controls: no

Limits. Public numbers: nothing on what a table holds. The written place alone: under the head the
seated place is this one by `p12_at_head` (Johnson/AtFull/Shape/TestNumbersAtHead.lean). Nothing on
completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.OpensFitB
import Johnson.Desc.ProofFile.Honest.K12.TermCount
import Johnson.Desc.K12.Law.PlacesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open H2K.Member (piLFull)

#eval (proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).rounds.length
#eval termLen piLFull.nums.stages
#eval piLFull.nums.stages.length
#eval piLFull.nums.first.map fun x => (x.1.a, x.1.W)
#eval opensFitB false piLFull.nums.stages (proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).rounds [23]
  [.own 76] 77

theorem termLen_L : termLen piLFull.nums.stages =
    (proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).rounds.length := by decide +kernel

theorem zip_L : ((proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).rounds.zip
      (proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).oracles).length =
    firstLen piLFull.nums.stages + restLen piLFull.nums.stages := by decide +kernel

theorem sends_L : ((proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).oracles.flatMap id).length + 1 =
    piLFull.nums.stages.length := by decide +kernel

theorem hk_L : ∀ a ∈ piLFull.nums.stages, a.h ≤ a.k := by decide +kernel

theorem opensFit_L : opensFitB false piLFull.nums.stages
    (proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).rounds [23] [.own 76] 77 = true := by decide +kernel

theorem opensFit_L_sent : opensFitB false piLFull.nums.stages
    (proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).rounds [23] [.own 76] 76 = false := by decide +kernel

theorem opensFit_L_depth : opensFitB false piLFull.nums.stages
    (proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).rounds [22] [.own 76] 77 = false := by decide +kernel

theorem opensFit_L_src : opensFitB false piLFull.nums.stages
    (proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).rounds [23] [.own 77] 77 = false := by decide +kernel

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.termLen_L
#print axioms ProofFile.Honest.K12.AtFile.zip_L
#print axioms ProofFile.Honest.K12.AtFile.sends_L
#print axioms ProofFile.Honest.K12.AtFile.hk_L
#print axioms ProofFile.Honest.K12.AtFile.opensFit_L
