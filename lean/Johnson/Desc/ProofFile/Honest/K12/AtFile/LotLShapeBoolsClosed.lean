-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLShapeBoolsClosed.lean

It states no goal. No property of the protocol is claimed.

THE TWO PUBLIC TESTS ON THE SHAPE IN
FRONT OF THE FIRST CHAIN's CLOSING PROXIMITY TEST (`frontFiveB`, K12/FrontAtShape.lean; `frontPlainB`,
K12/FrontPlainB.lean) SAY YES AT EVERY SHAPE WHOSE LAST GROUP, LAST TWO MESSAGES, LAST TREE AND LAST TWO
PLACES ARE THE WRITTEN ONES: BY LEAN's KERNEL, ONCE, WITH ALL THAT STANDS IN FRONT OF THESE AS FREE
LETTERS. Four definitions; two closed lines; six controls.

  `closingGroup`     group 25: codes 0 and 0, the one member 185, not kept, 658 open rows (one plain, then
                     657 of the generator's kind), no test begun
  `carrierMessage`   message 185: two main rows of degree 3 at code 0, one answer; sampled, one sample
                     row, the public pad, in group 25. LETTERS: its ledger, whether it is spent
  `maskMessage`      message 186: one mask row at mask code 0, no answer; not sampled, not spent.
                     LETTERS: its count of sample rows, its pad, its groups, its ledger
  `closingTree`      tree 76: depth 23, its two parts 185 and 186, opened at one list only, not yet
                     opened. LETTER: where its root is taken from
  `closingShape_passes_five`    `frontFiveB piLFull codesFull` says yes
  `closingShape_passes_plain`   `frontPlainB piLFull` says yes at the written finish's sending
  `closingShape_controls`       THE FIRST TEST SAYS NO: at a kept member · at one open row fewer · at a
                     third part in the tree · at a carrier in group 24 alone · at 76 roots · at a mask
                     that is spent

The values are those that one print of one run shows (a literal that is not in this file;
not imported, not beneath this file): here they are definitions, tied to no run.

By what. `kernel_rfl` (Johnson/Unfolds/KernelRfl.lean): the goal is closed with `Eq.refl`, and Lean's kernel
alone compares the two sides when the theorem is added. `decide +kernel` takes no goal with free
letters. That the kernel returns with these letters free SHOWS that the tests read none of them: neither
an entry in front, nor the seven fields named as letters above.

Limits.
- No state is shown to have this shape: LotLShapeBoolsStand.lean takes that as a premise.
- At the written place `piLFull`, the written codes `codesFull`, the written finish `finishW` alone.
- Nothing on values. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLShapeBoolsLaid
import Johnson.Desc.ProofFile.Honest.K12.FrontAtShape
import Johnson.Desc.ProofFile.Honest.K12.FrontPlainB
import Johnson.Desc.K12.Law.PlacesFull
import Johnson.Unfolds.KernelRfl
import AtFullSide.K12.FitsAtHeadL

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.LotL
open VerifiableInference.Desc.Ground.Sh (CoreSh GrpSh OrcSh TreeSh SrcSh)
open H2K.Member (piLFull codesFull)
open ProofFile.Honest.K12 (frontFiveB frontPlainB)
open ProofFile.Honest.K12.AtProof (finishW sentL)
open Johnson.Unfolds

/-- **Group 25 in front of the closing test.** -/
def closingGroup : GrpSh :=
  ⟨0, 0, [185], [false], .plain :: List.replicate 657 .generator, false⟩

/-- **Message 185: it carries the claim.** -/
def carrierMessage (ledger : Option OnBytes.Ledger) (spent : Bool) : OrcSh :=
  ⟨{ code := 0, mainRows := 2, mainDeg := 3, maskRows := 0, maskCode := 0, answers := 1 }, true, 1,
    [(.main, 8388607)], [25], ledger, spent⟩

/-- **Message 186: the first fold's fresh mask.** -/
def maskMessage (rows : ℕ) (pad : List (OnBytes.Part × ℕ)) (groups : List ℕ)
    (ledger : Option OnBytes.Ledger) : OrcSh :=
  ⟨{ code := 4294967295, mainRows := 0, mainDeg := 1, maskRows := 1, maskCode := 0, answers := 0 },
    false, rows, pad, groups, ledger, false⟩

/-- **Tree 76: the two messages' tree.** -/
def closingTree (source : SrcSh) : TreeSh :=
  ⟨{ logN := 23, logNzk := 17, mainSymbols := #[6, 0], maskSymbols := #[0, 3] }, 76, source,
    [185, 186], true, 0⟩

/-- **The first test says yes**, whatever stands in front. -/
theorem closingShape_passes_five (frontMessages : ℕ → OrcSh) (frontGroups : ℕ → GrpSh) (frontTrees : ℕ → TreeSh)
    (frontPlaces : ℕ → ℕ × ℕ) (carrierLedger maskLedger : Option OnBytes.Ledger) (carrierSpent : Bool)
    (maskRows : ℕ) (maskPad : List (OnBytes.Part × ℕ)) (maskGroups : List ℕ) (source : SrcSh) :
    frontFiveB piLFull codesFull
      ⟨(localCore codesFull frontMessages frontGroups frontTrees frontPlaces 25 185 76 77
        closingGroup (carrierMessage carrierLedger carrierSpent)
        (maskMessage maskRows maskPad maskGroups maskLedger) (closingTree source)), 25, .nothing, some 186⟩ = true := by
  kernel_rfl

/-- **The second test says yes at the written finish's sending**, whatever stands in front. `any`: so
the line also says that a written finish is there. -/
theorem closingShape_passes_plain (frontMessages : ℕ → OrcSh) (frontGroups : ℕ → GrpSh) (frontTrees : ℕ → TreeSh)
    (frontPlaces : ℕ → ℕ × ℕ) (carrierLedger maskLedger : Option OnBytes.Ledger) (carrierSpent : Bool)
    (maskRows : ℕ) (maskPad : List (OnBytes.Part × ℕ)) (maskGroups : List ℕ) (source : SrcSh) :
    (finishW.any fun p => frontPlainB piLFull (K2.sendingPar p.sizes.codes (sentL p))
      ⟨(localCore codesFull frontMessages frontGroups frontTrees frontPlaces 25 185 76 77
        closingGroup (carrierMessage carrierLedger carrierSpent)
        (maskMessage maskRows maskPad maskGroups maskLedger) (closingTree source)), 25, .nothing, some 186⟩) = true := by
  kernel_rfl

/-- **Controls: the first test can say no.** -/
theorem closingShape_controls (frontMessages : ℕ → OrcSh) (frontGroups : ℕ → GrpSh) (frontTrees : ℕ → TreeSh)
    (frontPlaces : ℕ → ℕ × ℕ) (carrierLedger maskLedger : Option OnBytes.Ledger) (carrierSpent : Bool)
    (maskRows : ℕ) (maskPad : List (OnBytes.Part × ℕ)) (maskGroups : List ℕ) (source : SrcSh) :
    frontFiveB piLFull codesFull
      ⟨(localCore codesFull frontMessages frontGroups frontTrees frontPlaces 25 185 76 77
        { closingGroup with kept := [true] } (carrierMessage carrierLedger carrierSpent)
        (maskMessage maskRows maskPad maskGroups maskLedger) (closingTree source)), 25, .nothing, some 186⟩ = false ∧
    frontFiveB piLFull codesFull
      ⟨(localCore codesFull frontMessages frontGroups frontTrees frontPlaces 25 185 76 77
        { closingGroup with kinds := .plain :: List.replicate 656 .generator } (carrierMessage carrierLedger carrierSpent)
        (maskMessage maskRows maskPad maskGroups maskLedger) (closingTree source)), 25, .nothing, some 186⟩ = false ∧
    frontFiveB piLFull codesFull
      ⟨(localCore codesFull frontMessages frontGroups frontTrees frontPlaces 25 185 76 77
        closingGroup (carrierMessage carrierLedger carrierSpent)
        (maskMessage maskRows maskPad maskGroups maskLedger) { closingTree source with parts := [185, 186, 184] }), 25, .nothing, some 186⟩ = false ∧
    frontFiveB piLFull codesFull
      ⟨(localCore codesFull frontMessages frontGroups frontTrees frontPlaces 25 185 76 77
        closingGroup { carrierMessage carrierLedger carrierSpent with groups := [24] }
        (maskMessage maskRows maskPad maskGroups maskLedger) (closingTree source)), 25, .nothing, some 186⟩ = false ∧
    frontFiveB piLFull codesFull
      ⟨(localCore codesFull frontMessages frontGroups frontTrees frontPlaces 25 185 76 76
        closingGroup (carrierMessage carrierLedger carrierSpent)
        (maskMessage maskRows maskPad maskGroups maskLedger) (closingTree source)), 25, .nothing, some 186⟩ = false ∧
    frontFiveB piLFull codesFull
      ⟨(localCore codesFull frontMessages frontGroups frontTrees frontPlaces 25 185 76 77
        closingGroup (carrierMessage carrierLedger carrierSpent)
        { maskMessage maskRows maskPad maskGroups maskLedger with spent := true } (closingTree source)), 25, .nothing, some 186⟩ = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.closingGroup
#print axioms ProofFile.Honest.K12.LotL.carrierMessage
#print axioms ProofFile.Honest.K12.LotL.maskMessage
#print axioms ProofFile.Honest.K12.LotL.closingTree
#print axioms ProofFile.Honest.K12.LotL.closingShape_passes_five
#print axioms ProofFile.Honest.K12.LotL.closingShape_passes_plain
#print axioms ProofFile.Honest.K12.LotL.closingShape_controls
