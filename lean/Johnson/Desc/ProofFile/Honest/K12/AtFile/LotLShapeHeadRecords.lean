-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLShapeHeadRecords.lean

It states no goal. No property of the protocol is claimed.

THE RECORDS THAT «finish_lays» LEAVES AS TERMS OF
THE REQUEST's SHAPE AND THE CODES (LotLShapePublicTerms.lean) ARE, AT THE WRITTEN SHAPE AND CODES, THE WRITTEN RECORDS OF
LotLShapeBoolsClosed.lean. Closed lines by Lean's kernel, each with a control; then one law at letters.

  mask_record_written       the fresh mask as it comes in is maskMessage 0 [] [] none
  tree_shape_written        the last switch's sending lays one tree, of closingTree's shape
  tree_shape_control        at the carrier alone, without the mask, the tree's shape is another
  carrier_record_written    the carrier's record at shL is carrierMessage at its ledger, not spent
  closingTree_record        a tree's record at that shape, number 76, parts 185 and 186 is closingTree
  closingGroup_record       the group's record at 657 open rows of the generator's kind is closingGroup
  closingGroupLaid_written  THE LAW: ClosingGroupLaid at the terms, with n = 657 and the sending's one tree shape τ,
                            is ClosingGroupLaid at the four written records

IMPORTS OF Johnson.Top.H0.*: none by name.

Limits. Facts on written values: the full size alone. No state is shown to bear the shape. n = 657 is a premise.
Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLShapePublicTerms
import Johnson.Desc.ReqLit.Full
import Johnson.G.PackLit
import Johnson.Loose.H2K12.PublicAt354
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLShapeBoolsClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.LotL
open OnBytes (TreeShape TreeLay)
open VerifiableInference.Desc (Own.treesMade)
open VerifiableInference.Desc.Ground.Sh (CoreSh GrpSh OrcSh TreeSh SrcSh freshOrc)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (codesFull2)

/-! ## 1 Closed lines -/

/-- **The fresh mask as it comes in is the written mask message**, at no sample row, no pad, no group,
no ledger. -/
theorem mask_record_written :
    freshOrc (maskNoticeOfShape shapeFull) = maskMessage 0 [] [] none := by decide +kernel

/-- **The last switch's sending lays one tree, of the written shape.** -/
theorem tree_shape_written :
    (treesOfFinish shapeFull codesFull2).map (·.shapes) = some #[(closingTree .given).shape] := by
  decide +kernel

/-- Control: of the carrier alone the tree's shape is another. -/
theorem tree_shape_control :
    decide ((Own.treesMade codesFull2
      #[⟨(targetOfShape shapeFull).shape, (targetOfShape shapeFull).leafClass⟩]).map (·.shapes) =
        some #[(closingTree .given).shape]) = false := by
  decide +kernel

/-- Control: the written mask message at one sample row is not what comes in. -/
theorem mask_record_control :
    decide (freshOrc (maskNoticeOfShape shapeFull) = maskMessage 1 [] [] none) = false := by
  decide +kernel

/-! ## 2 The records -/

/-- The carrier's record. -/
theorem carrier_record_written (ledger : Option OnBytes.Ledger) :
    (⟨H2K12.shL, true, 1, [(.main, 8388607)], [25], ledger, false⟩ : OrcSh) =
      carrierMessage ledger false := rfl

/-- The tree's record. -/
theorem closingTree_record (source : SrcSh) :
    (⟨(closingTree .given).shape, 76, source, [185, 186], true, 0⟩ : TreeSh) = closingTree source :=
  rfl

/-- The group's record. -/
theorem closingGroup_record :
    (⟨0, 0, [185], [false], .plain :: List.replicate 657 .generator, false⟩ : GrpSh) =
      closingGroup := rfl

/-- The one shape of the sending's trees is the written one. -/
theorem tree_shape_of_finish {lay : TreeLay} {τ : TreeShape}
    (hlay : treesOfFinish shapeFull codesFull2 = some lay) (hτ : lay.shapes = #[τ]) :
    τ = (closingTree .given).shape := by
  have t := tree_shape_written
  rw [hlay, Option.map_some, hτ] at t
  have e : #[τ] = #[(closingTree .given).shape] := Option.some.inj t
  simpa using e

/-! ## 3 The law -/

/-- **ClosingGroupLaid at the terms is ClosingGroupLaid at the four written records.** c: the shape.
n: how many open rows of the generator's kind. -/
theorem closingGroupLaid_written {c : CoreSh} {n : ℕ} {lay : TreeLay} {τ : TreeShape}
    {source : SrcSh} (hn : n = 657) (hlay : treesOfFinish shapeFull codesFull2 = some lay)
    (hτ : lay.shapes = #[τ])
    (h : ClosingGroupLaid c 25 185 186 76
      ⟨0, 0, [185], [false], .plain :: List.replicate n .generator, false⟩
      ⟨H2K12.shL, true, 1, [(.main, 8388607)], [25],
        OnBytes.Slice.freshLedger codesFull2 H2K12.shL, false⟩
      (freshOrc (maskNoticeOfShape shapeFull)) ⟨τ, 76, source, [185, 186], true, 0⟩) :
    ClosingGroupLaid c 25 185 186 76 closingGroup
      (carrierMessage (OnBytes.Slice.freshLedger codesFull2 H2K12.shL) false)
      (maskMessage 0 [] [] none) (closingTree source) := by
  subst hn
  rw [tree_shape_of_finish hlay hτ, mask_record_written] at h
  exact h

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.mask_record_written
#print axioms ProofFile.Honest.K12.LotL.mask_record_control
#print axioms ProofFile.Honest.K12.LotL.tree_shape_written
#print axioms ProofFile.Honest.K12.LotL.tree_shape_control
#print axioms ProofFile.Honest.K12.LotL.carrier_record_written
#print axioms ProofFile.Honest.K12.LotL.closingTree_record
#print axioms ProofFile.Honest.K12.LotL.closingGroup_record
#print axioms ProofFile.Honest.K12.LotL.tree_shape_of_finish
#print axioms ProofFile.Honest.K12.LotL.closingGroupLaid_written
