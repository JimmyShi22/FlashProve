-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK9R/BaseOfPubWhole.lean: `ProofFile.baseOf` RETURNS AT THE PUBLIC PART THAT `ProofFile.pubPlain`
RETURNS, WITH THE WRITTEN PLACES AND THE WRITTEN SHAPE, AND ITS THIRD FIELD IS WHAT `ProofFile.blankBy`
RETURNS: THE SECOND FORM OF BaseOfPub.lean: THE PREMISE q₃ IS GONE. No opening of the description.
Two theorems: calls.

  `blank_of_pub`: **the segments' values for a request of zeros are there: ∃ G, blankBy
    pureRoad.links Z = some G: from the scope, the reading of the files and pubPlain's return
    alone.** It is `blank_returns_pub` (Johnson/AtFull/Desc/BlankReturns.lean) with its
    four premises paid: as many layers' plans, and as many attention plans, as groups
    (`listLinksH_with` at `linksPlain`'s return, as in SubsOfPub.lean); at least one position
    (`T_in_scope`, Johnson/Goal/Meaning/HeadStartScope.lean); a vocabulary that is not empty
    (`V_public`, the same file; `hS_in_scope`, Johnson/Goal/Meaning/HeadShapeScope.lean: a closed
    numeral).
  `base_of_pub_whole`: **MAIN.** The last conjunct says of
    B.G₀ just what an opening's field blank says.
PREMISES: the scope; the reading of the files; pubPlain's return; hc.
Limits. **hc : Z.cuts = cutWritten is an equation with a closed value: it can be false: it is the
premise at which the main theorem could be idle. It is shown of nothing here, and this file names
no proof of it.** Which G it is, is not
said beyond "what blankBy returns". At the second hash function alone. No soundness statement.

-/
import Johnson.LPFK9R.BaseOfPub
import Johnson.AtFull.Desc.BlankReturns
import Johnson.Goal.Meaning.HeadStartScope
import Johnson.Goal.Meaning.HeadShapeScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open OnBytes OnBytes.Model

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}

/-- **q₃ FROM THE SCOPE.** -/
theorem blank_of_pub (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z) :
    ∃ G, ProofFile.blankBy ProofFile.pureRoad.links Z = some G := by
  have hX : Verify.publicOf P.pol P.KL (some lay) = .ok Z.p.X :=
    (VerifiableInference.PlanWritten.publicOfO_older P.pol P.KL (some lay)).symm.trans
      (ProofFile.Law.pub_public hZ)
  obtain ⟨h4, hN, -, -⟩ := Meaning.scope_plans hS hR hX
  obtain ⟨l₀, hl, -⟩ := IM.plain_built (IM.planned_built (ProofFile.Law.pub_planned hZ))
  unfold ProofFile.Plain.linksPlain at hl
  rw [h4] at hl
  obtain ⟨hG, hA, -⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ hl
  rw [Array.size_map] at hG hA
  have hT : 1 ≤ Z.p.X.T := by
    rw [VerifiableInference.Desc.Kinds.Head.Law.InScope.T_in_scope hS hR hX]
    exact Nat.two_pow_pos _
  have hV : 0 < Z.p.X.P.h.V := by
    rw [VerifiableInference.Desc.Kinds.Head.Law.InScope.V_public hX,
      Meaning.HeadS.hS_in_scope hS hR hX]
    exact Nat.le_of_ble_eq_true rfl
  exact Johnson.AtFull.Desc.blank_returns_pub hZ hG (fun _ => hA) hV hT

/-- **baseOf RETURNS: THE WRITTEN PLACES, THE WRITTEN SHAPE, AND WHAT blankBy RETURNS.** -/
theorem base_of_pub_whole (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hc : Z.cuts = Johnson.AtFull.Cut.cutWritten) :
    ∃ B, ProofFile.baseOf Z (ProofFile.pureSeat OnBytes.secondHashFunction Z) = .ok B ∧
      B.spots = Johnson.AtFull.Desc.spotsWritten ∧ B.shape = Johnson.AtFull.Desc.shapeW ∧
      ProofFile.blankBy ProofFile.pureRoad.links Z = some B.G₀ := by
  obtain ⟨G, q₃⟩ := blank_of_pub hS hR hZ
  obtain ⟨B, h1, h2, h3, h4⟩ := base_of_pub hS hR hZ hc q₃
  exact ⟨B, h1, h2, h3, by rw [h4]; exact q₃⟩

end LPFK9

#print axioms LPFK9.blank_of_pub
#print axioms LPFK9.base_of_pub_whole
