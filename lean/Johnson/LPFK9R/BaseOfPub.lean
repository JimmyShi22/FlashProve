-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK9R/BaseOfPub.lean: `ProofFile.baseOf` (Johnson/Desc/ProofFile/OnlineDescriptionFromBlockTables.lean) RETURNS AT THE PUBLIC
PART THAT `ProofFile.pubPlain` RETURNS, WITH ITS PLACES AND ITS SHAPE THE WRITTEN ONES: NO OPENING OF THE
DESCRIPTION. One theorem: a call of three.

Why. The road to an example of the head by the kernel wants "baseOf returns" without an
opening (an opening is what that road is to give).

How. baseOf is three steps and a value: the places of the table of steps (`spotsOf Z.cuts`), the
shape of the first chain (`shapeOf Z`), the segments' values for a request of zeros (`blankBy`); it
rejects for nothing else. The first: `spots_written`
(Johnson/AtFull/Desc/SpotsWritten.lean) under hc. The second: `shapeOf_written`
(Johnson/AtFull/Desc/ShapeIsCut.lean) under hc and hk, hk being `subs_written_of_pub`
(SubsWrittenOfPub.lean). The third is the premise q₃.
  `base_of_pub`: **MAIN.**
PREMISES: the scope; the reading of the files; pubPlain's return; hc : the table of steps is the
written one; q₃ : blankBy returns G.
Limits. hc and q₃ are shown of nothing here. At the second hash function alone. No soundness
statement.

-/
import Johnson.LPFK9R.SubsWrittenOfPub
import Johnson.AtFull.Desc.ShapeIsCut
import Johnson.Desc.ProofFile.OnlineDescription

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9

/-- **baseOf RETURNS, WITH THE WRITTEN PLACES AND THE WRITTEN SHAPE.** -/
theorem base_of_pub {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hc : Z.cuts = Johnson.AtFull.Cut.cutWritten)
    (q₃ : ProofFile.blankBy (ProofFile.pureSeat OnBytes.secondHashFunction Z).links Z = some G) :
    ∃ B, ProofFile.baseOf Z (ProofFile.pureSeat OnBytes.secondHashFunction Z) = .ok B ∧
      B.spots = Johnson.AtFull.Desc.spotsWritten ∧ B.shape = Johnson.AtFull.Desc.shapeW ∧
      B.G₀ = G := by
  have q₁ : ProofFile.spotsOf Z.cuts = some Johnson.AtFull.Desc.spotsWritten := by
    rw [hc]
    exact Johnson.AtFull.Desc.spots_written
  have q₂ : ProofFile.shapeOf Z = .ok Johnson.AtFull.Desc.shapeW :=
    Johnson.AtFull.Desc.shapeOf_written hc (subs_written_of_pub hS hR hZ)
  unfold ProofFile.baseOf
  rw [q₁, q₂, q₃]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

end LPFK9

#print axioms LPFK9.base_of_pub
