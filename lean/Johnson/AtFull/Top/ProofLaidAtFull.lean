-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Top/ProofLaidAtFull.lean: two facts on the public part's value X₀ at `VerifierAndGoals.storedPublicFiles`,
from the layout file's size: its arms pass their test, and its shape part is the written one.

Main names.
* `x_facts_zFull`: under hsz there is X₀ that `publicOfO` returns at `VerifierAndGoals.storedPublicFiles`, with `armsB X₀
  = true` and `xShapeOf X₀ = xShapeFull`. Calls of `publicOfO_zFull_facts`
  (Johnson/AtFull/Public/AtX0.lean) and `m4_at` (Johnson/AtFull/Public/XShapeAt.lean), at the
  letters of Johnson/AtFull/Public/Join.lean.
* `x_facts_at`: the same at whatever value `publicOfO` returns there: a maker is a function.
They pay two premises of `proofLaid_of_desc` (Johnson/AtFull/Top/ProofLaidOfDesc.lean) in
Johnson/AtFull/Top/ProofLaidWhole.lean.

What hsz is. A closed fact on a stored text: the stored public layout file has 224,975 bytes. It is
a premise here. Lean's kernel has borne it in the side library alone
(`Johnson.Unfolds.Layout.lay_size`, AtFullSide/Layout/Size.lean, behind a tie that wants a larger
thread stack), outside the library's audit.

A second text. The proof of `x_facts_zFull` opens the conclusion of Johnson/AtFull/Public/Join.lean
as the proof in Johnson/AtFull/Public/AtX0.lean does. It would fall to one call if that file's list
of facts held the shape part.

Limits. Calls. No return of `theProofLaid` is shown in this file. The full size, at the stored free
numbers alone; at the second hash function. That the premises of `proofLaid_of_desc` can be met
together is shown at storedPublicFiles alone: `proofLaid_zFull` (Johnson/AtFull/Top/LiveAtZFull.lean), under two
closed facts on the layout file whose proofs lie in the side library. No example of the head is
shown in this file; two, at storedPublicFiles and at zGap alone, are AtFullSide.Top.headMember_zFull and
headMember_zGap, whose own Limits say what they are worth. No soundness is claimed.

-/
import Johnson.AtFull.Top.ProofLaidOfMade
import Johnson.AtFull.Public.AtX0
import Johnson.AtFull.Public.XShapeAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Top
open ProofFile
open VerifiableInference VerifiableInference.PlanWritten
open Johnson.G Johnson.G.OfPlan VerifiableInference.Number
open OnBytes.Road.K4.Trial.Values (yFull polLayout_W)
open OnBytes.Model.Layer (ropeTable)
open Johnson.AtFull.Public (Makers opens_yFull arms_W m4_at publicOfO_zFull_facts)

/-- **From the layout file's size**: the public part's value at the stored full-size files, its arms
and its shape part. -/
theorem x_facts_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) :
    ∃ X₀ : OnBytes.Model.Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      VerifiableInference.Desc.LinkJoin.armsB X₀ = true ∧ xShapeOf X₀ = xShapeFull := by
  obtain ⟨sc, wsLay, HLy, l, ps, layers, G, seenA, owner, e1, e2, -, e4, ⟨e5, -⟩, e6, e7, e8, -, -,
    hX⟩ := _root_.AtFull.Public.publicOfO_zFull_of_rest hsz
  obtain ⟨pp, hF, -⟩ := VerifierAndGoals.filesRead.full.2
  obtain ⟨-, -, -, p10, -⟩ := Johnson.Unfolds.ledger_tables VerifierAndGoals.inScope_full hF polLayout_W
  have M : Makers yFull sc wsLay (ropeTable 12 500000 128 10) l ps layers G seenA :=
    { groups := _root_.AtFull.Public.yFull_NGr, p3 := _root_.AtFull.Public.yFull_p3,
      p4 := _root_.AtFull.Public.yFull_p4, scales := e1, weights := e2, rotary := p10, lines := e4,
      twins := e5, record := e6, plans := e7, owners := e8 }
  have ey : layers.y = yFull := OnBytes.Road.Hd.pubOf_y e6
  obtain ⟨X₁, hX₁, -, -, -, ha, -⟩ := publicOfO_zFull_facts hsz
  obtain rfl := Except.ok.inj (hX₁.symm.trans hX)
  refine ⟨_, hX, ha, m4_at opens_yFull M arms_W ?_ ?_ rfl rfl rfl⟩
  · show layers.y.NGr = 12
    rw [ey]
    exact _root_.AtFull.Public.yFull_NGr
  · show layers.y.h.p4 = true
    rw [ey]
    exact _root_.AtFull.Public.yFull_p4

/-- The same at whatever letter publicOfO returns there. -/
theorem x_facts_at (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : OnBytes.Model.Verify.Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) :
    VerifiableInference.Desc.LinkJoin.armsB X₀ = true ∧ xShapeOf X₀ = xShapeFull := by
  obtain ⟨X₁, hX₁, ha, m₄⟩ := x_facts_zFull hsz
  obtain rfl := Except.ok.inj (hX₁.symm.trans hX)
  exact ⟨ha, m₄⟩

end AtFull.Top

#print axioms AtFull.Top.x_facts_zFull
#print axioms AtFull.Top.x_facts_at
