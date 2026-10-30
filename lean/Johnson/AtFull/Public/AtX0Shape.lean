-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/AtX0Shape.lean: publicOfO_zFull_all (Johnson/AtFull/Public/AtX0All.lean) WITH
THREE FACTS MORE OF THE SAME X₀. One statement, under the join's one premise. AtX0.lean and
AtX0All.lean do not turn.

  **`publicOfO_zFull_more`** (hsz : the stored layout file has 224975 bytes): there is an X₀ with
    publicOfO, at the second hash function, returning X₀ at VerifierAndGoals.storedPublicFiles, and of that X₀:
      AtX0All's six (twelve layers' plans · twelve attention's plans · hV · armsB · PubFull · the
        range checks) ·
      xShapeOf X₀ = xShapeFull (m4_at, Johnson/AtFull/Public/XShapeAt.lean) ·
      at each g below 12 and each plan hp at g in X₀.G: numsOf X₀.layers hp = numsW g (k4Nums_at,
        Johnson/AtFull/Public/K4NumsAtMakers.lean) ·
      each member of X₀.A has 10248 columns in all in its smallness test (seam_columns_of_arms,
        Johnson/AtFull/Public/SeamColumns.lean).
How. As AtX0All.lean: the facts and the join's conclusion come with the maker's equation at the same
files: a maker is a function: so the two values are one.

Limits. UNDER hsz, WHICH IS NOT PAID HERE. As AtX0.lean's. Nothing on soundness.

-/
import Johnson.AtFull.Public.AtX0All
import Johnson.AtFull.Public.XShapeAt
import Johnson.AtFull.Public.K4NumsAtMakers
import Johnson.AtFull.Public.SeamColumns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Public

open OnBytes OnBytes.Model OnBytes.Model.Verify
open Johnson.AtFull.Made.Decl (viewL viewsFull)
open Johnson.AtFull.Made (checksFull)
open Johnson.AtFull.Rounds (numsOf numsW)
open OnBytes.Road.K4.Trial.Values (yFull polLayout_W)
open OnBytes.Model.Layer (ropeTable)
open VerifiableInference.PlanWritten (publicOfO xShapeOf)

/-- **The public part's value at the stored full-size files, with nine facts of it**, under hsz. -/
theorem publicOfO_zFull_more (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) :
    ∃ X₀ : Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      X₀.G.size = 12 ∧ X₀.A.size = 12 ∧
      (OnBytes.TieK.listedOf X₀ default).map viewL = viewsFull ∧
      VerifiableInference.Desc.LinkJoin.armsB X₀ = true ∧
      H2K.Sizes.PubFull X₀ ∧
      rangeChecksOf X₀ = some checksFull ∧
      xShapeOf X₀ = Johnson.G.xShapeFull ∧
      (∀ g, g < 12 → ∀ hp, X₀.G[g]? = some hp → numsOf X₀.layers hp = numsW g) ∧
      ∀ a ∈ X₀.A, a.seam.tl.foldColumns = 10248 := by
  obtain ⟨X₀, hX, hG, hA, hV, ha, P, hc⟩ := publicOfO_zFull_all hsz
  refine ⟨X₀, hX, hG, hA, hV, ha, P, hc, ?_, ?_, seam_columns_of_arms P.p4 P.groups ha hA⟩
  all_goals
    obtain ⟨sc, wsLay, HLy, l, ps, layers, G, seenA, owner, e1, e2, -, e4, ⟨e5, -⟩, e6, e7, e8, -,
      -, hX'⟩ := _root_.AtFull.Public.publicOfO_zFull_of_rest hsz
    obtain ⟨pp, hF, -⟩ := VerifierAndGoals.filesRead.full.2
    obtain ⟨-, -, -, p10, -⟩ := Johnson.Unfolds.ledger_tables VerifierAndGoals.inScope_full hF polLayout_W
    have M : Makers yFull sc wsLay (ropeTable 12 500000 128 10) l ps layers G seenA :=
      { groups := _root_.AtFull.Public.yFull_NGr, p3 := _root_.AtFull.Public.yFull_p3,
        p4 := _root_.AtFull.Public.yFull_p4, scales := e1, weights := e2, rotary := p10,
        lines := e4, twins := e5, record := e6, plans := e7, owners := e8 }
    have e : X₀ = _ := Except.ok.inj (hX.symm.trans hX')
  · exact m4_at opens_yFull M arms_W P.groups P.p4 (by rw [e]) (by rw [e]) (by rw [e])
  · rw [e]
    exact k4Nums_at opens_yFull M

end Johnson.AtFull.Public

#print axioms Johnson.AtFull.Public.publicOfO_zFull_more
