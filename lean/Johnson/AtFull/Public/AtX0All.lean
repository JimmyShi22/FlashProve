-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/AtX0All.lean: publicOfO_zFull_facts (Johnson/AtFull/Public/AtX0.lean) WITH ONE
FACT MORE OF THE SAME X₀: its range checks are the written list (hc_at,
Johnson/AtFull/Public/ChecksAtMakers.lean). One statement, under the join's one premise.

How. Both the facts and the join's conclusion come with the maker's equation at the same files: a
maker is a function: so the two values are one.

Limits. UNDER hsz, WHICH IS NOT PAID HERE. As AtX0.lean's. `VerifierAndGoals.storedPublicFiles` is three terms written in
Ladder/Stored.lean: no Lean code ties them to the top-level folder examples/; the example's weights
are synthetic. Nothing on soundness.

-/
import Johnson.AtFull.Public.AtX0
import Johnson.AtFull.Public.ChecksAtMakers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Public

open OnBytes OnBytes.Model OnBytes.Model.Verify
open Johnson.AtFull.Made.Decl (viewL viewsFull)
open Johnson.AtFull.Made (checksFull)
open OnBytes.Road.K4.Trial.Values (yFull polLayout_W)
open OnBytes.Model.Layer (ropeTable)
open VerifiableInference.PlanWritten (publicOfO tailView)

/-- **The public part's value at the stored full-size files, with what the steps behind ask of
it, the range checks among it.** -/
theorem publicOfO_zFull_all (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) :
    ∃ X₀ : Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      X₀.G.size = 12 ∧ X₀.A.size = 12 ∧
      (OnBytes.TieK.listedOf X₀ default).map viewL = viewsFull ∧
      VerifiableInference.Desc.LinkJoin.armsB X₀ = true ∧
      H2K.Sizes.PubFull X₀ ∧
      rangeChecksOf X₀ = some checksFull := by
  obtain ⟨X₀, hX, hG, hA, hV, ha, P, -, -, -⟩ := publicOfO_zFull_facts hsz
  refine ⟨X₀, hX, hG, hA, hV, ha, P, ?_⟩
  obtain ⟨sc, wsLay, HLy, l, ps, layers, G, seenA, owner, e1, e2, -, e4, ⟨e5, -⟩, e6, e7, e8, -, -,
    hX'⟩ := _root_.AtFull.Public.publicOfO_zFull_of_rest hsz
  obtain ⟨pp, hF, -⟩ := VerifierAndGoals.filesRead.full.2
  obtain ⟨-, -, -, p10, -⟩ := Johnson.Unfolds.ledger_tables VerifierAndGoals.inScope_full hF polLayout_W
  have M : Makers yFull sc wsLay (ropeTable 12 500000 128 10) l ps layers G seenA :=
    { groups := _root_.AtFull.Public.yFull_NGr, p3 := _root_.AtFull.Public.yFull_p3,
      p4 := _root_.AtFull.Public.yFull_p4, scales := e1, weights := e2, rotary := p10, lines := e4,
      twins := e5, record := e6, plans := e7, owners := e8 }
  have e : X₀ = _ := Except.ok.inj (hX.symm.trans hX')
  exact hc_at opens_yFull M P.groups P.p4 (by rw [e]) (by rw [e]) (by rw [e])

end Johnson.AtFull.Public

#print axioms Johnson.AtFull.Public.publicOfO_zFull_all
