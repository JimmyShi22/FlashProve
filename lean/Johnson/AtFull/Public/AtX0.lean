-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/AtX0.lean: WHAT THE STEPS BEHIND THE PUBLIC PART ASK OF IT, AT THE VERY VALUE
THAT ITS MAKER RETURNS AT THE STORED FULL-SIZE FILES. One statement, under the join's one premise.

  `opens_yFull`: OpensAt yFull: open_pubC (Johnson/AtFull/Public/Kit.lean), to the letter.
  **`publicOfO_zFull_facts`** (hsz : the stored layout file has 224975 bytes): there is an X₀ with
    publicOfO, at the second hash function, returning X₀ at VerifierAndGoals.storedPublicFiles, and of that X₀:
      twelve layers' plans · twelve attention's plans ·
      hV: the 25 links' views are the written ones (the premise of links_return,
        Johnson/AtFull/Made/LinksReturn.lean) ·
      armsB X₀ = true (Johnson/LPFE1R/RowsAtArms.lean: armOf X₀ at the numbers 0 to 25 is the
        written list armsW: the 25 links' arms, and none at 25) ·
      PubFull X₀ (Johnson/Desc/K12/Law/Sizes/: a public part as at the full size; it falls from
        the return, in scope) · X₀.P is the scan's written value ·
      the views of the 24 smallness tests that are not the head's are xShapeFull's segments 0 to
        23 (Johnson/G/XShapeLit.lean).
How. The join's conclusion (publicOfO_zFull_of_rest, Johnson/AtFull/Public/Join.lean) names X₀'s
parts by letters with their makers' equations; at_witnesses
(Johnson/AtFull/Public/AtWitnesses.lean) carries the closed facts views24_W and arms_W to these
letters; the head's parts stand at HW (Johnson/AtFull/Public/HeadAt.lean).

Limits. UNDER hsz, WHICH IS NOT PAID HERE: until it is, this is no return of publicOfO. The full
size, at the stored free numbers, at the second hash function. Not an example of the top theorem's
head: one step on one of the roads toward it. `VerifierAndGoals.storedPublicFiles` is three terms written in
Ladder/Stored.lean: no Lean code ties them to the top-level folder examples/; the example's weights
are synthetic. Nothing on soundness.

-/
import Johnson.AtFull.Public.Join
import Johnson.AtFull.Public.ArmsAtMakers
import Johnson.AtFull.Public.HeadAt
import Johnson.Desc.K12.Law.Sizes.PublicOAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Public

open OnBytes OnBytes.Model OnBytes.Model.Verify
open Johnson.AtFull.Made.Decl (viewL viewsFull)
open OnBytes.Road.K4.Trial.Values (yFull polLayout_W)
open OnBytes.Model.Layer (ropeTable)
open VerifiableInference.PlanWritten (publicOfO tailView)
open VerifiableInference.Desc.Kinds.Head.Law (Cond.hFull)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (shape_at_stored)

theorem opens_yFull : OpensAt yFull := fun _ h => _root_.AtFull.Public.open_pubC h

/-- **The public part's value at the stored full-size files, with what the steps behind ask of
it.** -/
theorem publicOfO_zFull_facts (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) :
    ∃ X₀ : Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      X₀.G.size = 12 ∧ X₀.A.size = 12 ∧
      (OnBytes.TieK.listedOf X₀ default).map viewL = viewsFull ∧
      VerifiableInference.Desc.LinkJoin.armsB X₀ = true ∧
      H2K.Sizes.PubFull X₀ ∧
      X₀.P = VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef VerifierAndGoals.storedLines ∧
      (∀ g, g < 12 → ∃ hp, X₀.G[g]? = some hp ∧
        some (tailView hp.tl) = Johnson.G.xShapeFull.1.getD (2 * g) none) ∧
      ∀ g, g < 12 → ∃ a, X₀.A[g]? = some a ∧
        some (tailView a.seam.tl) = Johnson.G.xShapeFull.1.getD (2 * g + 1) none := by
  obtain ⟨sc, wsLay, HLy, l, ps, layers, G, seenA, owner, e1, e2, ⟨-, hR, -⟩, e4, ⟨e5, -⟩, e6, e7,
    e8, ⟨a12, -⟩, -, hX⟩ := _root_.AtFull.Public.publicOfO_zFull_of_rest hsz
  obtain ⟨pp, hF, -⟩ := VerifierAndGoals.filesRead.full.2
  obtain ⟨-, -, -, p10, -⟩ := Johnson.Unfolds.ledger_tables VerifierAndGoals.inScope_full hF polLayout_W
  have M : Makers yFull sc wsLay (ropeTable 12 500000 128 10) l ps layers G seenA :=
    { groups := _root_.AtFull.Public.yFull_NGr, p3 := _root_.AtFull.Public.yFull_p3,
      p4 := _root_.AtFull.Public.yFull_p4, scales := e1, weights := e2, rotary := p10, lines := e4,
      twins := e5, record := e6, plans := e7, owners := e8 }
  have ey : layers.y = yFull := OnBytes.Road.Hd.pubOf_y e6
  refine ⟨_, hX, ?_, a12, ?_, ?_, H2K.Sizes.publicO_at_scope VerifierAndGoals.inScope_full hX, rfl,
    (tails_at opens_yFull M arms_W).1, (tails_at opens_yFull M arms_W).2⟩
  · have h := at_witnesses opens_yFull M arms_W
    rw [Bool.and_eq_true] at h
    exact (layers_of_B h.1).1
  · refine hV_at opens_yFull M ?_ ?_ rfl rfl (hHV_at ?_ rfl)
    · show layers.y.NGr = 12
      rw [ey]
      exact _root_.AtFull.Public.yFull_NGr
    · show layers.y.h.p4 = true
      rw [ey]
      exact _root_.AtFull.Public.yFull_p4
    · show layers.y.NGr = 12
      rw [ey]
      exact _root_.AtFull.Public.yFull_NGr
  · refine armsB_at opens_yFull M arms_W ?_ ?_ rfl rfl rfl (hHA_at rfl ?_ hR)
    · show layers.y.NGr = 12
      rw [ey]
      exact _root_.AtFull.Public.yFull_NGr
    · show layers.y.h.p4 = true
      rw [ey]
      exact _root_.AtFull.Public.yFull_p4
    · show headShape (VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef VerifierAndGoals.storedLines) yFull =
        Cond.hFull
      rw [shape_at_stored, _root_.AtFull.Public.yFull_lPd]
      rfl

end Johnson.AtFull.Public

#print axioms Johnson.AtFull.Public.opens_yFull
#print axioms Johnson.AtFull.Public.publicOfO_zFull_facts
