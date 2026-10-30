-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/MadeAtJoinC.lean: `Key.madeAt` returns, from the arms' test.

What it says.
  `first_of_arms`   e₁: the proof file's first plan returns the written one, from `armsB X = true`
                    (`proof_first_written`, Johnson/AtFull/Made/ProofFirstWritten.lean).
  `madeAt_of_arms`  `madeAt_of_rest` (Johnson/AtFull/Made/MadeAtJoinB.lean) at the written range
                    checks, with e₁ so paid and the 25 links' scalars paid from the same Bool
                    (`scalars_of_arms`,
                    Johnson/AtFull/Made/ShapesReadOfArms.lean). Nine binders are left: X is as at
                    the full size (P) · hG · hA · hV · b₁ · the digest has 32 bytes ·
                    ha : armsB X = true · hc : rangeChecksOf X = some checksFull · s₁.

Limits. A joining: it pays none of its hypotheses. THAT ANY PUBLIC FILES MEET THEM IS SHOWN NOWHERE
HERE. Nothing on soundness.
-/
import Johnson.AtFull.Made.MadeAtJoinB
import Johnson.AtFull.Made.ShapesReadOfArms
import Johnson.AtFull.Made.ProofFirstWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages OnBytes.Params
open VerifiableInference.PlanWritten (proofSizedFull FirstWritten MadeWritten)
open VerifiableInference.Number.ByRuns (proofThree)
open Johnson.AtFull.LayoutRead (LW)
open H2K.Sizes (PubFull)
open VerifiableInference.Desc.LinkJoin (armsB)

/-- **e₁ from the arms' test.** -/
theorem first_of_arms {X : Public} {rc : List RangeCheck} (P : PubFull X)
    (hc : rangeChecksOf X = some rc) (ha : armsB X = true) :
    firstPlan proofSizedFull (subproofsWith X reqLinksW) = .ok proofThree.A.plan := by
  obtain ⟨Y, sh, hY, hs⟩ := Lk6.AtPlan.shape_returns
  obtain rfl : Y = X.layers.wsLay := Except.ok.inj (hY.symm.trans P.wsLay)
  have b₂ : Plan.reqFrame declaredFull LW X.P.frame.answers =
      some (reqLinksW, Johnson.G.layoutFull) := reqFrame_of_pub P moments_seam rfl
  rw [P.frame] at b₂
  obtain ⟨-, e2⟩ := links_of_frame
    (show Plan.reqFrame declaredFull LW 1 = some (reqLinksW, Johnson.G.layoutFull) from b₂)
    declared_size Johnson.AtFull.LayoutRead.groups_are
  have hx := shapesWith_of (links := reqLinksW) (layout := Johnson.G.layoutFull) (ids := idsFull) hc
    (by rw [e2, P.p4, P.groups]; rfl) (ws_parts P.wsLay).1 hs
  have h := proof_first_written hx ha
  exact h

/-- **`Key.madeAt` returns, from the arms' test.** -/
theorem madeAt_of_arms {X : Public} {lay cfg : ByteArray}
    {k0 k1 k2 p0 p1 p2 : Johnson.G.ChainSends} (P : PubFull X)
    (hG : X.G.size = 12) (hA : X.A.size = 12)
    (hV : (OnBytes.TieK.listedOf X default).map Decl.viewL = Decl.viewsFull)
    (b₁ : Plan.layoutRead lay = some LW) (h32 : cfg.size = 32) (ha : armsB X = true)
    (hc : rangeChecksOf X = some checksFull)
    (s₁ : ∀ x, ∃ en, Johnson.G.sendsFrom (madeW x cfg) = .ok [k0, k1, k2, en, p0, p1, p2]) :
    ∃ (links₀ links : Array LinkH) (sh : Plan.Shape),
      VerifiableInference.Desc.Key.madeAt X lay cfg =
        .ok ⟨{ X := X, cfg := cfg, chains := chainsAt (xOf X sh checksFull) cfg,
               built := { links := links } }, (k0, k1, k2), (p0, p1, p2)⟩ ∧
      linksOf X default = .ok links₀ ∧
      declareLinks links₀ X.NGr X.p4 = .ok (links, declaredFull) ∧
      links.toList.map viewOf = viewFull ∧
      Plan.shapeOfLayout X.layers.wsLay X.layers.wsLay.lk = some sh ∧
      shapesOf X (some lay) = .ok (links, xOf X sh checksFull) ∧
      FirstWritten (chainsAt (xOf X sh checksFull) cfg).proof.first ∧
      MadeWritten (chainsAt (xOf X sh checksFull) cfg).made :=
  madeAt_of_rest P hG hA hV b₁ hc rfl h32 (first_of_arms P hc ha) (scalars_of_arms ha reqLinksW) s₁

#print axioms Johnson.AtFull.Made.first_of_arms
#print axioms Johnson.AtFull.Made.madeAt_of_arms

end Johnson.AtFull.Made
