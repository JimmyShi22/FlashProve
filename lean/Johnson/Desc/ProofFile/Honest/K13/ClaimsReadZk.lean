-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/ClaimsReadZk.lean: OF WHAT THE LOOKUP IN FRONT HAS SAMPLED THE
LAYERS' ARM OF THE PILE's FILLER's PARAMETER READS ONE FIELD. One lemma.

  `layersClaims_reads_zk`: **two makers of the small input of K4's honest parts (`K4In`,
    Johnson/Desc/K4/Honest/Front.lean) whose tokens agree at ξ, and whose `look` at the challenges
    in front of K4's first round returns structures with the same field zk, give the same
    `layersClaims` at ξ** (ClaimsIsLayers.lean of this folder). By unfolding `mergeClaimsAt`,
    `panelClaims`, `embClaim`, `claimEnvOf` (Merge.lean), `envOf`, `ptsOf` (Front.lean). It sharpens
    `layersClaims_reads` (ClaimsText.lean), which asks that the two `look` be one function.
So a text for `look` that lays zk and leaves other fields of the structure blank serves the claims.

The name zk, here and in the files named, is a field of the lookup's structure: each call's key
point: it does not stand for zero knowledge. What is not claimed. That tokv is read in every group
(it is read in the first alone). Anything on what else reads a `K4In`. Nothing on soundness,
completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.ClaimsIsLayers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes.Desc.First.K4.Honest (K4Pub K4In mergeClaimsAt panelClaims embClaim claimEnvOf envOf
  ptsOf)

/-- **OF `look`'s VALUE THE LAYERS' ARM READS THE FIELD zk ALONE**, at the challenges in front of
K4's first round. -/
theorem layersClaims_reads_zk {Xi : Type} (Q : K4Pub) (wOf wOf' : Xi → K4In) (ξ : Xi)
    (hd : List Fmt.Drawn) (h1 : (wOf ξ).tokv = (wOf' ξ).tokv)
    (h2 : ((wOf ξ).look (hd.take Q.r0)).zk = ((wOf' ξ).look (hd.take Q.r0)).zk) :
    layersClaims Q wOf ξ hd = layersClaims Q wOf' ξ hd := by
  unfold layersClaims mergeClaimsAt panelClaims embClaim claimEnvOf envOf ptsOf
  dsimp only
  rw [h1, h2]

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.layersClaims_reads_zk
