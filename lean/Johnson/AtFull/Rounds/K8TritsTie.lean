-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/K8TritsTie.lean: THE SMALLNESS TEST'S LOT, ITS SECOND ROW: A TIE: the
test on the built links' numbers of trits in Johnson/LPFK9R/TritsOfSums.lean is this row's
`k8TritsB`, and so that file's theorem gives the row's second hypothesis, under its own two named
premises. No soundness is claimed.

Why. `k8_lists_by_place` (Johnson/AtFull/Rounds/K8ByPlace.lean) stands under ht : `k8TritsB G =
true`. `LPFK9.trits_of_sums` ends in a test of its own text: `tritsOf` and
`tritsW` are hand copies of `k8TritsOf` and `k8TritsW`, made without importing them. Here the two
texts meet Lean in one file.

Main names.
  `k8TritsB_is`: the two tests are one, by definition.
  `k8TritsB_of_sums`: **in the goals' scope, the files read, `ProofFile.pubPlain` and `ProofFile.blankBy`
    returned: from sL (at every feed-forward plan of the public part the matrices' columns sum to
    24086) and sA (at every attention plan to 10248): `k8TritsB G = true`.**

Limits. sL AND sA ARE PREMISES: EQUATIONS THAT CAN BE FALSE: SHOWN OF NOTHING HERE. At the stored
full-size example an evaluation shows these sums; evaluated, not proved. At the format's second
hash function alone. The full size alone. No soundness is claimed.

-/
import Johnson.AtFull.Rounds.K8
import Johnson.LPFK9R.TritsOfSums

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8L
open OnBytes OnBytes.Model

/-- The two tests are one. -/
theorem k8TritsB_is (G : ProofFile.Ground) :
    k8TritsB G = (G.built.toList.all fun X => LPFK9.tritsOf X == LPFK9.tritsW X.kind) := rfl

/-- **The row's second hypothesis, from the two sums.** -/
theorem k8TritsB_of_sums {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G)
    (sL : ∀ (g : ℕ) (hp : Layer.HPlan2), Z.p.X.G[g]? = some hp → LPFK9.colSum hp.tl = 24086)
    (sA : ∀ (g : ℕ) (a : Attention.Plan), Z.p.X.A[g]? = some a →
      LPFK9.colSum a.seam.tl = 10248) :
    k8TritsB G = true :=
  (k8TritsB_is G).trans (LPFK9.trits_of_sums hS hR hZ hG sL sA)

end P1K8L

#print axioms P1K8L.k8TritsB_is
#print axioms P1K8L.k8TritsB_of_sums
