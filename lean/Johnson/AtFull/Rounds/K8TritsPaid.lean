-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/K8TritsPaid.lean: THE SMALLNESS TEST'S LOT, ITS SECOND ROW: ITS SECOND
HYPOTHESIS `k8TritsB G = true` FROM THE GOALS' SCOPE AND FOUR FACTS ON THE PUBLIC PART: a joining of
four theorems. No soundness is claimed.

Why. `k8_lists_by_place` (Johnson/AtFull/Rounds/K8ByPlace.lean) stands under ht : `k8TritsB G =
true`. `k8TritsB_is` (K8TritsTie.lean) ties that test to the one in Johnson/LPFK9R/TritsOfSums.lean;
`LPFK9.trits_of_sumA` (Johnson/LPFK9R/ColSumLayers.lean) has it from one premise: at every attention
plan of the public part the matrices' columns sum to 10248. `seam_columns_of_arms`
(Johnson/AtFull/Public/SeamColumns.lean) has that sum, as the library's `foldColumns`, from four
facts on the public part; `LPFK9.colSum_fold` (Johnson/LPFK9R/ColSumFold.lean) ties the two sums.
Here the four are called in one term.

Main names.
  `k8TritsB_of_arms`: **in the goals' scope, the files read, `ProofFile.pubPlain` and `ProofFile.blankBy`
    returned: where the public part has profile 4, twelve groups, twelve attention plans, and the
    test `armsB` accepts it: `k8TritsB G = true`.**
  `k8_lists_of_arms`: **and so the row itself**, with the first hypothesis hk beside.

Limits. THE FOUR FACTS ARE PREMISES: SHOWN OF NO PUBLIC PART HERE. They are said to be
conjuncts of what `publicOfO_zFull_all` (Johnson/AtFull/Public/AtX0All.lean) concludes of
the stored full-size files' public part, under a premise of its own on one file's size: not called
here. hk stays a premise. At the second hash function alone. The full size alone; the example's
weights are synthetic. No soundness is claimed.

-/
import Johnson.AtFull.Rounds.K8ByPlace
import Johnson.AtFull.Rounds.K8TritsTie
import Johnson.LPFK9R.ColSumLayers
import Johnson.LPFK9R.ColSumFold
import Johnson.AtFull.Public.SeamColumns

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8L
open OnBytes OnBytes.Model
open Johnson.AtFull.Rounds (listAt)
open ProofFile.Sk.Full (nameW)
open VerifiableInference.Desc.LinkJoin (armsB)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G : ProofFile.Ground}

/-- **The row's second hypothesis, from the scope and four facts on the public part.** -/
theorem k8TritsB_of_arms (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G)
    (h4 : Z.p.X.p4 = true) (hN : Z.p.X.NGr = 12) (ha : armsB Z.p.X = true)
    (hA : Z.p.X.A.size = 12) : k8TritsB G = true :=
  (k8TritsB_is G).trans (LPFK9.trits_of_sumA hS hR hZ hG fun _ a hg =>
    (LPFK9.colSum_fold a.seam.tl).trans
      (Johnson.AtFull.Public.seam_columns_of_arms h4 hN ha hA a (Array.mem_of_getElem? hg)))

/-- **The row, under hk and these.** -/
theorem k8_lists_of_arms (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G)
    (h4 : Z.p.X.p4 = true) (hN : Z.p.X.NGr = 12) (ha : armsB Z.p.X = true)
    (hA : Z.p.X.A.size = 12)
    (hk : G.built.toList.map (fun X => (X.kind, X.name)) = k8KindsW) :
    ∀ b ∈ (ProofFile.P1K8.lot Z).blocks G, b.rounds = listAt (nameW b.place) :=
  k8_lists_by_place hk (k8TritsB_of_arms hS hR hZ hG h4 hN ha hA)

end P1K8L

#print axioms P1K8L.k8TritsB_of_arms
#print axioms P1K8L.k8_lists_of_arms
