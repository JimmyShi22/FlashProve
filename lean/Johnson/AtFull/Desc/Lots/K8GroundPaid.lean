-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K8GroundPaid.lean: THE SMALLNESS TEST'S LOT: BOTH ROWS' HYPOTHESES ON THE
GROUND'S NUMBERS FROM THE GOALS' SCOPE AND FIVE FACTS ON THE PUBLIC PART. Two joinings. No soundness
is claimed.

Why. The first row (`k8_row_at`, K8Row.lean) stands under hn : `k8GroundB G = true`, the second
(`k8_lists_by_place`, Johnson/AtFull/Rounds/K8ByPlace.lean) under ht : `k8TritsB G = true`.
`k8TritsB_of_arms` (Johnson/AtFull/Rounds/K8TritsPaid.lean) has ht from the scope and four facts on
the public part; `k8GroundB_of_asks` (K8GroundOf.lean) has hn from ht and one closed test on the
public part. Here the two are joined.

Main names.
  `k8GroundB_of_arms`: **in the goals' scope, the files read, `ProofFile.pubPlain` and `ProofFile.blankBy`
    returned: where the public part has profile 4, twelve groups, twelve attention plans, and the
    tests `armsB` and `k8AsksWB` accept it: `k8GroundB G = true`.**
  `k8_row_of_arms`: **and so the first row**, with its other three hypotheses hc, he, hk beside.

Limits. THE FIVE FACTS ARE PREMISES: SHOWN OF NO PUBLIC PART HERE. hc, he and hk stay premises. At
the second hash function alone. The full size alone; the example's weights are synthetic. No
soundness is claimed.

-/
import Johnson.AtFull.Desc.Lots.K8GroundOf
import Johnson.AtFull.Rounds.K8TritsPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8L
open OnBytes OnBytes.Model
open Johnson.AtFull.K4Sent (esWritten)
open Johnson.AtFull.Cut (cutWritten)
open ProofFile.Sk (skel)
open VerifiableInference.Desc.LinkJoin (armsB)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G : ProofFile.Ground}

/-- **The first row's fourth hypothesis, from the scope and five facts on the public part.** -/
theorem k8GroundB_of_arms (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G)
    (h4 : Z.p.X.p4 = true) (hN : Z.p.X.NGr = 12) (ha : armsB Z.p.X = true)
    (hA : Z.p.X.A.size = 12) (hw : k8AsksWB Z.p.X = true) : k8GroundB G = true :=
  k8GroundB_of_asks hS hR hZ hG (k8TritsB_of_arms hS hR hZ hG h4 hN ha hA) hw

/-- **The first row, under hc, he, hk and these.** -/
theorem k8_row_of_arms (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G)
    (h4 : Z.p.X.p4 = true) (hN : Z.p.X.NGr = 12) (ha : armsB Z.p.X = true)
    (hA : Z.p.X.A.size = 12) (hw : k8AsksWB Z.p.X = true)
    (hc : Z.cuts = cutWritten) (he : Z.D.1.map (·.entry) = esWritten)
    (hk : G.built.toList.map (fun X => (X.kind, X.name)) = k8KindsW) :
    ((ProofFile.P1K8.lot Z).blocks G).map skel = k8RowsW :=
  k8_row_at hc he hk (k8GroundB_of_arms hS hR hZ hG h4 hN ha hA hw)

end P1K8L

#print axioms P1K8L.k8GroundB_of_arms
#print axioms P1K8L.k8_row_of_arms
