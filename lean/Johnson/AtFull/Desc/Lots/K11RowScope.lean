-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K11RowScope.lean: THE ROW OF THE MERGE's LOT
(Johnson/AtFull/Desc/Lots/K11Row.lean) WITH THREE OF ITS FIVE HYPOTHESES PAID IN THE GOALS' SCOPE:
the three numbers of the segments' records. Two theorems: calls.

What it says.
  `k11_lot_row_scope`: for public files in the goals' scope (hS, hR), where the plain road's public
    part Z is made at the second hash function (hZ) and the blank records G₀ are made (hG): if Z's
    table of steps and entries are as written (hc, he), `((K11.lot Z).blocks G₀).map skel = rowW`.
    `k11_lotSk_scope`: the same as a lot's skeleton.
  PAID: hb (25 segments are built): `IM.ground_gets` (Johnson/IMR/PureJoin.lean) · hk (the committed
    table has 18 column bits): `m0lk_in_scope`
    (Johnson/Desc/Sound/K11Tests/NumsHeadInScope.lean) · hn (the plan has one claim on that table):
    `public_H_ncl` (NclHeadInScope.lean): both at `IM.ground_publicK`: the records' public
    parameters are `publicOf`'s.

Limits. hc AND he STAY PREMISES, and so do hS, hR, hZ and hG: that any public files meet them is
shown nowhere here. No law at an opening and none under the proof file's pins is spent. At the
second hash function `OnBytes.secondHashFunction` alone. The limits of K11Row.lean hold here too.
Nothing on soundness.
-/
import Johnson.AtFull.Desc.Lots.K11Row
import Johnson.IMR.PureJoin
import Johnson.Desc.Sound.K11Tests.NumsHeadInScope
import Johnson.Desc.Sound.K11Tests.NclHeadInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K11Row

open Johnson.AtFull.K4Sent (esWritten)
open Johnson.AtFull.Cut (cutWritten)
open ProofFile.Sk (skel lotSk)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- **THE ROW, with the three numbers of the segments' records paid in the goals' scope.** -/
theorem k11_lot_row_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (hc : Z.cuts = cutWritten)
    (he : Z.D.1.map (·.entry) = esWritten) :
    ((K11.lot Z).blocks G₀).map skel = rowW :=
  k11_lot_row hc he (IM.ground_gets hS hR hZ hG).1
    (LT28.K11Tests.m0lk_in_scope hS (IM.ground_publicK hZ hG)).2
    (LT28.K11Tests.public_H_ncl (IM.ground_publicK hZ hG))

/-- The same, as a lot's skeleton. -/
theorem k11_lotSk_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (hc : Z.cuts = cutWritten)
    (he : Z.D.1.map (·.entry) = esWritten) :
    lotSk G₀ (K11.lot Z) =
      { name := "the merge of the weights' claims", letters := false, still := [], blocks := rowW
        batch := fun _ => none, each := fun _ => false, tests := fun _ => false } :=
  k11_lotSk hc he (IM.ground_gets hS hR hZ hG).1
    (LT28.K11Tests.m0lk_in_scope hS (IM.ground_publicK hZ hG)).2
    (LT28.K11Tests.public_H_ncl (IM.ground_publicK hZ hG))

end Johnson.AtFull.Lots.K11Row

#print axioms Johnson.AtFull.Lots.K11Row.k11_lot_row_scope
#print axioms Johnson.AtFull.Lots.K11Row.k11_lotSk_scope
