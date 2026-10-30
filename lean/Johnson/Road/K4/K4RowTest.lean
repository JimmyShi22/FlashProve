-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4RowTest.lean: A ROW FOR THE PROOF FILE's ENTRY TESTS,
ASKED BY NO LIST: the two tests on the plan of K4's sub-protocol that no law and
no written value closes, in one Bool on the public part. DEFINITIONS ALONE: two. The laws:
Johnson/Road/K4/K4RowTestLaws.lean. The tools of its negative tests:
Johnson/Road/K4/K4RowTestBends.lean: not imported here.

  `k4RowAt X lin`: there is a group of layers (0 < X.NGr), and at each group g below X.NGr: X.G has
    an entry hp at g; AT THE GROUPS 0 AND 1 the listing of K4's forms returns at the plan's value at
    zeros (frontB, Johnson/Road/K4/Total/PlanMemberDefs.lean); AT EVERY GROUP the light test on the
    pending row accepts with hp.NCL claims (rowLightB, Johnson/Road/K4/PendLightDefs.lean:
    arithmetic on the committed table's layout's units). NO GROUP AT ALL REJECTS. A GROUP WITHOUT AN
    ENTRY REJECTS.
  `k4RowB Z`: THE ROW: k4RowAt at the public part's own public parameters and at the first chain's
  shape of the test on the committed table. BARE: no guard on the key; it compares with no written
  value: it can be asked at every size.
(1) The row asks rowLightB, not rowB, which runs wsPending (OnBytes/Model/Pending.lean,
a routine of the program `verify-on-bytes`, over a vector of up to the committed table's rows):
they are THE SAME BOOL AT EVERY PLAN, by a law (rowLight_eq, Johnson/Road/K4/PendLightBack.lean);
rowLightB runs no routine of that program and walks no array. (2) frontB is asked at two groups:
WHERE THE PUBLIC PARAMETERS ARE WHAT publicOf RETURNS, it is one Bool at any two groups other than 0
that have an entry, by a law (frontB_later_public, Johnson/Road/K4/FrontLater.lean).
THE WORDS UNDER WHICH IT REJECTS: "at some group of layers, what is computed from the parameter
file has no entry for the group, or the layers' sub-protocol cannot list its claims from it, or
its row on the committed table cannot be formed from it with the stated number of claims; or there
is no group of layers at all".
Limits. It reads values made of the three public files alone: nothing that a prover sends. What the
row costs to run is not said here. Nothing on soundness.


-/
import Johnson.Road.K4.Total.PlanMemberDefs
import Johnson.Road.K4.PendLightDefs
import Johnson.Desc.ProofFile.Pub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Total (frontB)

/-- There is a group of layers; the listing returns at the groups 0 and 1; the light test accepts at
every group. -/
def k4RowAt (X : Verify.Public) (lin : Params.LinShape) : Bool :=
  decide (0 < X.NGr) && (List.range X.NGr).all fun g => (X.G[g]?).any fun hp =>
    (decide (2 ≤ g) || frontB false X.layers hp g X.layers.y.fo) &&
      Pend.rowLightB X.layers g hp.NCL lin

/-- **The row.** -/
def k4RowB (Z : ProofFile.Pub) : Bool := k4RowAt Z.p.X Z.first.lin

end OnBytes.Road.K4
