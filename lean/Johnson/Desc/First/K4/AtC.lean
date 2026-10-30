-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/AtC.lean: K4's BLOCK AT THE CARRIED RECORD, ITS RUNS OF CLAIMS TYPED AT THE
ONE TYPE OF A CLAIM (`VerifiableInference.Desc.Claim`, Johnson/Desc/Claim.lean). CODE ALONE: no
theorem.

K4's two runs "front" and "back" list forms (`verify-on-bytes`'s `Aff`): each says that the form is
0. A link's frame gathers the claims of all its blocks as one list, at one type.
  `claimOf a`: the form a as a claim: no run of entries; the weight of the claim's own number.
  `atClaims b`: the block b with each of its runs' forms so carried over. Name, place, test on the
    plan, rounds, oracles, `before`, `decide` and the runs behind the batching are b's own; the runs
    keep their names and their order.
  `blockAtC p`: K4's block at the carried record (`blockAtS p`, Johnson/Desc/First/K4/AtS.lean) so.

Limits. That a claim so made is added as `verify-on-bytes` adds the form stands in
Johnson/Desc/First/K4/AtCLaws.lean. This file has not run. Nothing on soundness.
-/
import Johnson.Desc.First.K4.AtS
import Johnson.Desc.Claim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)

/-- A form as a claim: the form is 0. -/
def claimOf (a : Aff) : Claim := { form := a }

/-- A block whose runs list forms, at the one type of a claim. -/
def atClaims {T : Type} (b : Block T Aff) : Block T Claim :=
  { name := b.name, place := b.place, planOk := b.planOk, rounds := b.rounds, oracles := b.oracles
    before := b.before, decide := b.decide
    claims := b.claims.map fun x => (x.1, fun n s => (x.2 n s).map fun y => (y.1.map claimOf, y.2))
    after := b.after }

/-- **K4 at the carried record, at the one type of a claim.** -/
def blockAtC (p : Par) : Block S Claim := atClaims (blockAtS p)

end OnBytes.Desc.First.K4
