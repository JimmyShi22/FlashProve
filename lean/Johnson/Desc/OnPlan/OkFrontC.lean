-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/OnPlan/OkFrontC.lean: the shared chain's front's share of the tests on a planner's
answer (OkD.Share.front2, Johnson/Desc/OnPlan/OkShare.lean), TYPED AT THE CHAINS ALONE; and that it
is that share. Definitions with code, and one law.

IT STANDS OVER NO FILE THAT IMPORTS Mathlib.

Why. OkD.Share.front2 takes the planner's whole answer, the record Model.Verify.Planned. It reads
the field «chains» alone; but that record's field «built» holds the links with their routines, whose
types name the verifier program's monads and its context: so a search over constants from front2
reaches these TYPES, through its argument's type, though it calls no routine. A block's test on the
plan is to reach none of them. The record Model.Verify.Chains holds sizes, plans and parameter bytes
as read back.

Main names (namespace VerifiableInference.OnPublicFiles.OkD.AtC): n3, sizedS, readShape, readCodes,
readSamples, remadeS: the six clauses, each with «c» where the clause has «p.chains». front2 c:
**the share**. front2_eq: OkD.Share.front2 p = AtC.front2 p.chains.

What is not claimed. THAT IT SAYS YES AT ANY c: nothing is evaluated here. Nothing on soundness, on
an honest prover or on hiding.

-/
import Johnson.Desc.OnPlan.OkShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.OkD
open OnBytes

namespace AtC

def n3 (c : Model.Verify.Chains) : Bool :=
  (Proof.tailPublic c.proof Maker.noTable).shared.given.plan.samples == 1

def sizedS (c : Model.Verify.Chains) : Bool :=
  (Params.linSizeOf c.made.sized.proof.codes c.made.sized.proof.batch).isSome

def readShape (c : Model.Verify.Chains) : Bool :=
  decide (c.made.sized.proof.batch.shape = c.proof.shared.lin)

def readCodes (c : Model.Verify.Chains) : Bool :=
  decide (c.made.sized.proof.codes = c.proof.shared.codes)

def readSamples (c : Model.Verify.Chains) : Bool :=
  c.made.sized.proof.set.samples == c.proof.shared.given.plan.samples

def remadeS (c : Model.Verify.Chains) : Bool :=
  let z := c.made.sized.proof
  match Params.sharedPlan z.set z.codes z.batch with
  | .ok P => decide (P.plan.entries = c.proof.shared.given.plan.entries)
  | .error _ => false

/-- **The shared chain as a whole.** -/
def front2 (c : Model.Verify.Chains) : Bool :=
  n3 c && sizedS c && readShape c && readCodes c && readSamples c && remadeS c

end AtC

/-- The share typed at the chains is the share. -/
theorem front2_eq (p : Model.Verify.Planned) : Share.front2 p = AtC.front2 p.chains := rfl

end VerifiableInference.OnPublicFiles.OkD
