-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5OwnScope.lean: CONDITIONAL (THAT THE FRONT RETURNS IS A PREMISE):
THE TWO LIGHT FACTS OF K5's ROW (162 ROUNDS; THE TEST ON
THE PLAN's OWN
NUMBERS SAYS YES) AT EACH OF THE PUBLIC PART's TWELVE ATTENTION PLANS, AT ALL PUBLIC FILES IN THE
GOALS' SCOPE. Joins; nothing is evaluated here.
  `public_of_front`: the public data of the front's return are publicOf's.
  **`h1_in_scope`**, **`h2_in_scope`** (hS) (hR) (hZ : pubPlain secondHashFunction Pb.pol lay Pb.KL = .ok Z) :
    `∀ g, g < 12 → ∀ a, Z.p.X.A[g]? = some a → nRounds a.own = 162` (`planOkOwn a.own = true`): the
    form of the binders h₁, h₂ of `k5_row_own` (K5RowOwn.lean). From `own_in_scope`
    (K5OwnInScope.lean), `rounds_written`, `planOk_written` (K5OwnRounds.lean, K5OwnPlanOk.lean).
Limits. Implications: that the front returns at any public files is a premise. Nothing on soundness.
On hiding nothing.
WHAT IT BUYS: of K5's row's eight binders (`k5_row_own`, K5RowOwn.lean) h₁ and h₂ fall, at all
public
files in the goals' scope, free of any twin of a plan and of any tie to one. WHAT IT DOES NOT: h₄
(the
walk at each plan) · hm · hZ, hG: shown at no public files by Lean's kernel.

-/
import Johnson.Desc.First.Att.Row.K5OwnInScope
import Johnson.Desc.First.Att.Row.K5OwnRounds
import Johnson.Desc.First.Att.Row.K5OwnPlanOk
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}

/-- The public data of the front's return are publicOf's. -/
theorem public_of_front (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z) :
    publicOf Pb.pol Pb.KL (some lay) = .ok Z.p.X :=
  (VerifiableInference.PlanWritten.publicOfO_older Pb.pol Pb.KL (some lay)).symm.trans
    (ProofFile.Law.pub_public hZ)

/-- **h₁ OF K5's ROW, IN SCOPE.** -/
theorem h1_in_scope (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z) :
    ∀ g, g < 12 → ∀ a, Z.p.X.A[g]? = some a → nRounds a.own = 162 := by
  intro g hg a ha
  rw [own_in_scope hS hR (public_of_front hZ) hg ha]
  exact (nRounds_rows ownW _).trans rounds_written

/-- **h₂ OF K5's ROW, IN SCOPE.** -/
theorem h2_in_scope (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z) :
    ∀ g, g < 12 → ∀ a, Z.p.X.A[g]? = some a → planOkOwn a.own = true := by
  intro g hg a ha
  rw [own_in_scope hS hR (public_of_front hZ) hg ha]
  exact (planOkOwn_rows ownW _).trans planOk_written

end H2K5.Row

#print axioms H2K5.Row.public_of_front
#print axioms H2K5.Row.h1_in_scope
#print axioms H2K5.Row.h2_in_scope
