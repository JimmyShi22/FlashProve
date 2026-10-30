-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/OnXOfPlan.lean: THE STRUCTURE K4OnX (Johnson/Road/K4/K4OnX.lean: nine facts
on the public parameters X and K4's own parameters par at a segment m, premises of K4's row at the
composed meaning) CONCLUDED IN THE GOALS' SCOPE.

  `k4OnX_of_plan`: the nine lines of PlanAtX (Johnson/Road/K4/Riders/PlanOfScope.lean) at group g
    are K4OnX's nine fields at m := 2 * g, layout := some ly. Premise: the structure PlanAtX.
  **`k4OnX_of_scope`**: K4OnX at the opening's own public parameters, at segment 2 g, g < 12, at
    par := x.2 with k3Runs := true, for every member x of K4's lot's list that bears the number
    2 g. Premises: the goals' scope (hS, hR) · an opening O of the IOP as written in Lean · hx, hl
    (k04_sits_desc, Johnson/Road/K4/K04Sits.lean, gives such an x).
No new argument: plan_of_scope.
Limits. That there is an opening is shown by no theorem (IM.seat_open: wherever onlineDescription returns).
The nine are lines on numbers: none says that a test on the public parameters is true. K04_law, the
law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.K4OnX
import Johnson.Road.K4.Riders.PlanOfScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)

/-- The nine lines are the nine fields. -/
theorem k4OnX_of_plan {X : Verify.Public} {pol KL ly : ByteArray} {g : ℕ} {par : Par}
    (Q : PlanAtX X pol KL ly g par) : K4OnX X pol KL (some ly) (2 * g) par where
  shape := Q.shape
  pc2 := Q.pc2
  pc7 := Q.pc7
  pubOf := Q.pubOf
  notHead := Q.notHead
  step := Q.step
  plan := Q.plan
  g := by rw [Q.g]
  y := Q.y

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}

/-- **K4OnX in the goals' scope, at an opening, at every member of K4's lot's list that bears the
number 2 g, g < 12.** -/
theorem k4OnX_of_scope {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {x : Bool × Par} (hx : x ∈ ProofFile.k4From Z Bs.G₀ Bs.G₀.built.toList 0 none)
    (hl : x.2.link = 2 * g) :
    K4OnX Bs.G₀.W Pb.pol Pb.KL (some ly) (2 * g) { x.2 with k3Runs := true } :=
  k4OnX_of_plan (plan_of_scope hS hR O hg hx hl)

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.k4OnX_of_plan
#print axioms OnBytes.Road.K4.Riders.k4OnX_of_scope
