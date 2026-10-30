-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/PlanOfScope.lean: NINE LINES ON THE PUBLIC PARAMETERS, AS THEOREMS IN THE
GOALS' SCOPE: SEVEN ARE FIELDS OF THE STRUCTURE K4RowPlan, which the row of the sub-protocol K4 asks
as premises (Johnson/Road/K4/K4RowOfMeans.lean: NOT IMPORTED: that the texts fit is held by reading,
not by Lean), two stand beside them (g, y): at an opening (IM.Open) of the IOP as written in Lean
for the proof file, at each of the twelve layers' links m = 2 g, at the opening's own public
parameters X, and at EVERY member x of K4's lot's list that bears the link's number. Statements and
proofs: a join.

  `not_head`: where p4 = true and NGr = 12, link 2 g, g < 12, is not the head's.
  `PlanAtX X pol KL ly g par`: THE NINE, BY NAME, seven in the words of K4RowPlan's fields: pc2, pc7
    (the two lookup arguments of the link stand at pieces 2 and 7) · notHead · step · plan (the
    entry of X.G at the link's group is par's own list of numbers hp) · pubOf (X is what publicOf
    returns on the public files) · shape (the shape of the lookup argument on the calls is one in X
    and in par) · g · y (par's group is g; its layout is X's).
  **`plan_of_scope`**: all nine, at par := x.2 with k3Runs := true.
No new argument: Meaning.scope_plans (Johnson/Goal/Meaning/PlanShapes.lean), K4Of at an opening and
k04_sits_one (Johnson/Road/K4/K04Sits.lean), IM's Open.public.
**Limits.** PREMISES: the goals' scope (VerifierAndGoals.InScope, VerifierAndGoals.readFiles) and an opening O: there is
one wherever the make of the IOP as written in Lean returns (IM.seat_open), at our second,
non-standard hash (built on BLAKE2b's compression function), OnBytes.secondHashFunction: THAT IT RETURNS IS
SHOWN BY NO THEOREM. The nine are lines on numbers: none says that a test on the plan (frontB, rowB,
lookInPlanB) is true. K4RowPlan's other fields, its tests on the plan among them, are not touched.
Nothing on soundness. K04_law, the law of the sub-protocol K4 itself, IS NOT PROVED.


-/
import Johnson.Road.K4.Riders.SeatsAtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (Block FileDescription K3.pieceAt K3.isHead)
open VerifiableInference.Desc.First (S)

/-- Link 2 g, g < 12, is not the head's. -/
theorem not_head {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12) {g : ℕ} (hg : g < 12) :
    K3.isHead X (2 * g) = false := by
  unfold K3.isHead
  rw [h4, hN, if_pos rfl]
  exact beq_false_of_ne (by omega)

/-- **The nine lines**, at link 2 g. -/
structure PlanAtX (X : Verify.Public) (pol KL ly : ByteArray) (g : ℕ) (par : Par) : Prop where
  pc2 : K3.pieceAt X (2 * g) false = 2
  pc7 : K3.pieceAt X (2 * g) true = 7
  notHead : 2 * g ≠ (if X.p4 then 2 else 1) * X.NGr
  step : 2 * g % (if X.p4 then 2 else 1) = 0
  plan : X.G[2 * g / (if X.p4 then 2 else 1)]? = some par.hp
  pubOf : Verify.publicOf pol KL (some ly) = .ok X
  shape : X.y.fo = par.P.y.fo
  g : par.g = g
  y : par.P.y = X.y

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}

/-- **In the goals' scope, at an opening, at every member of K4's lot's list that bears the number
of link 2 g, g < 12: the nine lines.** -/
theorem plan_of_scope {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {x : Bool × Par} (hx : x ∈ ProofFile.k4From Z Bs.G₀ Bs.G₀.built.toList 0 none)
    (hl : x.2.link = 2 * g) :
    PlanAtX Bs.G₀.W Pb.pol Pb.KL ly g { x.2 with k3Runs := true } := by
  obtain ⟨k4, kN, _⟩ := Meaning.scope_plans hS hR O.public
  obtain ⟨_, _, y, _, _, e3, _, e5, e6, e7, e8, _⟩ := k4Of_of_open hS hR O g hg
  obtain rfl : x = y := k04_sits_one hx e3 hl e5
  have hh := not_head k4 kN hg
  refine ⟨?_, ?_, ?_, ?_, ?_, O.public, ?_, e6, ?_⟩
  · unfold K3.pieceAt
    rw [hh]
    rfl
  · unfold K3.pieceAt
    rw [hh]
    rfl
  · rw [k4, kN, if_pos rfl]
    omega
  · rw [k4, if_pos rfl]
    exact Nat.mul_mod_right 2 g
  · rw [k4, if_pos rfl, Nat.mul_div_cancel_left g (by decide : 0 < 2)]
    exact e8
  · show Bs.G₀.W.layers.y.fo = x.2.P.y.fo
    rw [e7]
  · show x.2.P.y = Bs.G₀.W.layers.y
    rw [e7]

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.not_head
#print axioms OnBytes.Road.K4.Riders.plan_of_scope
