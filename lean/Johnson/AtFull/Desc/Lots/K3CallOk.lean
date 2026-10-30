-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Desc/Lots/K3CallOk.lean: THE LOT OF THE KIND "LOOKUP": WHEREVER THE VERIFIER's
`publicOf` RETURNS, EVERY CALL OF EVERY LOOKUP ON A SEGMENT's CALLS PASSES THE TEST ON A CALL
(`callOk`, Johnson/Desc/First/Look/ShapeOwn.lean). A LAW BY THE MAKE: no kernel fact; no table is
read. Joinings of laws. Why. `callOk` reads a call's written table whole (its length; each
value below the prime); three calls of each such place bear a table of 65,536 rows, so no written
value can hold them. But `publicOf` itself runs the elder library's `Forest.shape` on these very
calls before it returns, whose first line asks the twin test `Forest.callAsk` of every call.
  `callOk_of_shapeOf`: off `Fo.ShapeOf` (OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean), by another file's
    `all_of_shape` (Johnson/AtFull/ProofRows/K3CallsOkHead.lean: Forest.shape calls lid = .ok h
    gives calls.all callOk = true).
  `callOk_layers` (`layout_of_public`, `Fo.layout_shape`) · `callOk_att`: at every member of X.A
    (`Fo.Pub2.lookPubA_ok`'s field shape). The output head's: that other file's `public_calls_ok`.
  `callOk_at`: **at every place that `lookAt X i false` gives.** `callOk_atO`: the same where the
    text with the second hash function as an argument returns at OnBytes.secondHashFunction (`publicOfO_older`).
WHAT STAYS A PREMISE: `publicOf` returned X. WHERE THE WEIGHT GOES: this law pays nothing itself:
whoever shows that return walks the tables there, or needs a law on them: their cost stands once, in
the return.
Limits. Nothing on soundness.

-/
import Johnson.AtFull.ProofRows.K3CallsOkHead
import Johnson.Goal.Meaning.OkScope
import Johnson.Desc.Ok.PlanWritten.PublicMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K3
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf Public)
open VerifiableInference.Desc.First.Look (lookAt callOk)
open Johnson.AtFull.ProofRows.K3 (all_of_shape public_calls_ok)

theorem callOk_of_shapeOf {calls : Array Call} {pub : Array Nat} {lid : Nat} {h : Forest.Shape}
    (e : Fo.ShapeOf calls pub lid h) : calls.all callOk = true := by
  obtain ⟨h0, e0, -⟩ := e
  exact all_of_shape e0

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}

theorem callOk_layers (h : publicOf pol KL lay = .ok X) : X.y.cl.all callOk = true :=
  callOk_of_shapeOf (Fo.layout_shape (Meaning.P34.layout_of_public h))

theorem callOk_att (h : publicOf pol KL lay = .ok X) {g : Nat} {a : Attention.Plan}
    (ha : X.A[g]? = some a) : (a.S.calls.map (·.call)).all callOk = true :=
  callOk_of_shapeOf (Fo.Pub2.lookPubA_ok (M₀ := Unit) (fun _ _ => 0) h g a ha 0 0 Unit).shape

/-- **AT EVERY PLACE OF A LOOKUP ON THE CALLS.** -/
theorem callOk_at (h : publicOf pol KL lay = .ok X) {i : Nat}
    {x : VerifiableInference.Desc.First.Look.Place} (hx : lookAt X i false = some x) :
    x.calls.all callOk = true := by
  unfold lookAt at hx
  simp only [Bool.false_eq_true, ↓reduceIte] at hx
  repeat' split at hx
  all_goals first
    | (obtain rfl := Option.some.inj hx
       exact public_calls_ok h)
    | (obtain ⟨hp, -, e⟩ := Option.bind_eq_some_iff.1 hx
       obtain rfl := Option.some.inj e
       exact callOk_layers h)
    | (obtain ⟨a, ha, e⟩ := Option.bind_eq_some_iff.1 hx
       obtain rfl := Option.some.inj e
       exact callOk_att h ha)

/-- The same off the text with the second hash function as an argument, at OnBytes.secondHashFunction. -/
theorem callOk_atO
    (h : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction pol KL lay = .ok X) {i : Nat}
    {x : VerifiableInference.Desc.First.Look.Place} (hx : lookAt X i false = some x) :
    x.calls.all callOk = true :=
  callOk_at ((VerifiableInference.PlanWritten.publicOfO_older pol KL lay).symm.trans h) hx

end Johnson.AtFull.Lots.K3

#print axioms Johnson.AtFull.Lots.K3.callOk_of_shapeOf
#print axioms Johnson.AtFull.Lots.K3.callOk_layers
#print axioms Johnson.AtFull.Lots.K3.callOk_att
#print axioms Johnson.AtFull.Lots.K3.callOk_at
#print axioms Johnson.AtFull.Lots.K3.callOk_atO
