-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4NextOfScope.lean: THE PUBLIC PARAMETERS' NEXT FREE SLOT BEHIND A LAYERS' SEGMENT's
LOOKUP ON THE CALLS (nextOfPlan, Johnson/Desc/First/K4NextOf.lean) IS THE NUMBER OF ELEMENTS OF THE
LAYERS' LAYOUT's SHAPE OF THE LOOKUP: so it is there, and it is no letter.

  **`nextOf_lay`**: nextOfPlan X m = some (Forest.elems X.y.fo). Premises: h: X is what publicOf
    returns · hn: m is not the head's segment · h0: m is a layers' segment's number · hplan: X.G
    has an entry at its group. NO SCOPE IS ASKED: four fields of the structure K4OnX
    (Johnson/Road/K4/K4OnX.lean) are these premises.
No new argument: place_lay (Johnson/Desc/First/Look/K3PlaceLetters.lean: the shape is X.y.fo, the
first slot 0). That lookAt returns there is by unfolding; another file has that step
as a lemma (lookAt_plan, Johnson/Road/K4/K4PinsScope.lean): not imported: it stands over many files
that this one does not need.
Limits. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Desc.First.K4NextOf
import Johnson.Desc.First.Look.K3PlaceLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.FillK4 (nextOfPlan)
open VerifiableInference.Desc.First.Look (lookAt placeAt placeAt_iff place_lay)

/-- **The next free slot behind a layers' segment's lookup on the calls.** -/
theorem nextOf_lay {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public} {m : ℕ}
    {hp : Layer.HPlan2} (h : Verify.publicOf pol KL layout = .ok X)
    (hn : m ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : m % (if X.p4 then 2 else 1) = 0)
    (hplan : X.G[m / (if X.p4 then 2 else 1)]? = some hp) :
    nextOfPlan X m = some (Forest.elems X.y.fo) := by
  have hx : ∃ x, lookAt X m false = some x := by
    unfold lookAt
    dsimp only
    rw [if_neg (by simpa using hn), if_pos (by simpa using h0), hplan]
    exact ⟨_, rfl⟩
  obtain ⟨x, ex⟩ := hx
  obtain ⟨p, ep⟩ : ∃ p, placeAt X m false = some p := ⟨_, placeAt_iff.2 ⟨x, ex, rfl⟩⟩
  obtain ⟨_, _, es, _, ef, _⟩ := place_lay h ep hn h0
  unfold nextOfPlan
  rw [ep]
  show (p.shape.map fun s => p.first + Forest.elems s) = some (Forest.elems X.y.fo)
  rw [es, ef]
  show some (0 + Forest.elems X.y.fo) = some (Forest.elems X.y.fo)
  rw [Nat.zero_add]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.nextOf_lay
