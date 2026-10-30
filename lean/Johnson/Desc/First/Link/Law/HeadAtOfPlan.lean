-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HeadAtOfPlan.lean: "THE OUTPUT HEAD's LOOKUP HAS ITS PLACE" (headAt X is
some: Johnson/Desc/First/Look/K3CallerHead.lean) FROM K3's OWN SUB-PROTOCOL AT AN ADDRESS OF PIECE 3
AND ITS TEST ON THE PLAN. Theorems with their proofs. General in the public data X: no scope.

Why it holds. headAt X is lookAt X iH false, iH the head's link's number, with the shape of its
parameters laid in. K3's sub-protocol at an address is made only where placeAt X i digits answers,
and its test on the plan holds the kind's public test there (stated_planOk,
Johnson/Desc/First/Look/K3PlanOfOk.lean), which says no where the parameters fix no shape (their
planOk_parts). The piece 3 stands at the head's link's lookup on the calls alone (pieceAt,
Johnson/Desc/First/Look/K3Own.lean).

  headAt_of_place  placeAt X iH false = some p → p.shape.isSome = true → (headAt X).isSome = true
  theStated_head   **K3.theStated … a = some b → b.planOk = true → a.piece = 3 →
                   (headAt X).isSome = true**

Limits. That a description holds such a sub-protocol, and passes its test on the plan, is the
caller's. Nothing on soundness.

-/
import Johnson.Desc.First.Look.K3PlanOfOk
import Johnson.Desc.First.Look.K3CallerHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head.Law (headAt)

theorem headAt_of_place {X : Verify.Public} {p : First.Look.P}
    (hp : First.Look.placeAt X ((if X.p4 then 2 else 1) * X.NGr) false = some p)
    (hs : p.shape.isSome = true) : (headAt X).isSome = true := by
  unfold First.Look.placeAt at hp
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hp
  obtain ⟨h, e⟩ := Option.isSome_iff_exists.1 hs
  unfold headAt
  rw [hx]
  show (((First.Look.P.ofPlace (Params.settingOf X.P.frame) false x).shape.map fun h =>
    { x with fs := h }) : Option First.Look.Place).isSome = true
  rw [e]
  rfl

/-- **K3's sub-protocol at an address of piece 3, with its test on the plan, gives the place.** -/
theorem theStated_head {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) (hp : b.planOk = true)
    (h3 : a.piece = 3) : (headAt X).isSome = true := by
  obtain ⟨i, d, p, laid, _, e, hpl, hk⟩ := K3.stated_planOk claim readers X codes shape a b h hp
  obtain ⟨hs, es, _⟩ := K3.planOk_parts hk
  rw [h3] at e
  unfold K3.pieceAt at e
  cases hh : K3.isHead X i <;> cases d <;> simp [hh] at e
  have ei : i = (if X.p4 then 2 else 1) * X.NGr := by
    unfold K3.isHead at hh
    simpa using hh
  exact headAt_of_place (ei ▸ hpl) (by rw [es]; rfl)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.headAt_of_place
#print axioms VerifiableInference.Desc.LinkJoin.theStated_head
