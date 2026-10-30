-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K3LightTie.lean: THE LOT OF THE KIND "LOOKUP" (K3Lot.lot): THE LIGHT FILE's
TEST (K3Light.lean) IS K3RowXB.lean's; so a yes of the light test gives the six hypotheses
on the public data. Joinings.
  `readsXAt_light`, `readsXB_light`: the two tests are one, at a segment and whole: the tests on
    lists by a short induction (`sameList_light`: two recursive definitions of one text are not one
    by rfl), the rest by unfolding.
  `readsXAt_congr`: the congruence (`Light.readsAt_congr`) at K3RowXB.lean's own name.
  `readsX_of_light`: **`Light.readsB X = true → ReadsX X`.** `readsX_of_parts`: the same from the
    first 24 segments and the head's.
TWO NAMES FOR ONE TEXT, BY DESIGN: K3Light.lean goes with whoever decides the test at a value;
K3RowXB.lean and this file go with the join.
Limits. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K3RowXB
import Johnson.AtFull.Desc.Lots.K3Light

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K3
open OnBytes OnBytes.Model

theorem sameList_light : ∀ l m : List Call, sameList l m = Light.sameList l m
  | [], [] => rfl
  | a :: l, b :: m => by
    simp only [sameList, Light.sameList]
    rw [sameList_light l m]
    rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

theorem sameView_light (v w : String × Nat × Array Call × Array Nat × Nat × Nat × Nat × Nat) :
    sameView v w = Light.sameView v w := by
  unfold sameView Light.sameView
  rw [sameList_light]

theorem readsXAt_light (X : Verify.Public) (i : Nat) : readsXAt X i = Light.readsAt X i := by
  unfold readsXAt Light.readsAt
  simp only [sameView_light]
  rfl

theorem readsXB_light (X : Verify.Public) : readsXB X = Light.readsB X := by
  unfold readsXB Light.readsB
  congr 1
  funext i
  exact readsXAt_light X i

theorem readsXAt_congr {X X' : Verify.Public} (hL : X.layers = X'.layers) (hG : X.G = X'.G)
    (hA : X.A = X'.A) (h4 : X.p4 = true) (hN : X.NGr = 12) {i : Nat} (hi : i < 24) :
    readsXAt X i = readsXAt X' i := by
  rw [readsXAt_light, readsXAt_light]
  exact Light.readsAt_congr hL hG hA h4 hN hi

theorem readsX_of_light {X : Verify.Public} (h : Light.readsB X = true) : ReadsX X :=
  readsX_of ((readsXB_light X).trans h)

theorem readsX_of_parts {X : Verify.Public} (h : (List.range 24).all (Light.readsAt X) = true)
    (h24 : Light.readsAt X 24 = true) : ReadsX X :=
  readsX_of_light (Light.readsB_of_parts h h24)

end Johnson.AtFull.Lots.K3

#print axioms Johnson.AtFull.Lots.K3.sameList_light
#print axioms Johnson.AtFull.Lots.K3.sameView_light
#print axioms Johnson.AtFull.Lots.K3.readsXAt_light
#print axioms Johnson.AtFull.Lots.K3.readsXB_light
#print axioms Johnson.AtFull.Lots.K3.readsXAt_congr
#print axioms Johnson.AtFull.Lots.K3.readsX_of_light
#print axioms Johnson.AtFull.Lots.K3.readsX_of_parts
