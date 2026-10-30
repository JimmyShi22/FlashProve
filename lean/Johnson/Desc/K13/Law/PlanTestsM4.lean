-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/PlanTestsM4.lean: THE FOUR EQUATIONS ON THE PLAN THAT "the three items of the
book and K13's own item are riders at W's commitment" SPENDS (`riders4_over`,
Johnson/Desc/K13/Law/RidersK12.lean: its premises hft, hp, hs, hx), AS TESTS WITH CODE, each with
the lemma "the test's yes gives the premise, to the letter"; and a payer of hp and hs that is no
run; and the like for the chain's first sending. Definitions and statements with their proofs. It
names no block and no filling.
The letters. ft: the number of the chain's first tree by the plan. L: the plan's list of the
messages' seats (tree, part) and of the trees' shapes (`K12.Door.Laid`). M: the plan's list of the
messages' shapes. N: what the table of joints reads of the plan (`First.Numbers`). p: the place in
front of which W's commitment stands. P': the parameters of W's commitment (`K1.Par`). The user lays
d.ft, d.L, d.M (`K12.Door.K12Data`) and D.N.
Main names:
  `planFirstTreeB ft P'` (hft): the plan's first tree is the commitment's.
  `planPlacesB L N p P'` (hp): behind the messages that the plan counts in front of p, its list of
    seats goes on with this sending's layout, the trees counted on from those in front of p.
  `planTreesB L N p P'` (hs): behind the trees in front of p, its list of the trees' shapes goes on
    with this sending's.
  `planShapesB M N p P'` (hx): behind the messages in front of p, its list of the messages' shapes
    goes on with this sending's.
  `planM4B`, `PlanM4`, `planM4_of`: the four together.
  `plan_goes_on`: **hp AND hs WITHOUT A RUN**: where the plan's lists are made of the chain's
    sendings by the verifier's own layout (`K12.Coin.laidOf`), W's commitment is one of them, and
    the two counts in front of p are the lengths of what the sendings in front lay: by
    `laidOf_goes_on` (Johnson/Desc/K12/Coin/BookRides.lean), CALLED. That
    `layTrees P'.codes P'.sent` gives a layout is NO premise: the maker's yes gives it, so
    `K1.layOf`'s fall-back (the empty layout) is not met.
  `plan_goes_on_door`: the same from the other maker of the lists (`K12.Door.laidOf`), by
    `laidOf_is` (Johnson/Desc/K12/Door/DoorIs.lean), CALLED.
  `planM4_of_sends`: so the four from two tests (hft, hx) and that.
  `planIndexLastB N P'`, `PlanGSeats`, `planGB`, `planG_of`: THE LIKE FOR THE CHAIN's FIRST SENDING
    (Johnson/Desc/K13/Law/FillGFromSentences.lean): `riderG_seats`' hp and hs and
    `riderG_shapes`' hx are the three above at P' := K1.firstPar q gp (its letter L is laid as
    `toTree L`); `fillG_of`'s hidx is new: the index masks' message is the sending's last.
  `plan_goes_on_first`: hp and hs where no sending stands in front and both counts are 0.
What is not claimed. That any of these tests says yes at a plan: NONE HAS RUN. That the plan's lists
of record are made so, that W's commitment is among the sendings, or that the counts of the filling
of record are those lengths. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Borders
import Johnson.Desc.K1.Law.BookAtRecord
import Johnson.Desc.K1.Law.Writes3
import Johnson.Desc.K12.Door.DoorIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.K12.Door (Laid toTree)

/-- (hft) The plan's first tree is the commitment's. -/
def planFirstTreeB (ft : ℕ) (P' : K1.Par) : Bool := decide (ft = P'.gp.firstTree)

theorem planFirstTree_gives {ft : ℕ} {P' : K1.Par} (h : planFirstTreeB ft P' = true) :
    ft = P'.gp.firstTree := of_decide_eq_true h

/-- (hp) The plan's list of seats goes on with this sending's layout. -/
def planPlacesB (L : Laid) (N : Numbers) (p : Option Place) (P' : K1.Par) : Bool :=
  decide (((toTree L).places.drop (N.msgsAt p)).take P'.sent.size =
      K12.Coin.placesOf (N.treesAt p) P'.sent.size (K1.layOf P'))

theorem planPlaces_gives {L : Laid} {N : Numbers} {p : Option Place} {P' : K1.Par}
    (h : planPlacesB L N p P' = true) :
    ((toTree L).places.drop (N.msgsAt p)).take P'.sent.size =
      K12.Coin.placesOf (N.treesAt p) P'.sent.size (K1.layOf P') := of_decide_eq_true h

/-- (hs) The plan's list of the trees' shapes goes on with this sending's. -/
def planTreesB (L : Laid) (N : Numbers) (p : Option Place) (P' : K1.Par) : Bool :=
  decide (((toTree L).shapes.drop (N.treesAt p)).take (K1.layOf P').shapes.size =
      (K1.layOf P').shapes.toList)

theorem planTrees_gives {L : Laid} {N : Numbers} {p : Option Place} {P' : K1.Par}
    (h : planTreesB L N p P' = true) :
    ((toTree L).shapes.drop (N.treesAt p)).take (K1.layOf P').shapes.size =
      (K1.layOf P').shapes.toList := of_decide_eq_true h

/-- (hx) The plan's list of the messages' shapes goes on with this sending's. -/
def planShapesB (M : List OracleShape) (N : Numbers) (p : Option Place) (P' : K1.Par) : Bool :=
  decide ((M.drop (N.msgsAt p)).take (K1.shapesOf P').length = K1.shapesOf P')

theorem planShapes_gives {M : List OracleShape} {N : Numbers} {p : Option Place} {P' : K1.Par}
    (h : planShapesB M N p P' = true) :
    (M.drop (N.msgsAt p)).take (K1.shapesOf P').length = K1.shapesOf P' := of_decide_eq_true h

/-- The four premises together. -/
structure PlanM4 (ft : ℕ) (L : Laid) (M : List OracleShape) (N : Numbers) (p : Option Place)
    (P' : K1.Par) : Prop where
  hft : ft = P'.gp.firstTree
  hp : ((toTree L).places.drop (N.msgsAt p)).take P'.sent.size =
      K12.Coin.placesOf (N.treesAt p) P'.sent.size (K1.layOf P')
  hs : ((toTree L).shapes.drop (N.treesAt p)).take (K1.layOf P').shapes.size =
      (K1.layOf P').shapes.toList
  hx : (M.drop (N.msgsAt p)).take (K1.shapesOf P').length = K1.shapesOf P'

/-- The four tests together. -/
def planM4B (ft : ℕ) (L : Laid) (M : List OracleShape) (N : Numbers) (p : Option Place)
    (P' : K1.Par) : Bool :=
  planFirstTreeB ft P' && planPlacesB L N p P' && planTreesB L N p P' && planShapesB M N p P'

theorem planM4_of {ft : ℕ} {L : Laid} {M : List OracleShape} {N : Numbers} {p : Option Place}
    {P' : K1.Par} (h : planM4B ft L M N p P' = true) : PlanM4 ft L M N p P' := by
  unfold planM4B at h
  simp only [Bool.and_eq_true] at h
  exact ⟨planFirstTree_gives h.1.1.1, planPlaces_gives h.1.1.2, planTrees_gives h.1.2,
    planShapes_gives h.2⟩

/-- **hp and hs without a run**: the plan's lists are made of the chain's sendings, W's commitment
is one of them, and the counts in front of p are the lengths of what the sendings in front lay. -/
theorem plan_goes_on {L : Laid} {N : Numbers} {p : Option Place} {P' : K1.Par}
    (pre post : List (Array OracleNotice)) (A : K12.Coin.Laid)
    (hL : K12.Coin.laidOf P'.codes (pre ++ P'.sent :: post) = some (toTree L))
    (hA : K12.Coin.laidOf P'.codes pre = some A) (hm : N.msgsAt p = A.places.length)
    (ht : N.treesAt p = A.shapes.length) :
    (((toTree L).places.drop (N.msgsAt p)).take P'.sent.size =
        K12.Coin.placesOf (N.treesAt p) P'.sent.size (K1.layOf P')) ∧
      ((toTree L).shapes.drop (N.treesAt p)).take (K1.layOf P').shapes.size =
        (K1.layOf P').shapes.toList := by
  obtain ⟨A', lay, hA', hl, g1, g2⟩ :=
    K12.Coin.laidOf_goes_on P'.codes pre post P'.sent (toTree L) hL
  obtain rfl := Option.some.inj (hA.symm.trans hA')
  have e : K1.layOf P' = lay := by
    unfold K1.layOf
    rw [hl]
    rfl
  rw [e, hm, ht]
  exact ⟨g1, g2⟩

/-- The same from the other maker of the plan's lists. -/
theorem plan_goes_on_door {L : Laid} {N : Numbers} {p : Option Place} {P' : K1.Par}
    (sends : List (List OracleNotice)) (pre post : List (Array OracleNotice)) (A : K12.Coin.Laid)
    (hL : K12.Door.laidOf P'.codes sends = some L)
    (hsends : sends.map (·.toArray) = pre ++ P'.sent :: post)
    (hA : K12.Coin.laidOf P'.codes pre = some A) (hm : N.msgsAt p = A.places.length)
    (ht : N.treesAt p = A.shapes.length) :
    (((toTree L).places.drop (N.msgsAt p)).take P'.sent.size =
        K12.Coin.placesOf (N.treesAt p) P'.sent.size (K1.layOf P')) ∧
      ((toTree L).shapes.drop (N.treesAt p)).take (K1.layOf P').shapes.size =
        (K1.layOf P').shapes.toList := by
  refine plan_goes_on pre post A ?_ hA hm ht
  rw [← hsends, K12.Door.laidOf_is, hL]
  rfl

/-- **The four, from two tests and the maker of the plan's lists.** -/
theorem planM4_of_sends {ft : ℕ} {L : Laid} {M : List OracleShape} {N : Numbers}
    {p : Option Place} {P' : K1.Par} (pre post : List (Array OracleNotice)) (A : K12.Coin.Laid)
    (h1 : planFirstTreeB ft P' = true) (h4 : planShapesB M N p P' = true)
    (hL : K12.Coin.laidOf P'.codes (pre ++ P'.sent :: post) = some (toTree L))
    (hA : K12.Coin.laidOf P'.codes pre = some A) (hm : N.msgsAt p = A.places.length)
    (ht : N.treesAt p = A.shapes.length) : PlanM4 ft L M N p P' :=
  ⟨planFirstTree_gives h1, (plan_goes_on pre post A hL hA hm ht).1,
    (plan_goes_on pre post A hL hA hm ht).2, planShapes_gives h4⟩

/-! ## The chain's first sending -/

/-- (hidx) The index masks' message is the sending's last. -/
def planIndexLastB (N : Numbers) (P' : K1.Par) : Bool := decide (N.indexNo = P'.sent.size - 1)

theorem planIndexLast_gives {N : Numbers} {P' : K1.Par} (h : planIndexLastB N P' = true) :
    N.indexNo = P'.sent.size - 1 := of_decide_eq_true h

/-- The four premises on the plan at the chain's first sending. -/
structure PlanGSeats (L : Laid) (M : List OracleShape) (N : Numbers) (p : Option Place)
    (P' : K1.Par) :
    Prop where
  hp : ((toTree L).places.drop (N.msgsAt p)).take P'.sent.size =
      K12.Coin.placesOf (N.treesAt p) P'.sent.size (K1.layOf P')
  hs : ((toTree L).shapes.drop (N.treesAt p)).take (K1.layOf P').shapes.size =
      (K1.layOf P').shapes.toList
  hx : (M.drop (N.msgsAt p)).take (K1.shapesOf P').length = K1.shapesOf P'
  hidx : N.indexNo = P'.sent.size - 1

/-- The four tests together. -/
def planGB (L : Laid) (M : List OracleShape) (N : Numbers) (p : Option Place) (P' : K1.Par) :
    Bool :=
  planPlacesB L N p P' && planTreesB L N p P' && planShapesB M N p P' && planIndexLastB N P'

theorem planG_of {L : Laid} {M : List OracleShape} {N : Numbers} {p : Option Place} {P' : K1.Par}
    (h : planGB L M N p P' = true) : PlanGSeats L M N p P' := by
  unfold planGB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨planPlaces_gives h.1.1.1, planTrees_gives h.1.1.2, planShapes_gives h.1.2,
    planIndexLast_gives h.2⟩

/-- hp and hs without a run, where no sending stands in front. -/
theorem plan_goes_on_first {L : Laid} {N : Numbers} {p : Option Place} {P' : K1.Par}
    (post : List (Array OracleNotice))
    (hL : K12.Coin.laidOf P'.codes (P'.sent :: post) = some (toTree L)) (hm : N.msgsAt p = 0)
    (ht : N.treesAt p = 0) :
    (((toTree L).places.drop (N.msgsAt p)).take P'.sent.size =
        K12.Coin.placesOf (N.treesAt p) P'.sent.size (K1.layOf P')) ∧
      ((toTree L).shapes.drop (N.treesAt p)).take (K1.layOf P').shapes.size =
        (K1.layOf P').shapes.toList :=
  plan_goes_on [] post {} hL rfl hm ht

end VerifiableInference.Desc.K13.Law
