-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/DigitsShapeAt.lean: kind K3: at EVERY link of the public parameters the
lookup on the digits fixes, as its shape, the plan's own f9: so the reader `digAt`
(Johnson/Desc/First/Look/K3CallerTests.lean), which lays f9 anew, hands on the plan's own parameters
of the approximate range proof unturned. Statements and proofs. NO SOUNDNESS IS CLAIMED.
("Link" here: a member of the proof's first chain, the index i of lookAt | tlAt; not a proof that
two committed tables encode the same weights.)

Why. `digAt X i` returns the plan's tl with ONE field laid anew: f9 := the shape that the lookup's
own parameters make. Wherever another file's sentence stands at the plan's own f9 that is a seam.
At the attention links it is closed in Johnson/Desc/First/Att/GuardPlanDigits.lean.
Here it is closed at all links by one argument: `lookAt X i true` and
`tlAt X i` split by i in the same way.

Main names:
  `ShapeZAll X`: the premise: `Fo.ZPlan.ShapeZ` at hp.tl for every member hp of X.G, at a.seam.tl
    for every member a of X.A, and at X.H.tl. It is the conclusion of the library's
    `Fo.ZPlan.public_shapeZ` (OnBytes/Tie/Pv/Lookup/Ends/FoShapeZ.lean), word for word.
  `shapeZAll_of_public`: so it holds wherever `Verify.publicOf pol KL layout = .ok X`.
  `place_digits`: the place that lookAt returns for the digits at link i holds the two calls, the
    numbers of padding keys, the cap and the f9 of the very tl that tlAt returns at i. No premise.
  `shapeZ_at`: under ShapeZAll: ShapeZ at whatever tlAt returns.
  **`digits_shape_at`**: under ShapeZAll: (P.ofPlace set true x).shape = some tl.f9, at every link.
  **`digAt_is`**: under ShapeZAll: digAt X i = some (x, tl) → tlAt X i = some tl.
  `tlAt_lay`, `tlAt_head`, `digits_shape_lay`, `digits_shape_head`: the same at a layers' link and
    at the head's, by the group's number.

OBJECT: no text that runs: the readers digAt, lookAt, tlAt of the public parameters X.
USER: Johnson/Desc/First/Look/K3DigitsOfAt.lean, Johnson/P5T/DigStaticAtMg.lean,
  Johnson/P1K8R/DigitsAtDraw.lean, Johnson/HB/LLHARD/Q38E/TiesAtHead.lean (digAt_is);
  Johnson/Desc/AtSeats/ULayAtAll.lean (tlAt_lay); Johnson/K8Q35R/MatsAtHead.lean (tlAt_head).
LETTERS: X, i, g; set, x, tl as the readers return them.
Compiled with the whole library.


Limits. ShapeZAll is a premise but where publicOf returns (shapeZAll_of_public).
A condition that a first sketch of digits_shape_lay lacked: g ≠ X.NGr. At i = step * X.NGr both
readers take the head's arm, whatever X.G holds at X.NGr. That X.G has just X.NGr members is not
shown here.

No test is asked.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerTests
import Johnson.Desc.First.Look.K3CallerCellsLaw
import OnBytes.Tie.Pv.Lookup.Ends.FoShapeZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- At the parameters of every approximate range proof in the public parameters the lookup's shape
is made of that proof's own two calls, numbers of padding keys and cap. -/
def ShapeZAll (X : Verify.Public) : Prop :=
  (∀ (g : ℕ) (hp : Layer.HPlan2), X.G[g]? = some hp → _root_.Fo.ZPlan.ShapeZ hp.tl) ∧
  (∀ (g : ℕ) (a : Attention.Plan), X.A[g]? = some a → _root_.Fo.ZPlan.ShapeZ a.seam.tl) ∧
  _root_.Fo.ZPlan.ShapeZ X.H.tl

/-- It holds at whatever publicOf returns. -/
theorem shapeZAll_of_public {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) : ShapeZAll X :=
  _root_.Fo.ZPlan.public_shapeZ h

/-- **The digits' place at link i holds the own four of the tl that tlAt returns at i.** -/
theorem place_digits {X : Verify.Public} {i : ℕ} {x : Place} (hx : lookAt X i true = some x) :
    ∃ tl, tlAt X i = some tl ∧ x.calls = #[tl.z1.call, tl.z2.call] ∧ x.pub = tl.f9.pub ∧
      x.lid = tl.lidb ∧ x.fs = tl.f9 := by
  unfold lookAt at hx
  unfold tlAt
  cases hH : (i == (if X.p4 then 2 else 1) * X.NGr) with
  | true =>
    simp only [hH, ↓reduceIte] at hx ⊢
    obtain ⟨nx, -, rfl⟩ := Option.map_eq_some_iff.1 hx
    exact ⟨X.H.tl, rfl, rfl, rfl, rfl, rfl⟩
  | false =>
    cases hE : (i % (if X.p4 then 2 else 1) == 0) with
    | true =>
      simp only [hH, hE, Bool.false_eq_true, ↓reduceIte] at hx ⊢
      obtain ⟨hp, hg, hx⟩ := Option.bind_eq_some_iff.1 hx
      obtain ⟨nx, -, rfl⟩ := Option.map_eq_some_iff.1 hx
      refine ⟨hp.tl, ?_, rfl, rfl, rfl, rfl⟩
      rw [hg]
      rfl
    | false =>
      simp only [hH, hE, Bool.false_eq_true, ↓reduceIte] at hx ⊢
      obtain ⟨a, hg, hx⟩ := Option.bind_eq_some_iff.1 hx
      obtain ⟨nx, -, rfl⟩ := Option.map_eq_some_iff.1 hx
      refine ⟨a.seam.tl, ?_, rfl, rfl, rfl, rfl⟩
      rw [hg]
      rfl

/-- Under the premise: ShapeZ at whatever tlAt returns. -/
theorem shapeZ_at {X : Verify.Public} (Z : ShapeZAll X) {i : ℕ} {tl : HTailF2}
    (h : tlAt X i = some tl) : _root_.Fo.ZPlan.ShapeZ tl := by
  unfold tlAt at h
  cases hH : (i == (if X.p4 then 2 else 1) * X.NGr) with
  | true =>
    simp only [hH, ↓reduceIte] at h
    obtain rfl := Option.some.inj h
    exact Z.2.2
  | false =>
    cases hE : (i % (if X.p4 then 2 else 1) == 0) with
    | true =>
      simp only [hH, hE, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hp, hg, rfl⟩ := Option.map_eq_some_iff.1 h
      exact Z.1 _ hp hg
    | false =>
      simp only [hH, hE, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨a, hg, rfl⟩ := Option.map_eq_some_iff.1 h
      exact Z.2.1 _ a hg

/-- **At every link the digits' parameters fix the plan's own f9 as their shape.** -/
theorem digits_shape_at {X : Verify.Public} (Z : ShapeZAll X) {i : ℕ} {x : Place} {tl : HTailF2}
    (hx : lookAt X i true = some x) (ht : tlAt X i = some tl) (set : Params.Setting) :
    (P.ofPlace set true x).shape = some tl.f9 := by
  obtain ⟨tl', ht', e1, e2, e3, -⟩ := place_digits hx
  have e : tl' = tl := Option.some.inj (ht'.symm.trans ht)
  rw [e] at e1 e2 e3
  refine shape_of_made (p := P.ofPlace set true x) ?_
  show _root_.Fo.ShapeOf x.calls x.pub x.lid tl.f9
  rw [e1, e2, e3]
  exact shapeZ_at Z ht

/-- **The field that digAt lays anew is the plan's own: digAt hands on what tlAt returns.** -/
theorem digAt_is {X : Verify.Public} (Z : ShapeZAll X) {i : ℕ} {x : Place} {tl : HTailF2}
    (h : digAt X i = some (x, tl)) : tlAt X i = some tl := by
  unfold digAt at h
  obtain ⟨x', hx', h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨tl', ht', h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨s, hs, h⟩ := Option.map_eq_some_iff.1 h
  rw [digits_shape_at Z hx' ht' (Params.settingOf X.P.frame)] at hs
  obtain rfl := Option.some.inj hs
  obtain ⟨-, rfl⟩ := Prod.mk.inj h
  exact ht'

/-- tlAt at a layers' link, by the group's number. -/
theorem tlAt_lay {X : Verify.Public} {g : ℕ} {hp : Layer.HPlan2} (hg : X.G[g]? = some hp)
    (hn : g ≠ X.NGr) : tlAt X ((if X.p4 then 2 else 1) * g) = some hp.tl := by
  have hs : 0 < (if X.p4 then 2 else 1 : ℕ) := by
    split <;> decide
  have h1 : (((if X.p4 then 2 else 1 : ℕ) * g == (if X.p4 then 2 else 1) * X.NGr) = false) := by
    rw [beq_eq_false_iff_ne]
    intro e
    exact hn (Nat.eq_of_mul_eq_mul_left hs e)
  have h2 : ((((if X.p4 then 2 else 1 : ℕ) * g) % (if X.p4 then 2 else 1) == 0) = true) := by
    rw [Nat.mul_mod_right]
    rfl
  have h3 : ((if X.p4 then 2 else 1 : ℕ) * g) / (if X.p4 then 2 else 1) = g :=
    Nat.mul_div_cancel_left g hs
  unfold tlAt
  simp only [h1, h2, h3, hg, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- tlAt at the head's link. -/
theorem tlAt_head (X : Verify.Public) :
    tlAt X ((if X.p4 then 2 else 1) * X.NGr) = some X.H.tl := by
  unfold tlAt
  simp only [beq_self_eq_true, ↓reduceIte]

/-- At a layers' link. -/
theorem digits_shape_lay {X : Verify.Public} (Z : ShapeZAll X) {g : ℕ} {hp : Layer.HPlan2}
    (hg : X.G[g]? = some hp) (hn : g ≠ X.NGr) {xd : Place}
    (hx : lookAt X ((if X.p4 then 2 else 1) * g) true = some xd) (set : Params.Setting) :
    (P.ofPlace set true xd).shape = some hp.tl.f9 :=
  digits_shape_at Z hx (tlAt_lay hg hn) set

/-- At the head's link. -/
theorem digits_shape_head {X : Verify.Public} (Z : ShapeZAll X) {xd : Place}
    (hx : lookAt X ((if X.p4 then 2 else 1) * X.NGr) true = some xd) (set : Params.Setting) :
    (P.ofPlace set true xd).shape = some X.H.tl.f9 :=
  digits_shape_at Z hx (tlAt_head X) set

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.place_digits
#print axioms VerifiableInference.Desc.First.Look.digits_shape_at
#print axioms VerifiableInference.Desc.First.Look.digAt_is
#print axioms VerifiableInference.Desc.First.Look.digits_shape_lay
#print axioms VerifiableInference.Desc.First.Look.digits_shape_head
