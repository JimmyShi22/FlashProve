-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsScope.lean: TESTS UNDER `k4_own_end` (Johnson/Road/K4/K4PinsEnd.lean) THAT ARE
NO TESTS: they follow from `publicOf`'s return and four lines on the public parameters X at a
layers' segment m: `WorthTies`' five fields on X (Johnson/Road/K4/K4PinsEndFill.lean) and `PlaceIs`
(Johnson/Road/K4/K4PinsPlanes.lean). THE PLACE x IS MADE, NOT ASKED: there is one, and it bears the
segment's number as its link. By unfolding, and calls of the lookup's authors' lemmas
(Johnson/Desc/First/Look/K3CallerAtPlan.lean, K3CallerMasksLaw.lean, K3PlaceLetters.lean). No draw,
no count.

THE FOUR LINES (as another file draws them in the goals' scope): hn: m is not the head's
link · h0: m is a multiple of the number of links a group has · hplan: X's plan of group number
m / that number is hp · (for `attAt`) m is even.

  `attAt_even`: at an even m attention has no place.
  `lookAt_plan`: `lookAt X m false` finds a place, whose link is m.
  **`layAt_plan`**: `layAt X m` finds a place x, with: x.link = m · x.fs = X.y.fo · x.lm = X.y.h.lmb
    · x.F.next = 0 · x.ns = hp.ns.
  `tlAt_plan`: `tlAt X m = some hp.tl`.
  **`ties_of_plan`**: there is a place x with x.link = m, `PlaceIs x p 0`, and `WorthTies X L p m
    x`: from the lines above at hp := p.hp, "the lookup on the calls stands at piece 2", "p's layout
    is X's", and the two equations on the letter L (its numbers of rows and columns are the
    reference ones).

OBJECT: `layAt X m`. USER: none yet; meant: the assembly of K4's law. LETTERS: pol, KL, layout, X,
m, hp, p, L: free.

Limits. K04_law IS NOT PROVED BY THIS. `publicOf`'s return and the lines on X stay premises. L's two
equations are a choice of the letter L.
-/
import Johnson.Road.K4.K4PinsEndFill
import Johnson.Desc.First.Look.K3PlaceLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes.Model (Verify.publicOf)
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Model.Verify (Public)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc.First.Look (Place lookAt attAt layAt tlAt stepOf lookAt_lay
  lookAt_lay_F first_lay lay_shape)
open VerifiableInference.OnPublicFiles (K3Letters)
open Inst.Model.Layout (kRef hRef)

variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Public} {m : ℕ} {hp : HPlan2}

/-- At an even number attention has no place. -/
theorem attAt_even (h2 : m % 2 = 0) : attAt X m = none := by
  unfold attAt
  rw [if_neg]
  rintro ⟨_, h⟩
  omega

/-- The lookup on the calls has a place at a layers' link, and the place bears the link's number. -/
theorem lookAt_plan (hn : m ≠ (if X.p4 then 2 else 1) * X.NGr)
    (h0 : m % (if X.p4 then 2 else 1) = 0)
    (hplan : X.G[m / (if X.p4 then 2 else 1)]? = some hp) :
    ∃ x, lookAt X m false = some x ∧ x.link = m := by
  unfold lookAt
  dsimp only
  rw [if_neg (by simpa using hn), if_pos (by simpa using h0), hplan]
  exact ⟨_, rfl, rfl⟩

/-- **The place at a layers' segment, with its letters.** -/
theorem layAt_plan (h : Verify.publicOf pol KL layout = .ok X)
    (hn : m ≠ (if X.p4 then 2 else 1) * X.NGr) (h0 : m % (if X.p4 then 2 else 1) = 0)
    (hplan : X.G[m / (if X.p4 then 2 else 1)]? = some hp) :
    ∃ x, layAt X m = some x ∧ x.link = m ∧ x.fs = X.y.fo ∧ x.lm = X.y.h.lmb ∧ x.F.next = 0 ∧
      x.ns = hp.ns := by
  obtain ⟨x, e, hl⟩ := lookAt_plan hn h0 hplan
  obtain ⟨hp', hg', _, e1, e2, _⟩ := lookAt_lay e hn h0
  obtain ⟨hp'', hg'', _, _, en⟩ := lookAt_lay_F e hn h0
  obtain rfl : hp'' = hp := Option.some.inj (hg''.symm.trans hplan)
  refine ⟨x, ?_, hl, e1, e2, first_lay h e hn h0, en⟩
  unfold layAt stepOf
  have hc : (m % (if X.p4 then 2 else 1) == 0 && m != (if X.p4 then 2 else 1) * X.NGr) = true := by
    rw [Bool.and_eq_true]
    exact ⟨beq_iff_eq.2 h0, bne_iff_ne.2 hn⟩
  rw [if_pos hc, e]
  show ((VerifiableInference.Desc.First.Look.P.ofPlace
    (OnBytes.Params.settingOf X.P.frame) false x).shape.map fun s => { x with fs := s }) = some x
  rw [lay_shape _ h e hn h0]
  rfl

/-- The smallness test's structure at a layers' segment is the group's plan's. -/
theorem tlAt_plan (hn : m ≠ (if X.p4 then 2 else 1) * X.NGr)
    (h0 : m % (if X.p4 then 2 else 1) = 0)
    (hplan : X.G[m / (if X.p4 then 2 else 1)]? = some hp) : tlAt X m = some hp.tl := by
  obtain ⟨x, e, _⟩ := lookAt_plan hn h0 hplan
  obtain ⟨hp', hg', ht, _⟩ := lookAt_lay e hn h0
  obtain rfl : hp' = hp := Option.some.inj (hg'.symm.trans hplan)
  exact ht

/-- **The place is made; `PlaceIs` and `WorthTies` hold of it.** -/
theorem ties_of_plan {Cells Tok : Type} (L : K3Letters Cells Tok) (p : Par)
    (h : Verify.publicOf pol KL layout = .ok X) (hn : m ≠ (if X.p4 then 2 else 1) * X.NGr)
    (h0 : m % (if X.p4 then 2 else 1) = 0)
    (hplan : X.G[m / (if X.p4 then 2 else 1)]? = some p.hp) (h2 : m % 2 = 0)
    (hpc : VerifiableInference.Desc.K3.pieceAt X m false = 2) (hy : p.P.y = X.y)
    (hr : L.nr = hRef) (hc : L.nc = 2 ^ kRef) :
    ∃ x : Place, x.link = m ∧ x.ns = p.hp.ns ∧ PlaceIs x p 0 ∧ WorthTies X L p m x := by
  obtain ⟨x, hx, hl, e1, e2, e3, en⟩ := layAt_plan h hn h0 hplan
  exact ⟨x, hl, en, ⟨by rw [e1, hy], by rw [e2, hy], e3⟩,
    ⟨attAt_even h2, hx, tlAt_plan hn h0 hplan, hpc, hr, hc, hy⟩⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.attAt_even
#print axioms OnBytes.Road.K4.lookAt_plan
#print axioms OnBytes.Road.K4.layAt_plan
#print axioms OnBytes.Road.K4.tlAt_plan
#print axioms OnBytes.Road.K4.ties_of_plan
