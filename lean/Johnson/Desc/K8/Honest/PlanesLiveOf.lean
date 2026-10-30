-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/PlanesLiveOf.lean: THE SMALLNESS TEST: FROM CONDITIONS ON THE VALUES THAT THE
DIGITS' LOOKUP HAS HEARD TO `planesLive` (Johnson/Desc/K8/Honest/PlanesFew.lean). A definition,
statements and proofs. On plain data: no block, no prover. Lemmas; none of the library's goals.

tl: the smallness test's data; g: what its lookup has heard (tl.heard = some g). BZ: the array of
the counts' bits.
  **`eqTabK_ne`**, **`eqTab_ne`**   no coordinate of a point has the value 0 or 1: then no entry of
      its table of equality weights has the value 0
  `entsE_none`, **`coef_one_run`**   a claim with one run from column 0 on, whose form names no
      entry at the place: its coefficient there is the run's coefficient times the run's weight
  `PlanesGood tl g`   the conditions, by name: the leaves' form names no entry of BZ; eps and the
      leaves' factor are not 0; no coordinate of the two stretches of the points on the planes is 0
      or 1; the two tables are at least as long as BZ has columns
  `four8_one`, `four8_two`, `four8_three`   the three claims on the planes, by their numbers among
      the four
  **`planesLive_of`**   tl.heard = some g and `PlanesGood tl g`: then `planesLive tl` says yes
By: K9L.four8 (Johnson/Desc/First/Batch/Law/K8Four.lean) · Fo.eqTab_val, Fo.rdL_getD
(OnBytes/Tie/Pv/Lookup/Port/FoTwins.lean) · Fo.eqTabK_snoc, Fo.eqTabK_len
(Cb/Pv/Lookup/Forest/FoEq.lean) · Fo.natE_val (OnBytes/Tie/Pv/Lookup/Ends/FoTailBits.lean) ·
gl_two_ne_zero (Cb/Pv/Head/NormGl.lean) · OnBytes.Slice.isZeroE_iff, okE_add.
Limits. `PlanesGood` is a premise: that any state's data meet it is not shown here. Nothing on
`digitsLive`. Nothing on any measure.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.PlanesFew
import Cb.Pv.Head.NormGl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc

theorem step_ne {K : Type} [Field K] (t : List K) (zv : K) (h0 : zv ≠ 0) (h1 : zv ≠ 1)
    (ht : ∀ a ∈ t, a ≠ 0) : ∀ y ∈ Fo.eqTabStepK t zv, y ≠ 0 := by
  intro y hy
  unfold Fo.eqTabStepK at hy
  obtain ⟨a, ha, hy⟩ := List.mem_flatMap.1 hy
  rcases List.mem_cons.1 hy with rfl | hy
  · intro e
    have e' : a * (1 - zv) = 0 := by linear_combination e
    rcases mul_eq_zero.1 e' with h | h
    · exact ht a ha h
    · exact h1 (by linear_combination -h)
  · obtain rfl := List.mem_singleton.1 hy
    exact mul_ne_zero (ht a ha) h0

/-- **No coordinate is 0 or 1: no entry of the table is 0.** -/
theorem eqTabK_ne {K : Type} [Field K] (zs : List K) :
    (∀ z ∈ zs, z ≠ 0 ∧ z ≠ 1) → ∀ y ∈ Fo.eqTabK zs, y ≠ 0 := by
  induction zs using List.reverseRecOn with
  | nil =>
    intro _ y hy
    obtain rfl : y = 1 := List.mem_singleton.1 hy
    exact one_ne_zero
  | append_singleton zs zv ih =>
    intro h y hy
    rw [Fo.eqTabK_snoc] at hy
    exact step_ne _ zv (h zv (by simp)).1 (h zv (by simp)).2
      (ih fun z hz => h z (List.mem_append_left _ hz)) y hy

/-- **The same of the table with code.** -/
theorem eqTab_ne (z : Array E)
    (h : ∀ w ∈ z.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1) (u : Nat)
    (hu : u < 2 ^ z.size) : Reading.gl.val ((eqTab z).getD u zeroE) ≠ 0 := by
  rw [Fo.rdL_getD Reading.gl, Fo.eqTab_val Reading.gl]
  have hlen : u < (Fo.eqTabK (Fo.rdL Reading.gl z)).length := by
    rw [Fo.eqTabK_len]
    unfold Fo.rdL
    rw [List.length_map, Array.length_toList]
    exact hu
  rw [List.getD_eq_getElem _ _ hlen]
  refine eqTabK_ne _ (fun x hx => ?_) _ (List.getElem_mem hlen)
  unfold Fo.rdL at hx
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
  exact h w hw

theorem entsE_none : ∀ (l : List Ent) (t r i : Nat),
    (∀ x ∈ l, ¬ (x.tree = t ∧ x.row = r ∧ x.idx = i)) → entsE l t r i = zeroE
  | [], _, _, _, _ => rfl
  | x :: l, t, r, i, h => by
    have ih := entsE_none l t r i fun y hy => h y (List.mem_cons_of_mem _ hy)
    unfold entsE at ih ⊢
    rw [List.foldr_cons, if_neg (h x List.mem_cons_self)]
    exact ih

/-- **A claim with one run from column 0 on.** -/
theorem coef_one_run (cl : Claim) (R : Run2) (t r i : Nat) (hr : cl.runs = #[R])
    (h1 : R.tree = t) (h2 : R.row = r) (h3 : R.first = 0) (h4 : R.w0 = 0) (hi : i < R.n)
    (he : ∀ x ∈ cl.form.ents.toList, ¬ (x.tree = t ∧ x.row = r ∧ x.idx = i)) :
    Reading.gl.val (coefE cl t r i) =
      Reading.gl.val R.coef * Reading.gl.val (R.w.getD i zeroE) := by
  unfold coefE
  rw [entsE_none _ t r i he, hr]
  show Reading.gl.val (addE zeroE (runsE [R] t r i)) = _
  unfold runsE
  rw [List.foldr_cons, List.foldr_nil, if_pos ⟨h1, h2, by omega, by omega⟩, Reading.gl.add,
    Reading.gl.add, Reading.gl.mul, Reading.gl.zero, h3, h4, Nat.sub_zero, Nat.zero_add]
  ring

/-- The conditions on what the lookup has heard, by name. -/
structure PlanesGood (tl : HTailF2) (g : Forest.Heard) : Prop where
  rowFree : ∀ x ∈ (g.leaves.rowForm oneE {}).ents.toList, x.tree ≠ tl.ix.BZ
  eps : Reading.gl.val g.leaves.eps ≠ 0
  leavesA : Reading.gl.val g.leavesA ≠ 0
  zb0 : ∀ w ∈ (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)).toList,
    Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1
  zb1 : ∀ w ∈ (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)).toList,
    Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1
  wide0 : tl.bzColumns ≤ 2 ^ (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)).size
  wide1 : tl.bzColumns ≤ 2 ^ (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)).size

/-- A coefficient whose value is not 0 is live. -/
theorem liveAt_of_val (cl : Claim) (t r i : Nat) (h : Reading.gl.val (coefE cl t r i) ≠ 0) :
    liveAt cl t r i = true := by
  unfold liveAt
  cases hz : isZeroE (coefE cl t r i) with
  | false => rfl
  | true =>
    exact absurd ((OnBytes.Slice.isZeroE_iff _ (Part.MaskedSum.okE_add _ _)).1 hz) h

/-- The three claims on the planes, by number. -/
theorem four8_one (tl : HTailF2) (g : Forest.Heard) : (K9L.four8 tl g)[1]? = some
    { form := g.leaves.rowForm oneE {},
      runs := #[Fo.bzRun tl 0 (mulE g.leaves.eps g.leavesA)
        (eqTab (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)))] } := rfl

theorem four8_two (tl : HTailF2) (g : Forest.Heard) : (K9L.four8 tl g)[2]? = some
    { form := Aff.slot g.sBit,
      runs := #[Fo.bzRun tl 1 (subE zeroE oneE)
        (eqTab (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)))] } := rfl

theorem four8_three (tl : HTailF2) (g : Forest.Heard) : (K9L.four8 tl g)[3]? = some
    { form := Aff.ofConst (subE zeroE (ofNat (2 ^ tl.f9.v - tl.f9.padding))),
      runs := #[Fo.bzRun tl 2 oneE (Fo.pinW tl)] } := rfl

/-- **The conditions give `planesLive`.** -/
theorem planesLive_of (tl : HTailF2) (g : Forest.Heard) (hg : tl.heard = some g)
    (G : PlanesGood tl g) : planesLive tl = true := by
  unfold planesLive
  rw [hg]
  simp only [List.all_eq_true, List.mem_range]
  intro r hr u hu
  have hr3 : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hr3 with rfl | rfl | rfl
  · have h0 := coef_one_run
      { form := g.leaves.rowForm oneE {},
        runs := #[Fo.bzRun tl 0 (mulE g.leaves.eps g.leavesA)
          (eqTab (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)))] }
      (Fo.bzRun tl 0 (mulE g.leaves.eps g.leavesA)
        (eqTab (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)))) tl.ix.BZ 0 u rfl rfl rfl rfl rfl hu
      (fun x hx h => G.rowFree x hx h.1)
    rw [show (1 + 0 : Nat) = 1 from rfl, four8_one, Option.any_some]
    refine liveAt_of_val _ _ _ _ ?_
    rw [h0]
    show Reading.gl.val (mulE g.leaves.eps g.leavesA) * _ ≠ 0
    rw [Reading.gl.mul]
    exact mul_ne_zero (mul_ne_zero G.eps G.leavesA)
      (eqTab_ne _ G.zb0 u (Nat.lt_of_lt_of_le hu G.wide0))
  · have h0 := coef_one_run
      { form := Aff.slot g.sBit,
        runs := #[Fo.bzRun tl 1 (subE zeroE oneE)
          (eqTab (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)))] }
      (Fo.bzRun tl 1 (subE zeroE oneE)
        (eqTab (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)))) tl.ix.BZ 1 u rfl rfl rfl rfl rfl hu
      (fun x hx _ => by simp [Aff.slot] at hx)
    rw [show (1 + 1 : Nat) = 2 from rfl, four8_two, Option.any_some]
    refine liveAt_of_val _ _ _ _ ?_
    rw [h0]
    show Reading.gl.val (subE zeroE oneE) * _ ≠ 0
    rw [Reading.gl.sub, Reading.gl.zero, Reading.gl.one, zero_sub]
    exact mul_ne_zero (neg_ne_zero.2 one_ne_zero)
      (eqTab_ne _ G.zb1 u (Nat.lt_of_lt_of_le hu G.wide1))
  · have h0 := coef_one_run
      { form := Aff.ofConst (subE zeroE (ofNat (2 ^ tl.f9.v - tl.f9.padding))),
        runs := #[Fo.bzRun tl 2 oneE (Fo.pinW tl)] }
      (Fo.bzRun tl 2 oneE (Fo.pinW tl)) tl.ix.BZ 2 u rfl rfl rfl rfl rfl hu
      (fun x hx _ => by simp [Aff.ofConst] at hx)
    rw [show (1 + 2 : Nat) = 3 from rfl, four8_three, Option.any_some]
    refine liveAt_of_val _ _ _ _ ?_
    rw [h0]
    show Reading.gl.val oneE * Reading.gl.val ((Fo.pinW tl).getD u zeroE) ≠ 0
    rw [Reading.gl.one, one_mul]
    have hp : (Fo.pinW tl).getD u zeroE = ofNat (2 ^ (u % 32)) := by
      unfold Fo.pinW
      simp [Array.getD_eq_getD_getElem?, hu]
    rw [hp, Fo.natE_val Reading.gl]
    push_cast
    exact pow_ne_zero _ Cb.Pv.Head.gl_two_ne_zero

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.eqTabK_ne
#print axioms VerifiableInference.Desc.First.K8.Honest.eqTab_ne
#print axioms VerifiableInference.Desc.First.K8.Honest.coef_one_run
#print axioms VerifiableInference.Desc.First.K8.Honest.planesLive_of
