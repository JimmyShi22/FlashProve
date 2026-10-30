--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/HotIs.lean: group 10 of the claims of the layers' own rounds: in a world in which
the reads are true, THE FORM AT PLACE lm IS WORTH THE IDENTITY (J10) OF THE ROUTED LAYER lm,
EXTENDED OVER THE POSITIONS, AT THE POINT. An equation, form by form, by place.

Statements and proofs. No new argument: `Fits.hot` (Johnson/Road/FormsKeysIdnL.lean),
`fits_of_laid` (Johnson/Road/FormsKeysFits.lean), `mapM_range_get`
(OnBytes/Desc/First/K4/RowsLaws.lean).

Why. The identity (J10), "the selector's entries of a routed layer sum to 1 at every position", is
tested at a point that the lookup draws, not the layers' own rounds. Whoever counts the bad points
for it counts them for the identity as an array on the cube. What the layers' own rounds owe is
that the form which their text lays IS that array's extension at the point, where the reads are
true; and that the array reads the selector's cells alone.

  `oneHotForms_length`: the list has v.y.LamM forms.
  `hot_form_is`: under `Fits`: the list has D.ne forms, and the form at place lm is worth
    `ext D.lT (d10 D t lm) u`. (`d10`, Inst/Model/FF/Objects.lean: the defect of (J10); it is what
    `layer_start_base`, Johnson/Road/Rows/LayerStart.lean, asks to be 0 in its premise `hHot`.)
  `hot_form_is_laid`: the same with `Fits` taken apart by `fits_of_laid`; the cells are
    `cellsOf D c`.
  `hot_zero_iff`: every form of the list is worth 0 just if all D.ne extensions vanish at the point.
  `hot_forms_zero_of_cube`: if (J10) holds at every routed layer and every position below 2 ^ D.lT,
    every form of the list is worth 0: so that premise of a law on this group CAN hold.
  `d10_congr`: `d10` reads the cells of the array `sel` alone.

Limits. IDENTITIES IN ONE WORLD, AT ONE POINT. NOTHING HERE GOES FROM THE POINT TO THE POSITIONS: no
set of bad points is named or counted, and nothing here joins the point u to any tape or draw: u is
a free variable, tied to the world through `Fits` (`Tabs`) alone: the tables named "..@zt" are true
AT u. That the reads are true is a premise. That the list is there (`oneHotForms v = some l`) is a
premise. The environment v is made of no plan here. That the premises of `hot_form_is_laid` hold
together at the layout of a shipped example is not shown here. All positions below 2 ^ D.lT are
meant, padded ones too. In the field: nothing on the integers. No verifier occurs in any statement.
No theorem on a run of `verify-on-bytes` is called; its records `Env` and `Aff` and its pure
function `sumForms` occur.
-/
import Johnson.Road.K4.Says
import Johnson.Road.FormsKeysFits
import OnBytes.Desc.First.K4.RowsLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell d10)
open Blocks (ext)

/-- A list made by mapM is as long as the list that it is made of. -/
theorem mapM_length {α β : Type} (f : α → Option β) : ∀ (xs : List α) (L : List β),
    xs.mapM f = some L → L.length = xs.length
  | [], L, h => by
    rw [List.mapM_nil] at h
    rw [← Option.some.inj h]
    rfl
  | x :: xs, L, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, _, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨bs, hbs, h2⟩ := Option.bind_eq_some_iff.mp h1
    rw [← Option.some.inj h2, List.length_cons, List.length_cons, mapM_length f xs bs hbs]

/-- Group 10 has one form for each routed layer. -/
theorem oneHotForms_length {v : Env} {l : List Aff}
    (h : Desc.First.K4.oneHotForms v = some l) : l.length = v.y.LamM := by
  rw [mapM_length _ _ _ h, List.length_range]

section
variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {v : Env} {c : Cells K}
  {t : Cell → K} {D : Dim} {low u : ℕ → K}

/-- **The form at place lm is worth the identity of the routed layer lm at the point.** -/
theorem hot_form_is [scl : Scl] (F : Fits ρ W v D c t low u) {l : List Aff}
    (h : Desc.First.K4.oneHotForms v = some l) :
    l.length = D.ne ∧
      ∀ lm f, l[lm]? = some f → f.value ρ W = ext D.lT (fun i => d10 D t lm i) u := by
  have hl := oneHotForms_length h
  refine ⟨hl.trans F.LamM, fun lm f hf => ?_⟩
  have hlm : lm < v.y.LamM := by
    rw [← hl]
    exact (List.getElem?_eq_some_iff.mp hf).1
  obtain ⟨b, hb, gb⟩ := Desc.First.K4.mapM_range_get _ h hlm
  obtain ⟨s, hs, eb⟩ := Option.map_eq_some_iff.mp hb
  rw [gb] at hf
  rw [← Option.some.inj hf, ← eb]
  exact F.hot lm hs (fun _ _ => 0) fun _ => 0

/-- Every form of the group is worth 0 just if all the extensions vanish at the point. -/
theorem hot_zero_iff [scl : Scl] (F : Fits ρ W v D c t low u) {l : List Aff}
    (h : Desc.First.K4.oneHotForms v = some l) :
    (∀ f ∈ l, f.value ρ W = 0) ↔ ∀ lm, lm < D.ne → ext D.lT (fun i => d10 D t lm i) u = 0 := by
  obtain ⟨hl, hv⟩ := hot_form_is F h
  constructor
  · intro hz lm hlm
    have hlt : lm < l.length := by rw [hl]; exact hlm
    have g : l[lm]? = some l[lm] := List.getElem?_eq_getElem hlt
    rw [← hv lm _ g]
    exact hz _ (List.getElem_mem hlt)
  · intro hz f hf
    obtain ⟨lm, hlt, e⟩ := List.getElem_of_mem hf
    have g : l[lm]? = some f := by rw [List.getElem?_eq_getElem hlt, e]
    rw [hv lm f g]
    exact hz lm (by rw [← hl]; exact hlt)

/-- The premise "every form of the group is worth 0" can hold: it does where (J10) holds at every
routed layer and every position below 2 ^ D.lT. -/
theorem hot_forms_zero_of_cube [scl : Scl] (F : Fits ρ W v D c t low u) {l : List Aff}
    (h : Desc.First.K4.oneHotForms v = some l)
    (hc : ∀ lm, lm < D.ne → ∀ i, i < 2 ^ D.lT → d10 D t lm i = 0) : ∀ f ∈ l, f.value ρ W = 0 :=
  (hot_zero_iff F h).2 fun lm hlm => Blocks.ext_zero_of_forall (hc lm hlm) u

end

/-- The same as `hot_form_is`, from the verifier's own layout, the switches, the range of the norms'
shifts, sizes that agree with the shape, a reading that takes numerals to numbers, and six families
of tables that are found and are true in the world at the point (low | u). -/
theorem hot_form_is_laid {K : Type} [Field K] {ρ : Reading K} {W : World K} (hρ : Numerals ρ)
    (v : Env) (L : Laid v.y) (S : Switches v.y.h)
    (hK : ∀ lam, lam < 2 ^ v.y.h.ll → 16 ≤ v.sc.kl (v.lay lam) Model.Layer.LK1 ∧
      16 ≤ v.sc.kl (v.lay lam) Model.Layer.LK2)
    {D : Dim} (Z : Sized v.y.h D) (c : Cells K) (low u : ℕ → K)
    (T : Tabs ρ W v v.y.h.lt c low u) {l : List Aff}
    (h : Desc.First.K4.oneHotForms v = some l) :
    l.length = D.ne ∧ ∀ lm f, l[lm]? = some f →
      f.value ρ W = ext D.lT (fun i => d10 D (cellsOf D c) lm i) u :=
  letI : Scl := sclOf v.y.h v.sc v.g v.y.Lam
  hot_form_is (fits_of_laid hρ v L S hK Z c low u T) h

/-- The defect of (J10) reads the cells of the array `sel` alone. -/
theorem d10_congr {K : Type} [Field K] (D : Dim) {t t' : Cell → K}
    (h : ∀ k a j i, t ⟨.sel, k, a, j, i⟩ = t' ⟨.sel, k, a, j, i⟩) (lm i : ℕ) :
    d10 D t lm i = d10 D t' lm i := by
  simp only [d10, Inst.Model.FFSeg.val, h]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.oneHotForms_length
#print axioms OnBytes.Road.K4.hot_form_is
#print axioms OnBytes.Road.K4.hot_zero_iff
#print axioms OnBytes.Road.K4.hot_forms_zero_of_cube
#print axioms OnBytes.Road.K4.hot_form_is_laid
#print axioms OnBytes.Road.K4.d10_congr
