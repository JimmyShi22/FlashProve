-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LaysRL.lean: what the places "(rec_gamma)" and "LOC" of the linear claim's
shared rounds lay.

Main names: rowsOn_addRowsP, rowsOn_joinP, length_mapM, laysRecW, laysLocW.

What is not claimed. Nothing on what these constraints say of words. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LawRL
import Johnson.Desc.K14.Law.Lays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Ground (addRowP addRowsP addRowsFrom joinP ok)

/-- A constraint more leaves the small record. -/
theorem loc_addRowP (d d' : St) (g : Nat) (row : Row) (h : addRowP d g row = some d') :
    d'.loc = d.loc := by
  unfold addRowP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h; rfl
  · cases h

/-- Constraints added one by one: the group's list has them last, in order; every other group's
list and the small record stay. -/
theorem rowsOn_addRowsFrom (g : Nat) : ∀ (rows : List Row) (d d' : St),
    addRowsFrom g rows d = some d' →
    rowsOn d' g = rowsOn d g ++ rows ∧ (∀ g', g' ≠ g → rowsOn d' g' = rowsOn d g') ∧
      d'.loc = d.loc := by
  intro rows
  induction rows with
  | nil =>
    intro d d' h
    simp only [addRowsFrom, Option.some.injEq] at h
    subst h
    exact ⟨by simp, fun _ _ => rfl, rfl⟩
  | cons row rows ih =>
    intro d d' h
    simp only [addRowsFrom, Option.bind_eq_some_iff] at h
    obtain ⟨d1, h1, h2⟩ := h
    obtain ⟨a, b, c⟩ := ih d1 d' h2
    refine ⟨?_, fun g' hg => ?_, ?_⟩
    · rw [a, rowsOn_addRowP_same d d1 g row h1]; simp
    · rw [b g' hg, rowsOn_addRowP_other d d1 g g' row h1 (Ne.symm hg)]
    · rw [c, loc_addRowP d d1 g row h1]

@[inherit_doc rowsOn_addRowsFrom]
theorem rowsOn_addRowsP (g : Nat) (rows : List Row) (d d' : St)
    (h : addRowsP d g rows = some d') :
    rowsOn d' g = rowsOn d g ++ rows ∧ (∀ g', g' ≠ g → rowsOn d' g' = rowsOn d g') ∧
      d'.loc = d.loc := by
  unfold addRowsP at h
  split at h
  · exact rowsOn_addRowsFrom g rows d d' h
  · cases h

/-- A message that joins a group: every group's list and the small record stay. -/
theorem rowsOn_joinP (d d' : St) (g o : Nat) (kept : Bool) (h : joinP d g o kept = some d') :
    (∀ g', rowsOn d' g' = rowsOn d g') ∧ d'.loc = d.loc := by
  unfold joinP at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨G, _, rfl⟩ := h
    refine ⟨fun g' => ?_, rfl⟩
    simp only [rowsOn, withMessageInGroup, Array.getElem?_modify]
    split
    · cases d.st.groups[g']? <;> rfl
    · rfl
  · cases h

/-- A list made item by item is as long as the list that it is made of. -/
theorem length_mapM {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β),
    l.mapM f = some r → r.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro r h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | cons a l ih =>
    intro r h
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, _, bs, hbs, rfl⟩ := h
    simp [ih bs hbs]

/-- **LAYS**, for (rec_gamma). -/
theorem laysRecW : LaysRecW := by
  intro p d d' rs h
  unfold laysRec at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨u0, hg, d1, hj, rows, hm, ha⟩ := h
  have hok : ok (laysRecL p d.loc) = true := by
    by_contra hne
    simp [guard, hne] at hg
  obtain ⟨j1, j2⟩ := rowsOn_joinP d d1 _ _ _ hj
  obtain ⟨a, b, c⟩ := rowsOn_addRowsP _ rows d1 d' ha
  exact ⟨hok, c.trans j2, rows, hm, by rw [a, j1], fun g hg => by rw [b g hg, j1]⟩

/-- **LAYS**, for (loc_x). -/
theorem laysLocW : LaysLocW := by
  intro p d d' r cols h
  unfold loc at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨rows, hm, ha⟩ := h
  obtain ⟨a, b, c⟩ := rowsOn_addRowsP _ rows d d' ha
  refine ⟨c, rows, hm, ?_, a, b⟩
  rw [length_mapM _ _ _ hm, List.length_map]

end Desc.K14.Law
