-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/RowsAll.lean: the members of a list.

What is here. Groups 4 to 6 of the layers' own rounds (sub-protocol K4): every member of the list
`rowsForms` (OnBytes/Desc/First/K4/Claims.lean) is one of some norm's 21 forms. It is
`rowsForms_mem` (OnBytes/Desc/First/K4/RowsLaws.lean) read from right to left. Statements and
proofs.

  `mapM_get_inv`, `mapM_range_inv`   member i of a list made by mapM is made of member i.
  **`rowsForms_all`**   each member is one of the four claims on the shown end values, of the nine
                      carries or of the eight lines of a norm below NI, whose digits are there at
                      both token points.

Not shown here. What a form is worth: membership in a list alone. That the list is there anywhere:
the statement starts from its return.
No property is claimed.
-/
import OnBytes.Desc.First.K4.RowsLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Heard epsOf twoM)
open OnBytes.Desc.First
open OnBytes.Desc.First.K4 (rowsForms digitsAt mapM_range_get)

theorem mapM_get_inv {α β : Type} (f : α → Option β) : ∀ (xs : List α) (L : List β),
    xs.mapM f = some L → ∀ (i : Nat) (b : β), L[i]? = some b →
      ∃ a, xs[i]? = some a ∧ f a = some b
  | [], L, h, i, b, hb => by
    rw [List.mapM_nil] at h
    obtain rfl : [] = L := Option.some.inj h
    simp at hb
  | x :: xs, L, h, i, b, hb => by
    rw [List.mapM_cons] at h
    obtain ⟨c, hc, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cs, hcs, h2⟩ := Option.bind_eq_some_iff.mp h1
    obtain rfl : c :: cs = L := Option.some.inj h2
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
      subst hb
      exact ⟨x, by simp, hc⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hb
      obtain ⟨a, ha, hfa⟩ := mapM_get_inv f xs cs hcs j b hb
      exact ⟨a, by simpa using ha, hfa⟩

theorem mapM_range_inv {β : Type} (f : Nat → Option β) {n : Nat} {L : List β}
    (h : (List.range n).mapM f = some L) {i : Nat} {b : β} (hb : L[i]? = some b) :
    i < n ∧ f i = some b := by
  obtain ⟨a, ha, hfa⟩ := mapM_get_inv f _ L h i b hb
  obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.mp ha
  rw [List.getElem_range] at e
  subst e
  exact ⟨by simpa using hi, hfa⟩

/-- **Every member of the list is one of some norm's 21 forms.** Dr, Dp: the norm's digits at the
token sumcheck's end point and at the norms' token point. -/
theorem rowsForms_all {v : Env} {H : Heard} {l : List Aff} (h : rowsForms v H = some l) {f : Aff}
    (hf : f ∈ l) :
    ∃ i, i < v.y.NI ∧ ∃ Dr Dp, digitsAt v "r_tV" i = some Dr ∧ digitsAt v "P_V" i = some Dp ∧
      (f ∈ ([(P6.Row.ofDigits Dr).a, (P6.Row.ofDigits Dr).b, (P6.Row.ofDigits Dr).Rlo,
          (P6.Row.ofDigits Dr).Rhi].zipIdx.map fun x =>
            Aff.slot (H.tV.sEnd + 4 * i + x.2) - x.1) ∨
        f ∈ P6.carries (P6.Row.ofDigits Dp) Dp (fun s => Aff.slot (H.sW + 9 * i + s)) ∨
        f ∈ P6.lines (P6.Row.ofDigits Dp) (fun j => Aff.slot (H.sPv + 7 * i + j)) (epsOf v.y i)
          (twoM v i)) := by
  unfold rowsForms at h
  obtain ⟨ends, a1, h1⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Ds, a2, h2⟩ := Option.bind_eq_some_iff.mp h1
  have e := (Option.some.inj h2).symm
  rw [e] at hf
  have drOf : ∀ i, i < v.y.NI → ∃ Dr, digitsAt v "r_tV" i = some Dr := by
    intro i hi
    obtain ⟨b, hb, _⟩ := mapM_range_get _ a1 hi
    obtain ⟨Dr, hDr, _⟩ := Option.map_eq_some_iff.mp hb
    exact ⟨Dr, hDr⟩
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨b, hb, hfb⟩ := List.mem_flatten.mp hf
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hb
      obtain ⟨hn, hbi⟩ := mapM_range_inv _ a1 hi
      obtain ⟨Dr, hDr, eb⟩ := Option.map_eq_some_iff.mp hbi
      obtain ⟨Dp, hDp, _⟩ := mapM_range_get _ a2 hn
      refine ⟨i, hn, Dr, Dp, hDr, hDp, Or.inl ?_⟩
      rw [← eb] at hfb
      exact hfb
    · obtain ⟨b, hb, hfb⟩ := List.mem_flatten.mp hf
      obtain ⟨⟨Dp, i⟩, hx, rfl⟩ := List.mem_map.mp hb
      obtain ⟨hn, hDp⟩ := mapM_range_inv _ a2 (List.mem_zipIdx_iff_getElem?.mp hx)
      obtain ⟨Dr, hDr⟩ := drOf i hn
      exact ⟨i, hn, Dr, Dp, hDr, hDp, Or.inr (Or.inl hfb)⟩
  · obtain ⟨b, hb, hfb⟩ := List.mem_flatten.mp hf
    obtain ⟨⟨Dp, i⟩, hx, rfl⟩ := List.mem_map.mp hb
    obtain ⟨hn, hDp⟩ := mapM_range_inv _ a2 (List.mem_zipIdx_iff_getElem?.mp hx)
    obtain ⟨Dr, hDr⟩ := drOf i hn
    exact ⟨i, hn, Dr, Dp, hDr, hDp, Or.inr (Or.inr hfb)⟩

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.mapM_get_inv
#print axioms OnBytes.Road.K4.W.mapM_range_inv
#print axioms OnBytes.Road.K4.W.rowsForms_all
