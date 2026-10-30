-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FixEntries.lean: A FORM THAT FITS STILL FITS, IN ITS SHAPE, WITH ITS LOW
VARIABLES FIXED: THE SINGLE ENTRIES' HALF. Form.fixLow (OnBytes/Iop/Tensor.lean) moves a single
entry to the index that its higher bits give, and adds up the entries that then have one index
(mergeEntries): so every index of the result is some old index divided by 2 ^ (the number of
coordinates fixed). With the library's half on the tensors (Form.fixLow_shape,
OnBytes/Iop/FixLaws.lean): CFits (Johnson/Desc/Means/Shape.lean) of the result, whole; and the same
at what the program's fold hands on (foldOutput).

Main names (namespace Johnson.Prover.Link).
  mem_mergeLoop, mem_mergeEntries   every index behind the adding up is an index in front of it.
  entries_fixLow_lt   THE ENTRIES: below 2 ^ n, if they were below 2 ^ (the coordinates' number +
    n).
  cfits_fixLow   CFits n (f.fixLow g times) from f.fits (g.length + n).
  cfits_foldOutput   the same of the form on the main row behind the program's fold, from the
    program's own test of the row's sizes (foldRowOk).

By: mergeEntries_eq, mergeStep, Form.fixLow_shape (OnBytes/Iop/FixLaws.lean) · fits_tensors,
fits_of_foldRowOk (OnBytes/Slice/BlkProxFold.lean) · foldOutput_c (OnBytes/Slice/BlkFoldVec.lean).

Limits. On indices and numbers of variables alone: nothing on a coefficient's value. Not Form.fits
of the result (that each slice lies inside its vector is not shown here).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Means.Shape
import OnBytes.Iop.FixLaws
import OnBytes.Slice.BlkProxFold

set_option autoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun

/-- The loop of mergeEntries makes no new index. -/
theorem mem_mergeLoop : ∀ (l acc : List (Nat × E)) (e : Nat × E), e ∈ l.foldl mergeStep acc →
    (∃ a ∈ acc, a.1 = e.1) ∨ ∃ a ∈ l, a.1 = e.1
  | [], _, e, h => Or.inl ⟨e, h, rfl⟩
  | a :: l, acc, e, h => by
    rcases mem_mergeLoop l (mergeStep acc a) e h with ⟨x, hx, hxe⟩ | ⟨x, hx, hxe⟩
    · cases acc with
      | nil =>
        obtain rfl : x = a := List.mem_singleton.1 hx
        exact Or.inr ⟨x, List.mem_cons_self, hxe⟩
      | cons b r =>
        by_cases hab : (a.1 == b.1) = true
        · have hx' : x ∈ (b.1, addE b.2 a.2) :: r := by
            simpa only [mergeStep, hab, if_true] using hx
          rcases List.mem_cons.1 hx' with rfl | hr
          · exact Or.inl ⟨b, List.mem_cons_self, hxe⟩
          · exact Or.inl ⟨x, List.mem_cons_of_mem _ hr, hxe⟩
        · have hx' : x ∈ a :: b :: r := by
            simpa only [mergeStep, hab, Bool.false_eq_true, if_false] using hx
          rcases List.mem_cons.1 hx' with rfl | hr
          · exact Or.inr ⟨x, List.mem_cons_self, hxe⟩
          · exact Or.inl ⟨x, hr, hxe⟩
    · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hxe⟩

/-- Every index behind the adding up is an index in front of it. -/
theorem mem_mergeEntries (l : List (Nat × E)) (e : Nat × E) (h : e ∈ mergeEntries l) :
    ∃ a ∈ l, a.1 = e.1 := by
  rw [mergeEntries_eq] at h
  rcases mem_mergeLoop _ [] e (List.mem_reverse.1 h) with ⟨_, hx, _⟩ | ⟨x, hx, hxe⟩
  · exact (List.not_mem_nil hx).elim
  · exact ⟨x, (List.mergeSort_perm _ _).mem_iff.1 hx, hxe⟩

/-- **The single entries behind fixLow.** -/
theorem entries_fixLow_lt (f : Form) (g : List E) (times : E) (n : Nat)
    (h : ∀ e ∈ f.entries, e.1 < 2 ^ (g.length + n)) :
    ∀ e ∈ (f.fixLow g times).entries, e.1 < 2 ^ n := by
  intro e he
  obtain ⟨a, ha, hae⟩ := mem_mergeEntries _ e he
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
  rw [← hae]
  show b.1 / 2 ^ g.length < 2 ^ n
  refine Nat.div_lt_of_lt_mul ?_
  rw [← Nat.pow_add]
  exact h b hb

/-- **A form that fits, with its low variables fixed, has the shape.** -/
theorem cfits_fixLow (f : Form) (g : List E) (times : E) (n : Nat)
    (h : f.fits (g.length + n) = true) : OnBytes.Means.CFits n (f.fixLow g times) := by
  refine ⟨fun v hv => ?_, entries_fixLow_lt f g times n fun e he => ?_⟩
  · rw [(Form.fixLow_shape f g times _ (fits_tensors f _ h) v hv).1, Nat.add_sub_cancel_left]
  · unfold Form.fits at h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact h.2 e he

/-- **The form on the main row behind the program's fold has the shape.** -/
theorem cfits_foldOutput (S : Statement) (F : FoldShape) (row : GroupRow) (o : ℕ) (eps : E)
    (gamma : List E) (claim : E) (hg : gamma.length = F.layout.k)
    (hr : foldRowOk S F row = true) :
    OnBytes.Means.CFits (ceilLog2 (S.codes.base.getD F.code default).ell)
      (foldOutput S F row o eps gamma claim).c := by
  rw [foldOutput_c]
  refine cfits_fixLow row.c gamma eps _ ?_
  rw [hg]
  exact fits_of_foldRowOk S F row hr

end Johnson.Prover.Link
