-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkNoKept.lean: the batching on a group without kept members makes no form on a kept
member.

A row on a group has, beside its two tables, a list of forms on the main tables of kept members
(OnBytes/Iop/Ground.lean: `GroupRow.kept`). This file shows that the list stays empty if the
group's layout has no kept member.

Main theorems: `addTermTo_noKept`, `addEntryTo_noKept`, `addFormTo_noKept`,
`addToGroupRow_noKept`, `combine_noKept`.
Not claimed. Nothing on the two tables. Nothing on soundness.
-/
import OnBytes.Iop.RowLaws
import OnBytes.Slice.BlkRead

set_option autoImplicit false

namespace OnBytes.Slice

section
variable (S : Statement) (L : GroupLayout) (hL : ∀ i, L.kept.getD i false = false)
include hL

/-- Carrying a structured vector leaves the forms on kept members as they were. Here and in the
next three theorems the layout has no kept member (`hL`). -/
theorem addTermTo_noKept (x : E) (acc acc' : GroupRow) (t : Term)
    (h : addTermTo S L x acc t = some acc') : acc'.kept = acc.kept := by
  unfold addTermTo at h
  simp only [hL, Bool.false_eq_true, if_false] at h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | cases h

/-- Carrying a coefficient on a single entry leaves them as they were. -/
theorem addEntryTo_noKept (x : E) (acc acc' : GroupRow) (o : ℕ) (part : Part) (index : ℕ)
    (coeff : E) (h : addEntryTo S L x acc o part index coeff = some acc') :
    acc'.kept = acc.kept := by
  unfold addEntryTo at h
  simp only [hL, Bool.false_eq_true, if_false] at h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | cases h

/-- Carrying a whole coefficient vector leaves them as they were. -/
theorem addFormTo_noKept (x : E) (acc acc' : GroupRow) (f : MainForm)
    (h : addFormTo S L x acc f = some acc') : acc'.kept = acc.kept := by
  unfold addFormTo at h
  simp only [hL, Bool.false_eq_true, if_false] at h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | cases h

/-- Carrying a row leaves them as they were. -/
theorem addToGroupRow_noKept (row : Row) (x : E) (acc acc' : GroupRow)
    (h : addToGroupRow S L row x acc = some acc') : acc'.kept = acc.kept := by
  unfold addToGroupRow at h
  simp only [← Array.foldlM_toList, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨a1, h1, a2, h2, a3, h3, a4, h4, rfl⟩ := h
  have e1 := foldlM_keeps (fun g : GroupRow => g.kept) _
    (fun t b b' hb => addTermTo_noKept S L hL x b b' t hb) _ _ _ h1
  have e2 := foldlM_keeps (fun g : GroupRow => g.kept)
    (fun acc (u : Single) => addEntryTo S L x acc u.oracle u.part u.index u.coeff)
    (fun u b b' hb => addEntryTo_noKept S L hL x b b' _ _ _ _ hb) _ _ _ h2
  have e3 := foldlM_keeps (fun g : GroupRow => g.kept) _
    (fun (w : Run) b b' hb => foldlM_keeps (fun g : GroupRow => g.kept) _
      (fun j c c' hc => addEntryTo_noKept S L hL x c c' _ _ _ _ hc) _ _ _ hb) _ _ _ h3
  have e4 := foldlM_keeps (fun g : GroupRow => g.kept) _
    (fun f b b' hb => addFormTo_noKept S L hL x b b' f hb) _ _ _ h4
  have e0 : (acc.ready L).kept = acc.kept := by
    unfold GroupRow.ready
    split <;> rfl
  dsimp only at e1 e2 e3 e4
  show a4.kept = acc.kept
  rw [e4, e3, e2, e1, e0]

end

/-- The batching on a group without kept members returns a row without a form on a kept member.
The law on the batching that reads a row at one place is used with the reading "0 if the list is
empty, else 1". -/
theorem combine_noKept (S : Statement) (g : ℕ) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (hr : ∀ r ∈ input.rows.toList, RowFits S r)
    (hL : ∀ i, input.layout.kept.getD i false = false) : out.kept = #[] := by
  classical
  have h1 := combine_read rdE S g input x out h (RowFits S) (fun _ a => a)
    (fun _ a => a.structured) (fun _ a => a.fits) hr (fun _ => True)
    (fun a => if a.kept = #[] then (0 : GE) else 1) (fun _ => 0)
    (fun row y acc acc' _ _ ha => by
      refine ⟨trivial, ?_⟩
      dsimp only
      rw [addToGroupRow_noKept S input.layout hL row y acc acc' ha, zero_mul, add_zero])
    (fun _ _ _ => by rw [zero_mul, add_zero]) (fun _ => (add_zero _).symm) trivial
    (if_pos rfl) rfl
  rw [hornerSum_zero _ _ (fun a ha => by
    obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha
    rfl)] at h1
  by_contra hne
  dsimp only at h1
  rw [if_neg hne] at h1
  exact one_ne_zero h1

end OnBytes.Slice

#print axioms OnBytes.Slice.addToGroupRow_noKept
#print axioms OnBytes.Slice.combine_noKept
#print axioms OnBytes.Slice.addTermTo_noKept
#print axioms OnBytes.Slice.addEntryTo_noKept
#print axioms OnBytes.Slice.addFormTo_noKept
