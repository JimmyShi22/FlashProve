-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkBatVars.lean: each tensor of a batched row has a variable for each row bit of the
group's main table.

The block BAT of the program (the Lean verifier in OnBytes/) carries the rows of a run to the
group's tables and adds them up (OnBytes/Iop/Bat.lean: `Bat.combine`). A tensor on a member's main
table gets new variables, which pick the member's block among the group's rows. So it has at least
as many variables as the group's main table has row bits, if it had at least as many as its own
table has. That is what the laws on the batching ask of a row (OnBytes/Iop/RowLaws.lean: `RowFits`).

Main definition: `RowBitsIn`.
Main theorems: `addToGroupRow_vars`, `combine_vars`.

Not claimed. The exact number of variables. Nothing on the coefficients of the sum.
-/
import OnBytes.Iop.MaskLaws
import OnBytes.Slice.BlkPlain

set_option autoImplicit false

namespace OnBytes.Slice

/-- Each tensor of the form has at least k variables. -/
def RowBitsIn (k : ℕ) (f : Form) : Prop := ∀ v ∈ f.tensors, k ≤ v.vars

/-- The form without a tensor meets every bound. -/
theorem rowBitsIn_empty (k : ℕ) : RowBitsIn k {} := fun _ h => absurd h List.not_mem_nil

/-! ## What the four kinds of parts of a row do to the form on the main table -/

/-- A single entry brings no tensor. -/
theorem addEntryTo_tensors (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (o : ℕ)
    (part : Part) (index : ℕ) (coeff : E)
    (h : addEntryTo S L x acc o part index coeff = some acc') :
    acc'.c.tensors = acc.c.tensors := by
  unfold addEntryTo at h
  -- Each way through the function fails, leaves c as it was, or adds one entry to c.
  repeat' first
    | split at h
    | (dsimp only at h; split at h)
  all_goals first
    | (cases h; done)
    | (cases h; rfl)

/-- A tensor of a row leaves c as it was, or it is added with new variables that fill its table's
row bits up to the group's. -/
theorem addTermTo_c (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (t : Term)
    (h : addTermTo S L x acc t = some acc') :
    acc'.c = acc.c ∨ (S.rowBits t.oracle t.part ≤ L.k ∧ ∃ value, acc'.c = acc.c.add
      ((t.v.scale x).insertChoice (S.rowBits t.oracle t.part)
        (L.k - S.rowBits t.oracle t.part) value)) := by
  unfold addTermTo at h
  repeat' first
    | split at h
    | (dsimp only at h; split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact Or.inl rfl)
    | (cases h; exact Or.inr ⟨by omega, _, rfl⟩)

/-- A whole coefficient vector of a row leaves c as it was, or it is added likewise. -/
theorem addFormTo_c (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (f : MainForm)
    (h : addFormTo S L x acc f = some acc') :
    acc'.c = acc.c ∨ (S.rowBits f.oracle .main ≤ L.k ∧ ∃ value, acc'.c = acc.c.addForm
      (f.c.insertChoice (S.rowBits f.oracle .main) (L.k - S.rowBits f.oracle .main) value) x) := by
  unfold addFormTo at h
  repeat' first
    | split at h
    | (dsimp only at h; split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact Or.inl rfl)
    | (cases h; exact Or.inr ⟨by omega, _, rfl⟩)

/-- A tensor with at least a variables, with k - a more, has at least k. -/
theorem le_vars_filled (v : Tensor) (x : E) (a k value : ℕ) (hv : a ≤ v.vars) (hk : a ≤ k) :
    k ≤ ((v.scale x).insertChoice a (k - a) value).vars := by
  rw [Tensor.vars_insertChoice _ _ _ _ (by rw [Tensor.vars_scale]; exact hv), Tensor.vars_scale]
  omega

/-- A tensor of a row that has a variable for each row bit of its own table keeps the bound. -/
theorem addTermTo_vars (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (t : Term)
    (hv : S.rowBits t.oracle t.part ≤ t.v.vars) (hp : RowBitsIn L.k acc.c)
    (h : addTermTo S L x acc t = some acc') : RowBitsIn L.k acc'.c := by
  rcases addTermTo_c S L x acc acc' t h with e | ⟨hk, value, e⟩
  · rw [e]
    exact hp
  · rw [e]
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw'
    · exact le_vars_filled t.v x _ _ _ hv hk
    · exact hp w hw'

/-- A whole coefficient vector of a row keeps the bound, if each of its tensors has a variable for
each row bit of its own table. -/
theorem addFormTo_vars (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow)
    (f : MainForm) (hv : ∀ v ∈ f.c.tensors, S.rowBits f.oracle .main ≤ v.vars)
    (hp : RowBitsIn L.k acc.c) (h : addFormTo S L x acc f = some acc') :
    RowBitsIn L.k acc'.c := by
  rcases addFormTo_c S L x acc acc' f h with e | ⟨hk, value, e⟩
  · rw [e]
    exact hp
  · rw [e]
    intro w hw
    rcases List.mem_append.1 hw with hw' | hw'
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hw'
      obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hu
      rw [Tensor.vars_scale, Tensor.vars_insertChoice _ _ _ _ (hv v hv')]
      have := hv v hv'
      omega
    · exact hp w hw'

/-! ## A whole row, and the batch -/

/-- A row whose tensors have a variable for each row bit of their own tables, carried to the group's
tables and added, keeps the bound. -/
theorem addToGroupRow_vars (S : Statement) (L : GroupLayout) (row : Row) (x : E)
    (acc acc' : GroupRow)
    (hterms : ∀ t ∈ row.terms.toList, S.rowBits t.oracle t.part ≤ t.v.vars)
    (hforms : ∀ f ∈ row.forms.toList, ∀ v ∈ f.c.tensors, S.rowBits f.oracle .main ≤ v.vars)
    (hp : RowBitsIn L.k acc.c) (h : addToGroupRow S L row x acc = some acc') :
    RowBitsIn L.k acc'.c := by
  unfold addToGroupRow at h
  simp only [← Array.foldlM_toList] at h
  obtain ⟨a1, h1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a2, h2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a3, h3, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a4, h4, h⟩ := Option.bind_eq_some_iff.1 h
  have hentry : ∀ (y y' : GroupRow) (o : ℕ) (part : Part) (index : ℕ) (coeff : E),
      RowBitsIn L.k y.c → addEntryTo S L x y o part index coeff = some y' →
      RowBitsIn L.k y'.c := fun y y' o part index coeff hy hs => by
    unfold RowBitsIn
    rw [addEntryTo_tensors S L x y y' o part index coeff hs]
    exact hy
  have p0 : RowBitsIn L.k (acc.ready L).c := by
    rw [ready_c]
    exact hp
  have p1 : RowBitsIn L.k a1.c := foldlM_keeps (fun a : GroupRow => RowBitsIn L.k a.c) _ _ _ _
    (fun t ht y y' hy hs => addTermTo_vars S L x y y' t (hterms t ht) hy hs) p0 h1
  have p2 : RowBitsIn L.k a2.c := foldlM_keeps (fun a : GroupRow => RowBitsIn L.k a.c) _ _ _ _
    (fun _ _ y y' hy hs => hentry y y' _ _ _ _ hy hs) p1 h2
  have p3 : RowBitsIn L.k a3.c := foldlM_keeps (fun a : GroupRow => RowBitsIn L.k a.c) _ _ _ _
    (fun w _ y y' hy hs => foldlM_keeps (fun a : GroupRow => RowBitsIn L.k a.c) _ _ y y'
      (fun _ _ z z' hz hs' => hentry z z' _ _ _ _ hz hs') hy hs) p2 h3
  have p4 : RowBitsIn L.k a4.c := foldlM_keeps (fun a : GroupRow => RowBitsIn L.k a.c) _ _ _ _
    (fun f hf y y' hy hs => addFormTo_vars S L x y y' f (hforms f hf) hy hs) p3 h4
  cases h
  exact p4

/-- Each tensor of a batched row has at least as many variables as the group's main table has row
bits, if the rows fit. -/
theorem combine_vars (S : Statement) (g : ℕ) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (hr : ∀ r ∈ input.rows.toList, RowFits S r) :
    ∀ v ∈ out.c.tensors, input.layout.k ≤ v.vars := by
  unfold Bat.combine at h
  simp only [← Array.foldlM_toList] at h
  obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.1 h
  -- Through the loop the sum keeps the bound, and the row of written-out parts has no tensor.
  have inv : RowBitsIn input.layout.k s.1.c ∧ s.2.1.terms = #[] ∧ s.2.1.forms = #[] :=
    foldlM_keeps (fun s : GroupRow × Row × E => RowBitsIn input.layout.k s.1.c ∧
        s.2.1.terms = #[] ∧ s.2.1.forms = #[]) _ _ _ _
      (fun r hmem y y' hy hstep => by
        obtain ⟨acc, hacc, hy'⟩ := Option.bind_eq_some_iff.1 hstep
        cases hy'
        have hw := addScaled_written y.2.1 { units := r.units, runs := r.runs } y.2.2 rfl rfl
        exact ⟨addToGroupRow_vars S input.layout { r with units := #[], runs := #[] } _ _ _
          (hr r hmem).terms (hr r hmem).forms hy.1 hacc, hw.1.trans hy.2.1, hw.2.trans hy.2.2⟩)
      ⟨rowBitsIn_empty _, rfl, rfl⟩ hs
  exact addToGroupRow_vars S input.layout _ _ _ _
    (fun t ht => by rw [inv.2.1] at ht; exact absurd ht List.not_mem_nil)
    (fun f hf => by rw [inv.2.2] at hf; exact absurd hf List.not_mem_nil) inv.1 h

end OnBytes.Slice

#print axioms OnBytes.Slice.rowBitsIn_empty
#print axioms OnBytes.Slice.addEntryTo_tensors
#print axioms OnBytes.Slice.addTermTo_c
#print axioms OnBytes.Slice.addFormTo_c
#print axioms OnBytes.Slice.le_vars_filled
#print axioms OnBytes.Slice.addTermTo_vars
#print axioms OnBytes.Slice.addFormTo_vars
#print axioms OnBytes.Slice.addToGroupRow_vars
#print axioms OnBytes.Slice.combine_vars
