-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkPlain.lean: the row that a batch hands to a fold has no written-out factor.

A form of the program is a list of tensors and single entries. A tensor may carry a written-out
factor, a vector on some of its variables. OnBytes/Slice/BlkFoldVec.lean reads a fold of a form in
the field for forms in which no tensor has such a factor (`PlainForm`). This file shows where that
hypothesis comes from: the block BAT carries the rows of a run to the group's tables and adds them
up, and if no row has a written-out factor, neither has the sum.

Main definition: `PlainRow`: no tensor among a row's terms has a written-out factor, and each of
its whole coefficient vectors is a plain form.
Main theorems: `addToGroupRow_plain`, `combine_plain`, `plainRow_form` (the sample row is plain).

Not claimed. That the rows of a given protocol are plain: that is shown where these rows are read.
Nothing on the coefficients of the sum.
-/
import OnBytes.Iop.Bat
import OnBytes.Slice.BlkFoldVec
import OnBytes.Slice.BlkSend

set_option autoImplicit false

namespace OnBytes.Slice

/-- No tensor among the row's terms has a written-out factor, and each of its whole coefficient
vectors is a plain form. -/
def PlainRow (r : Row) : Prop :=
  (∀ t ∈ r.terms.toList, t.v.denseVars = []) ∧ ∀ f ∈ r.forms.toList, PlainForm f.c

/-! ## Loops that may fail -/

/-- A property that every step of a loop keeps holds at the loop's end. -/
theorem foldlM_keeps {α β : Type} (P : β → Prop) (step : β → α → Option β) :
    ∀ (l : List α) (b b' : β), (∀ a ∈ l, ∀ x y, P x → step x a = some y → P y) → P b →
      l.foldlM step b = some b' → P b'
  | [], b, b', _, hb, h => by
      rw [List.foldlM_nil] at h
      cases h
      exact hb
  | a :: l, b, b', hs, hb, h => by
      rw [List.foldlM_cons] at h
      obtain ⟨y, hy, hrest⟩ := Option.bind_eq_some_iff.1 h
      exact foldlM_keeps P step l y b' (fun a' ha' => hs a' (List.mem_cons_of_mem _ ha'))
        (hs a List.mem_cons_self b y hb hy) hrest

/-! ## The four kinds of parts of a row -/

/-- A coefficient on a single entry keeps the sum plain. -/
theorem addEntryTo_plain (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (o : ℕ)
    (part : Part) (index : ℕ) (coeff : E) (hp : PlainForm acc.c)
    (h : addEntryTo S L x acc o part index coeff = some acc') : PlainForm acc'.c := by
  unfold addEntryTo at h
  -- Each way through the function fails, leaves c as it was, or adds one entry to c, which brings
  -- no tensor.
  repeat' first
    | split at h
    | (dsimp only at h; split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact hp)

/-- A term whose tensor has no written-out factor keeps the sum plain. -/
theorem addTermTo_plain (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (t : Term)
    (ht : t.v.denseVars = []) (hp : PlainForm acc.c) (h : addTermTo S L x acc t = some acc') :
    PlainForm acc'.c := by
  unfold addTermTo at h
  have hv : ∀ pos count value, ((t.v.scale x).insertChoice pos count value).denseVars = [] :=
    insertChoice_denseVars _ ((scale_denseVars t.v x).trans ht)
  -- Each way through the function fails, leaves c as it was, or adds one tensor to c.
  repeat' first
    | split at h
    | (dsimp only at h; split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact hp)
    | (cases h; exact plainForm_add hp (hv _ _ _))

/-- A run of single entries keeps the sum plain. -/
theorem addRunTo_plain (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow) (w : Run)
    (hp : PlainForm acc.c) (h : addRunTo S L x acc w = some acc') : PlainForm acc'.c :=
  foldlM_keeps (fun a : GroupRow => PlainForm a.c) _ _ acc acc'
    (fun _ _ y y' hy hstep => addEntryTo_plain S L x y y' _ _ _ _ hy hstep) hp h

/-- A plain whole coefficient vector keeps the sum plain. -/
theorem addFormTo_plain (S : Statement) (L : GroupLayout) (x : E) (acc acc' : GroupRow)
    (f : MainForm) (hf : PlainForm f.c) (hp : PlainForm acc.c)
    (h : addFormTo S L x acc f = some acc') : PlainForm acc'.c := by
  unfold addFormTo at h
  -- Each way through the function fails, leaves c as it was, or adds a plain form to c.
  repeat' first
    | split at h
    | (dsimp only at h; split at h)
  all_goals first
    | (cases h; done)
    | (cases h; exact hp)
    | (cases h; exact plainForm_addForm hp (plainForm_insertChoice hf _ _ _) x)

/-! ## A whole row, and the batch -/

/-- Making room for the mask table leaves c as it was. -/
theorem ready_c (acc : GroupRow) (L : GroupLayout) : (acc.ready L).c = acc.c := by
  unfold GroupRow.ready
  split <;> rfl

/-- A plain row, carried to the group's tables and added, keeps the sum plain. -/
theorem addToGroupRow_plain (S : Statement) (L : GroupLayout) (row : Row) (x : E)
    (acc acc' : GroupRow) (hr : PlainRow row) (hp : PlainForm acc.c)
    (h : addToGroupRow S L row x acc = some acc') : PlainForm acc'.c := by
  unfold addToGroupRow at h
  simp only [← Array.foldlM_toList] at h
  obtain ⟨a1, h1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a2, h2, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a3, h3, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a4, h4, h⟩ := Option.bind_eq_some_iff.1 h
  have p0 : PlainForm (acc.ready L).c := by
    rw [ready_c]
    exact hp
  have p1 : PlainForm a1.c := foldlM_keeps (fun a : GroupRow => PlainForm a.c) _ _ _ _
    (fun t ht y y' hy hs => addTermTo_plain S L x y y' t (hr.1 t ht) hy hs) p0 h1
  have p2 : PlainForm a2.c := foldlM_keeps (fun a : GroupRow => PlainForm a.c) _ _ _ _
    (fun _ _ y y' hy hs => addEntryTo_plain S L x y y' _ _ _ _ hy hs) p1 h2
  have p3 : PlainForm a3.c := foldlM_keeps (fun a : GroupRow => PlainForm a.c) _ _ _ _
    (fun w _ y y' hy hs => addRunTo_plain S L x y y' w hy hs) p2 h3
  have p4 : PlainForm a4.c := foldlM_keeps (fun a : GroupRow => PlainForm a.c) _ _ _ _
    (fun f hf y y' hy hs => addFormTo_plain S L x y y' f (hr.2 f hf) hy hs) p3 h4
  cases h
  exact p4

/-- A row without terms and without whole coefficient vectors is plain. -/
theorem plainRow_of_empty (r : Row) (ht : r.terms = #[]) (hf : r.forms = #[]) : PlainRow r := by
  unfold PlainRow
  rw [ht, hf]
  exact ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

/-- Adding a multiple of a row that has only single entries and runs brings no term and no whole
coefficient vector. -/
theorem addScaled_written (r other : Row) (x : E) (ht : other.terms = #[])
    (hf : other.forms = #[]) :
    (r.addScaled other x).terms = r.terms ∧ (r.addScaled other x).forms = r.forms := by
  unfold Row.addScaled Row.addRunsScaled
  simp [ht, hf]

/-- The batch of plain rows is plain. -/
theorem combine_plain (S : Statement) (g : ℕ) (input : RunInput) (x : E) (G : GroupRow)
    (hrows : ∀ r ∈ input.rows.toList, PlainRow r) (h : Bat.combine S g input x = some G) :
    PlainForm G.c := by
  unfold Bat.combine at h
  simp only [← Array.foldlM_toList] at h
  obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.1 h
  have inv : PlainForm s.1.c ∧ s.2.1.terms = #[] ∧ s.2.1.forms = #[] :=
    foldlM_keeps (fun s : GroupRow × Row × E => PlainForm s.1.c ∧ s.2.1.terms = #[] ∧
        s.2.1.forms = #[]) _ _ _ _
      (fun r hr y y' hy hstep => by
        obtain ⟨acc, hacc, hy'⟩ := Option.bind_eq_some_iff.1 hstep
        cases hy'
        have hw := addScaled_written y.2.1 { units := r.units, runs := r.runs } y.2.2 rfl rfl
        have hpr : PlainRow { r with units := #[], runs := #[] } := hrows r hr
        exact ⟨addToGroupRow_plain S input.layout _ _ _ _ hpr hy.1 hacc,
          hw.1.trans hy.2.1, hw.2.trans hy.2.2⟩)
      ⟨plainForm_empty, rfl, rfl⟩ hs
  exact addToGroupRow_plain S input.layout _ _ _ _ (plainRow_of_empty _ inv.2.1 inv.2.2) inv.1 h

/-! ## The sample row -/

/-- The sample row is plain. -/
theorem plainRow_form (codes : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed) (answer : ℕ)
    (row : Row) (h : Send.form codes s o seed answer = some row) : PlainRow row := by
  obtain ⟨ht, _, hf⟩ := form_parts codes s o seed answer row h
  have hT : ∀ part, (sendTensor codes s seed.z part).denseVars = [] := fun part => by
    cases part <;> rfl
  refine ⟨fun t hmem => ?_, fun f hmem => ?_⟩
  · rw [ht, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · split at hmem
      · rw [List.mem_singleton.1 hmem]
        exact hT .main
      · exact absurd hmem List.not_mem_nil
    · split at hmem
      · rw [List.mem_singleton.1 hmem]
        exact hT .mask
      · exact absurd hmem List.not_mem_nil
  · rw [hf] at hmem
    exact absurd hmem List.not_mem_nil

end OnBytes.Slice

#print axioms OnBytes.Slice.foldlM_keeps
#print axioms OnBytes.Slice.addEntryTo_plain
#print axioms OnBytes.Slice.addTermTo_plain
#print axioms OnBytes.Slice.addRunTo_plain
#print axioms OnBytes.Slice.addFormTo_plain
#print axioms OnBytes.Slice.ready_c
#print axioms OnBytes.Slice.addToGroupRow_plain
#print axioms OnBytes.Slice.plainRow_of_empty
#print axioms OnBytes.Slice.addScaled_written
#print axioms OnBytes.Slice.combine_plain
#print axioms OnBytes.Slice.plainRow_form
