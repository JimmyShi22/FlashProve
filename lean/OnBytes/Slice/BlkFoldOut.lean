-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkFoldOut.lean: what is public of the claim that the program's fold hands on.

The program's block FOLD ends with the record `foldOutput` (OnBytes/Iop/Fold.lean). This file says
what its public fields are. The first section reads them off the definition, one lemma for each
field, and does the same for the shape of the fold at a stage (`ioppFoldShape`,
OnBytes/Iop/Prox.lean). The second section gives, from what the program's own tests of the shape and
of the row say, the sizes of the two written-out vectors, the number of variables of the form, and
what is left of kept members (members of the group whose main rows are not folded) where there are
none.

Main theorems.
 `foldOutput_code` to `foldOutput_keptRows`, `ioppFoldShape_code` to `ioppFoldShape_maskFirst`
                 the fields, by definition.
 `of_foldShapeOk`   what the test of the shape says of h, k and the mask code's message length.
 `foldOutput_kept_nil`, `foldOutput_keptRows_zero`, `switchKept_foldOutput`   nothing is kept.
 `size_foldOutput_d0`, `size_foldOutput_d1`   both written-out vectors have the mask code's
                 message length.
 `vars_foldOutput`, `plainForm_foldOutput`   the form on the main row.
 `foldOutput_ok`    seven facts of the second section together.

Not claimed. Nothing on the values of the vectors (OnBytes/Slice/BlkFoldVec.lean) or of the target.
The number of variables is shown for a form without a written-out factor only. Nothing on the run
of the block. Nothing on soundness.
-/
import OnBytes.Slice.BlkFoldVec
import OnBytes.Iop.Cs
import OnBytes.Iop.Prox

set_option autoImplicit false

namespace OnBytes.Slice

open Params (IoppStage)

variable (S : Statement) (F : FoldShape) (row : GroupRow) (o : ℕ) (eps : E) (gamma : List E)
  (claim : E)

/-! ## The fields, by definition -/

/-- The code of the main row is the shape's. -/
theorem foldOutput_code : (foldOutput S F row o eps gamma claim).code = F.code := rfl

/-- The code of the mask rows is the shape's. -/
theorem foldOutput_maskCode : (foldOutput S F row o eps gamma claim).maskCode = F.maskCode := rfl

/-- The layout is the shape's. -/
theorem foldOutput_layout : (foldOutput S F row o eps gamma claim).layout = F.layout := rfl

/-- The challenges are those of the rounds. -/
theorem foldOutput_gamma : (foldOutput S F row o eps gamma claim).gamma = gamma := rfl

/-- There are two mask rows: the old one and the fresh one. -/
theorem foldOutput_masks : (foldOutput S F row o eps gamma claim).masks = 2 := rfl

/-- The fresh mask is the oracle message that was named. -/
theorem foldOutput_fresh : (foldOutput S F row o eps gamma claim).fresh = o := rfl

/-- The target is the running claim. -/
theorem foldOutput_target : (foldOutput S F row o eps gamma claim).target = claim := rfl

/-- The forms on kept members are the row's, each times one factor. -/
theorem foldOutput_kept : (foldOutput S F row o eps gamma claim).kept =
    row.kept.map fun f => { f with c := f.c.scale (foldKeptFactor eps gamma) } := rfl

/-- The main rows of the kept members, counted member by member. -/
theorem foldOutput_keptRows : (foldOutput S F row o eps gamma claim).keptRows =
    (List.range F.layout.members.size).foldl (fun n i =>
      if F.layout.kept.getD i false then
        n + ((S.oracles[F.layout.members.getD i noId]?).map (·.shape.mainRows)).getD 0
      else n) 0 := rfl

section Stage
variable (s : IoppStage) (L : GroupLayout)

/-- The fold at a stage has the stage's code. -/
theorem ioppFoldShape_code : (ioppFoldShape s L).code = s.code := rfl

/-- The fold at a stage has the stage's mask code. -/
theorem ioppFoldShape_maskCode : (ioppFoldShape s L).maskCode = s.maskCode := rfl

/-- The layout of the fold at a stage is the given one with the stage's k and h. -/
theorem ioppFoldShape_layout : (ioppFoldShape s L).layout = { L with k := s.k, h := s.h } := rfl

/-- The number of row variables is the stage's. -/
theorem ioppFoldShape_k : (ioppFoldShape s L).layout.k = s.k := rfl

/-- The number of mask row variables is the stage's. -/
theorem ioppFoldShape_h : (ioppFoldShape s L).layout.h = s.h := rfl

/-- The members are the given layout's. -/
theorem ioppFoldShape_members : (ioppFoldShape s L).layout.members = L.members := rfl

/-- Which members are kept is as in the given layout. -/
theorem ioppFoldShape_kept : (ioppFoldShape s L).layout.kept = L.kept := rfl

/-- Where the main rows begin is as in the given layout. -/
theorem ioppFoldShape_mainFirst : (ioppFoldShape s L).layout.mainFirst = L.mainFirst := rfl

/-- Where the mask rows begin is as in the given layout. -/
theorem ioppFoldShape_maskFirst : (ioppFoldShape s L).layout.maskFirst = L.maskFirst := rfl

end Stage

/-! ## From the program's tests -/

/-- If the program's test of the shape is true, then h ≤ k and the mask code's message length is at
least `foldMaskColumns k h`. -/
theorem of_foldShapeOk (hs : foldShapeOk S F = true) :
    F.layout.h ≤ F.layout.k ∧
      foldMaskColumns F.layout.k F.layout.h ≤ (S.codes.mask.getD F.maskCode default).ell := by
  unfold foldShapeOk at hs
  split at hs
  · rename_i c zk hc hz
    have ez : S.codes.mask.getD F.maskCode default = zk := by
      rw [Array.getD_eq_getD_getElem?, hz]
      rfl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [ez]
    exact ⟨hs.1.1.1.1.1.1.1.2, hs.1.1.1.1.1.2⟩
  · cases hs

/-- A row without forms on kept members hands on none. -/
theorem foldOutput_kept_nil (h0 : row.kept = #[]) :
    (foldOutput S F row o eps gamma claim).kept = #[] := by
  rw [foldOutput_kept, h0]
  exact Array.map_empty

/-- Where no member is kept, no main row of a kept member is counted. -/
theorem foldOutput_keptRows_zero
    (hk : ∀ i, i < F.layout.members.size → F.layout.kept.getD i false = false) :
    (foldOutput S F row o eps gamma claim).keptRows = 0 := by
  rw [foldOutput_keptRows]
  have step : ∀ (l : List ℕ), (∀ i ∈ l, i < F.layout.members.size) → ∀ n : ℕ, l.foldl (fun n i =>
      if F.layout.kept.getD i false then
        n + ((S.oracles[F.layout.members.getD i noId]?).map (·.shape.mainRows)).getD 0
      else n) n = n := by
    intro l
    induction l with
    | nil => intro _ n; rfl
    | cons i l ih =>
      intro hl n
      rw [List.foldl_cons, hk i (hl i List.mem_cons_self)]
      exact ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) n
  exact step _ (fun i hi => List.mem_range.1 hi) 0

/-- Where no member is kept, the switch after the fold finds no kept member. -/
theorem switchKept_foldOutput
    (hk : ∀ i, i < F.layout.members.size → F.layout.kept.getD i false = false) :
    switchKept (foldOutput S F row o eps gamma claim) = #[] := by
  unfold switchKept
  rw [foldOutput_layout]
  have hf : (F.layout.members.zip F.layout.kept).filter (·.2) = #[] := by
    rw [Array.filter_eq_empty_iff]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
    rw [Array.size_zip] at hi
    have hi2 : i < F.layout.kept.size := by omega
    have e := hk i (by omega)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi2] at e
    rw [Array.getElem_zip]
    simpa using e
  rw [hf]
  exact Array.map_empty

/-- The form on the carried mask row has the message length of the mask code. -/
theorem size_foldOutput_d0 (hg : gamma.length = F.layout.k) (hr : foldRowOk S F row = true)
    (hhk : F.layout.h ≤ F.layout.k) :
    ((foldOutput S F row o eps gamma claim).d.getD 0 #[]).size =
      (S.codes.mask.getD F.maskCode default).ell := by
  have hlen : (gamma.take F.layout.h).length = F.layout.h := by
    rw [List.length_take, hg]
    exact Nat.min_eq_left hhk
  rw [foldOutput_d]
  show (foldMaskForm F.layout.h row.d eps gamma).size = _
  rw [foldMaskForm_def, Array.size_map, size_foldLowB, hlen, (of_foldRowOk S F row hr).2,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- The list of weights `weightsL h n g` has h + 2 n + 1 members: as many as the table of the hiding
polynomial's coefficients has columns (`foldMaskColumns (h + n) h`). -/
theorem length_weightsL (h n : ℕ) (g : Array E) : (weightsL h n g).length = h + 2 * n + 1 := by
  unfold weightsL layL
  rw [List.length_append, List.length_cons, List.length_map, List.length_range, List.length_append,
    length_midL]
  by_cases hn : 0 < n
  · rw [if_pos hn, List.length_singleton]
    omega
  · rw [if_neg hn, List.length_nil]
    omega

/-- The weights on the fresh mask row have the message length of the mask code. -/
theorem size_foldOutput_d1 (hhk : F.layout.h ≤ F.layout.k)
    (hcol : foldMaskColumns F.layout.k F.layout.h ≤ (S.codes.mask.getD F.maskCode default).ell) :
    ((foldOutput S F row o eps gamma claim).d.getD 1 #[]).size =
      (S.codes.mask.getD F.maskCode default).ell := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hhk
  rw [foldOutput_d]
  show (foldMaskWeights F.layout.k F.layout.h (S.codes.mask.getD F.maskCode default).ell
    gamma.toArray).size = _
  unfold foldMaskColumns at hcol
  rw [hn] at hcol ⊢
  rw [foldMaskWeights_eq, List.size_toArray, List.length_append, List.length_replicate,
    length_weightsL]
  omega

/-- Every tensor of the form on the main row has the variables of one message of the code. -/
theorem vars_foldOutput (hg : gamma.length = F.layout.k) (hr : foldRowOk S F row = true)
    (hp : PlainForm row.c) : ∀ v ∈ (foldOutput S F row o eps gamma claim).c.tensors,
      v.vars = ceilLog2 (S.codes.base.getD F.code default).ell := by
  rw [foldOutput_c]
  exact vars_fixLow hp gamma eps _ fun v hv => by rw [(of_foldRowOk S F row hr).1 v hv, hg]

/-- The form on the main row has no written-out factor, if the row's form has none. -/
theorem plainForm_foldOutput (hp : PlainForm row.c) :
    PlainForm (foldOutput S F row o eps gamma claim).c := by
  rw [foldOutput_c]
  exact plainForm_fixLow hp gamma eps

/-- What is public of the claim after a fold in which nothing is kept: seven facts together. -/
theorem foldOutput_ok (hg : gamma.length = F.layout.k) (hr : foldRowOk S F row = true)
    (hhk : F.layout.h ≤ F.layout.k)
    (hcol : foldMaskColumns F.layout.k F.layout.h ≤ (S.codes.mask.getD F.maskCode default).ell)
    (hp : PlainForm row.c) (h0 : row.kept = #[])
    (hk : ∀ i, i < F.layout.members.size → F.layout.kept.getD i false = false) :
    (foldOutput S F row o eps gamma claim).kept = #[] ∧
    switchKept (foldOutput S F row o eps gamma claim) = #[] ∧
    (foldOutput S F row o eps gamma claim).keptRows = 0 ∧
    ((foldOutput S F row o eps gamma claim).d.getD 0 #[]).size =
      (S.codes.mask.getD F.maskCode default).ell ∧
    ((foldOutput S F row o eps gamma claim).d.getD 1 #[]).size =
      (S.codes.mask.getD F.maskCode default).ell ∧
    (∀ v ∈ (foldOutput S F row o eps gamma claim).c.tensors,
      v.vars = ceilLog2 (S.codes.base.getD F.code default).ell) ∧
    PlainForm (foldOutput S F row o eps gamma claim).c :=
  ⟨foldOutput_kept_nil S F row o eps gamma claim h0,
    switchKept_foldOutput S F row o eps gamma claim hk,
    foldOutput_keptRows_zero S F row o eps gamma claim hk,
    size_foldOutput_d0 S F row o eps gamma claim hg hr hhk,
    size_foldOutput_d1 S F row o eps gamma claim hhk hcol,
    vars_foldOutput S F row o eps gamma claim hg hr hp,
    plainForm_foldOutput S F row o eps gamma claim hp⟩

end OnBytes.Slice

#print axioms OnBytes.Slice.of_foldShapeOk
#print axioms OnBytes.Slice.foldOutput_kept_nil
#print axioms OnBytes.Slice.foldOutput_keptRows_zero
#print axioms OnBytes.Slice.switchKept_foldOutput
#print axioms OnBytes.Slice.size_foldOutput_d0
#print axioms OnBytes.Slice.size_foldOutput_d1
#print axioms OnBytes.Slice.vars_foldOutput
#print axioms OnBytes.Slice.plainForm_foldOutput
#print axioms OnBytes.Slice.foldOutput_ok
#print axioms OnBytes.Slice.foldOutput_code
#print axioms OnBytes.Slice.foldOutput_maskCode
#print axioms OnBytes.Slice.foldOutput_layout
#print axioms OnBytes.Slice.foldOutput_gamma
#print axioms OnBytes.Slice.foldOutput_masks
#print axioms OnBytes.Slice.foldOutput_fresh
#print axioms OnBytes.Slice.foldOutput_target
#print axioms OnBytes.Slice.foldOutput_kept
#print axioms OnBytes.Slice.foldOutput_keptRows
#print axioms OnBytes.Slice.ioppFoldShape_code
#print axioms OnBytes.Slice.ioppFoldShape_maskCode
#print axioms OnBytes.Slice.ioppFoldShape_layout
#print axioms OnBytes.Slice.ioppFoldShape_k
#print axioms OnBytes.Slice.ioppFoldShape_h
#print axioms OnBytes.Slice.ioppFoldShape_members
#print axioms OnBytes.Slice.ioppFoldShape_kept
#print axioms OnBytes.Slice.ioppFoldShape_mainFirst
#print axioms OnBytes.Slice.ioppFoldShape_maskFirst
#print axioms OnBytes.Slice.length_weightsL
