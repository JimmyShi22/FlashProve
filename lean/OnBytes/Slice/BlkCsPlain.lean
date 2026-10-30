-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkCsPlain.lean: the rows of the program's code switch have no written-out factor.

A tensor of the program may have one factor that is written out as a slice of an array. The laws on
the program's fold are stated for forms without such a factor (`PlainForm`), and a batched row has
such a form if all its rows are plain (`PlainRow`, OnBytes/Slice/BlkPlain.lean). This file shows
that the rows of a code switch into a stage (OnBytes/Slice/BlkCsRows.lean) are plain: the rows of
generator matrices always, the carried claim if the old claim's form is.

Main theorems: `plainRow_genMain`, `plainRow_genMask`, `plainRow_carriedRow`.
Not claimed. Nothing on the sample row, which has its own law.
-/
import OnBytes.Slice.BlkCsRows
import OnBytes.Slice.BlkPlain

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## Coefficients on a stretch add runs alone -/

/-- Coefficients over the extension field on a stretch add no tensor to the row's terms. -/
theorem terms_restE (g : ℕ) (part : Part) (coeff : Array E) : ∀ (pieces : List SwitchPiece)
    (row : Row), (switchAddRestE row g part pieces coeff).terms = row.terms
  | [], _ => rfl
  | p :: pieces, row =>
    terms_restE g part coeff pieces
      (row.addRun g part p.first p.step (.own (coeff.extract p.start p.stop)))

/-- Coefficients over the extension field on a stretch add no whole coefficient vector. -/
theorem forms_restE (g : ℕ) (part : Part) (coeff : Array E) : ∀ (pieces : List SwitchPiece)
    (row : Row), (switchAddRestE row g part pieces coeff).forms = row.forms
  | [], _ => rfl
  | p :: pieces, row =>
    forms_restE g part coeff pieces
      (row.addRun g part p.first p.step (.own (coeff.extract p.start p.stop)))

/-- Coefficients over the base field on a stretch add no tensor to the row's terms. -/
theorem terms_restF (g : ℕ) (part : Part) (coeff : Array F) : ∀ (pieces : List SwitchPiece)
    (row : Row), (switchAddRestF row g part pieces coeff).terms = row.terms
  | [], _ => rfl
  | p :: pieces, row =>
    terms_restF g part coeff pieces
      (row.addRun g part p.first p.step (.stretch coeff p.start (p.stop - p.start)))

/-- Coefficients over the base field on a stretch add no whole coefficient vector. -/
theorem forms_restF (g : ℕ) (part : Part) (coeff : Array F) : ∀ (pieces : List SwitchPiece)
    (row : Row), (switchAddRestF row g part pieces coeff).forms = row.forms
  | [], _ => rfl
  | p :: pieces, row =>
    forms_restF g part coeff pieces
      (row.addRun g part p.first p.step (.stretch coeff p.start (p.stop - p.start)))

/-! ## The parts of the rows -/

/-- A form that is carried to the new main table stays plain. -/
theorem plainForm_switchLift {c : Form} (hc : PlainForm c) (vars : ℕ) (cut : RowCut)
    (tableRowBits tableBits : ℕ) : PlainForm (switchLift c vars cut tableRowBits tableBits) :=
  plainForm_insertChoice (plainForm_insertChoice hc _ _ _) _ _ _

/-- The tensor of a generator's row on a message has no written-out factor. -/
theorem plain_messageTensor (c : OnBytes.Code) (x : ℕ) : (messageTensor c x).denseVars = [] := rfl

/-- A form that is one plain tensor is plain. -/
theorem plainForm_ofTensor {v : Tensor} (hv : v.denseVars = []) : PlainForm (Form.ofTensor v) :=
  fun w hw => by
    rw [List.mem_singleton.1 hw]
    exact hv

/-- A plain tensor on a box stays plain. -/
theorem plain_switchOnBox (b : SwitchBox) {v : Tensor} (hv : v.denseVars = [])
    (vars tableBits : ℕ) : (switchOnBox b v vars tableBits).denseVars = [] := by
  show ((v.denseVars.map _).map _) = []
  rw [hv]
  rfl

/-! ## The rows -/

/-- The row of the old main code's generator is plain. -/
theorem plainRow_genMain (W : SwitchFrame) (x : ℕ) (t : E) : PlainRow (genMain W x t) := by
  constructor
  · intro u hu
    have e : (genMain W x t).terms = #[] := terms_restF _ _ _ _ _
    rw [e] at hu
    exact absurd hu List.not_mem_nil
  · intro f hf
    have e : (genMain W x t).forms = #[⟨W.g, switchLift (Form.ofTensor (messageTensor W.code x))
        W.code.logEll W.mainCut W.rowBits W.tableBits⟩] := forms_restF _ _ _ _ _
    rw [e] at hf
    rw [List.mem_singleton.1 hf]
    exact plainForm_switchLift (plainForm_ofTensor (plain_messageTensor W.code x)) _ _ _ _

/-- The row of the old mask code's generator is plain. -/
theorem plainRow_genMask (W : SwitchFrame) (x j : ℕ) (t : E) : PlainRow (genMask W x j t) := by
  unfold genMask
  cases W.box.getD j none with
  | none =>
    refine plainRow_of_empty _ ?_ ?_
    · exact (terms_restF _ _ _ _ _).trans (terms_restF _ _ _ _ _)
    · exact (forms_restF _ _ _ _ _).trans (forms_restF _ _ _ _ _)
  | some b =>
    constructor
    · intro u hu
      have e : (switchAddRestF (({} : Row).add W.g W.restPart (switchOnBox b
          (messageTensor W.zk (shortPosition W.zk.logN x)) W.zk.logEll W.restBits)) W.g W.restPart
          (W.maskTail.getD j []) (generatorTail W.zk (shortPosition W.zk.logN x))).terms
          = #[⟨W.g, W.restPart, switchOnBox b (messageTensor W.zk (shortPosition W.zk.logN x))
            W.zk.logEll W.restBits⟩] := terms_restF _ _ _ _ _
      have hu' : u ∈ (#[⟨W.g, W.restPart, switchOnBox b
          (messageTensor W.zk (shortPosition W.zk.logN x)) W.zk.logEll W.restBits⟩]
          : Array Term).toList := e ▸ hu
      rw [List.mem_singleton.1 hu']
      exact plain_switchOnBox b (plain_messageTensor W.zk _) _ _
    · intro f hf
      have e : (switchAddRestF (({} : Row).add W.g W.restPart (switchOnBox b
          (messageTensor W.zk (shortPosition W.zk.logN x)) W.zk.logEll W.restBits)) W.g W.restPart
          (W.maskTail.getD j []) (generatorTail W.zk (shortPosition W.zk.logN x))).forms = #[] :=
        forms_restF _ _ _ _ _
      have hf' : f ∈ (#[] : Array MainForm).toList := e ▸ hf
      exact absurd hf' List.not_mem_nil

/-- The carried claim is plain, if the old claim's form on the main row is. -/
theorem plainRow_carriedRow (W : SwitchFrame) (old : SingleRows) (hc : PlainForm old.c) :
    PlainRow (carriedRow W old) := by
  constructor
  · intro u hu
    have e : (carriedRow W old).terms = #[] :=
      (terms_restE _ _ _ _ _).trans (terms_restE _ _ _ _ _)
    rw [e] at hu
    exact absurd hu List.not_mem_nil
  · intro f hf
    have e : (carriedRow W old).forms = #[⟨W.g, switchLift old.c W.code.logEll W.mainCut W.rowBits
        W.tableBits⟩] := (forms_restE _ _ _ _ _).trans (forms_restE _ _ _ _ _)
    rw [e] at hf
    rw [List.mem_singleton.1 hf]
    exact plainForm_switchLift hc _ _ _ _

end OnBytes.Slice

#print axioms OnBytes.Slice.plainRow_genMain
#print axioms OnBytes.Slice.plainRow_genMask
#print axioms OnBytes.Slice.plainRow_carriedRow
#print axioms OnBytes.Slice.terms_restE
#print axioms OnBytes.Slice.forms_restE
#print axioms OnBytes.Slice.terms_restF
#print axioms OnBytes.Slice.forms_restF
#print axioms OnBytes.Slice.plainForm_switchLift
#print axioms OnBytes.Slice.plain_messageTensor
#print axioms OnBytes.Slice.plainForm_ofTensor
#print axioms OnBytes.Slice.plain_switchOnBox
