-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkRow.lean: the coefficients of the program's rows, in the field.

A row of the program (OnBytes/Iop/Ground.lean: `Row`) is a sum of four kinds of parts: tensors on a
table, single entries, runs of written-out coefficients at equal distances, and forms on a main
table. `Row.coefficient` adds up what all parts give on one entry of one table. This file reads that
coefficient in the field (`coefAt`, OnBytes/Slice/BlkRead.lean) and says how each call that makes or
changes a row changes it.

Main definitions: `runAt` (what one run gives on an entry), `termsAt`, `unitsAt`, `runsAt`,
`formsAt`.
Main theorems: `coefAt_eq` (the coefficient is the sum of the four kinds), `coefAt_empty`,
`coefAt_add`, `coefAt_addForm`, `coefAt_addRun`, `coefAt_addUnit`.

Not claimed. Nothing on targets. Nothing on a protocol.
-/
import OnBytes.Slice.BlkRead

set_option autoImplicit false

namespace OnBytes.Slice

/-- A sum that a loop makes by adding the parts that pass a test. -/
theorem readE_foldl_if {α : Type} (p : α → Bool) (f : α → E) : ∀ (l : List α) (a : E),
    readE (l.foldl (fun s t => if p t then addE s (f t) else s) a)
      = readE a + (l.map fun t => if p t then readE (f t) else 0).sum
  | [], a => by simp
  | t :: l, a => by
    rw [List.foldl_cons, readE_foldl_if p f l, List.map_cons, List.sum_cons]
    by_cases h : p t = true
    · rw [if_pos h, if_pos h, readE_add, add_assoc]
    · rw [if_neg h, if_neg h, zero_add]

/-- True if the run has a coefficient on entry i of that table. -/
def runHits (w : OnBytes.Run) (o : ℕ) (part : Part) (i : ℕ) : Bool :=
  w.oracle == o && w.part == part && w.first ≤ i && 0 < w.step &&
    (i - w.first) % w.step == 0 && (i - w.first) / w.step < w.coeffs.size

/-- What a run gives on entry i of a table. -/
def runAt (w : OnBytes.Run) (o : ℕ) (part : Part) (i : ℕ) : GE :=
  if runHits w o part i then readE (w.coeffs.get ((i - w.first) / w.step)) else 0

/-- What the tensors of a row give on entry i of a table. -/
def termsAt (r : Row) (o : ℕ) (part : Part) (i : ℕ) : GE :=
  (r.terms.toList.map fun t =>
    if t.oracle == o && t.part == part then readE (t.v.entry i) else 0).sum

/-- What the single entries of a row give on entry i of a table. -/
def unitsAt (r : Row) (o : ℕ) (part : Part) (i : ℕ) : GE :=
  (r.units.toList.map fun u =>
    if u.oracle == o && u.part == part && u.index == i then readE u.coeff else 0).sum

/-- What the runs of a row give on entry i of a table. -/
def runsAt (r : Row) (o : ℕ) (part : Part) (i : ℕ) : GE :=
  (r.runs.toList.map fun w => runAt w o part i).sum

/-- What the forms of a row give on entry i of a table. -/
def formsAt (r : Row) (o : ℕ) (part : Part) (i : ℕ) : GE :=
  (r.forms.toList.map fun f =>
    if f.oracle == o && part == .main then formAt f.c i else 0).sum

/-- The coefficient of a row is the sum of what its four kinds of parts give. -/
theorem coefAt_eq (r : Row) (o : ℕ) (part : Part) (i : ℕ) :
    coefAt r o part i
      = termsAt r o part i + unitsAt r o part i + runsAt r o part i + formsAt r o part i := by
  unfold coefAt Row.coefficient
  simp only [← Array.foldl_toList]
  rw [readE_foldl_if (fun f : MainForm => f.oracle == o && part == .main) (fun f => f.c.entry i),
    readE_foldl_if (fun w : OnBytes.Run => w.oracle == o && w.part == part && w.first ≤ i &&
        0 < w.step && (i - w.first) % w.step == 0 && (i - w.first) / w.step < w.coeffs.size)
      (fun w => w.coeffs.get ((i - w.first) / w.step)),
    readE_foldl_if (fun u : Single => u.oracle == o && u.part == part && u.index == i)
      (fun u => u.coeff),
    readE_foldl_if (fun t : Term => t.oracle == o && t.part == part) (fun t => t.v.entry i),
    readE_zero, zero_add]
  rfl

/-- The row without parts has the coefficient 0 everywhere. -/
theorem coefAt_empty (o : ℕ) (part : Part) (i : ℕ) : coefAt {} o part i = 0 := by
  rw [coefAt_eq]
  simp [termsAt, unitsAt, runsAt, formsAt]

/-- One more tensor. -/
theorem coefAt_add (r : Row) (o' : ℕ) (part' : Part) (v : Tensor) (o : ℕ) (part : Part) (i : ℕ) :
    coefAt (r.add o' part' v) o part i
      = coefAt r o part i + if o' == o && part' == part then readE (v.entry i) else 0 := by
  rw [coefAt_eq, coefAt_eq]
  have h : termsAt (r.add o' part' v) o part i
      = termsAt r o part i + if o' == o && part' == part then readE (v.entry i) else 0 := by
    simp [termsAt, Row.add]
  rw [h]
  show _ + unitsAt r o part i + runsAt r o part i + formsAt r o part i = _
  ring

/-- One more form on a main table. -/
theorem coefAt_addForm (r : Row) (o' : ℕ) (c : Form) (o : ℕ) (part : Part) (i : ℕ) :
    coefAt (r.addForm o' c) o part i
      = coefAt r o part i + if o' == o && part == .main then formAt c i else 0 := by
  rw [coefAt_eq, coefAt_eq]
  have h : formsAt (r.addForm o' c) o part i
      = formsAt r o part i + if o' == o && part == .main then formAt c i else 0 := by
    simp [formsAt, Row.addForm]
  rw [h]
  show termsAt r o part i + unitsAt r o part i + runsAt r o part i + _ = _
  ring

/-- One more run. -/
theorem coefAt_addRun (r : Row) (o' : ℕ) (part' : Part) (first step : ℕ) (c : Coeffs) (o : ℕ)
    (part : Part) (i : ℕ) :
    coefAt (r.addRun o' part' first step c) o part i
      = coefAt r o part i + runAt ⟨o', part', first, step, c⟩ o part i := by
  rw [coefAt_eq, coefAt_eq]
  have h : runsAt (r.addRun o' part' first step c) o part i
      = runsAt r o part i + runAt ⟨o', part', first, step, c⟩ o part i := by
    simp [runsAt, Row.addRun]
  rw [h]
  show termsAt r o part i + unitsAt r o part i + _ + formsAt r o part i = _
  ring

/-- One more single entry. -/
theorem coefAt_addUnit (r : Row) (o' : ℕ) (part' : Part) (index : ℕ) (x : E) (o : ℕ)
    (part : Part) (i : ℕ) :
    coefAt (r.addUnit o' part' index x) o part i
      = coefAt r o part i + if o' == o && part' == part && index == i then readE x else 0 := by
  rw [coefAt_eq, coefAt_eq]
  have h : unitsAt (r.addUnit o' part' index x) o part i
      = unitsAt r o part i + if o' == o && part' == part && index == i then readE x else 0 := by
    simp [unitsAt, Row.addUnit]
  rw [h]
  show termsAt r o part i + _ + runsAt r o part i + formsAt r o part i = _
  ring

end OnBytes.Slice

#print axioms OnBytes.Slice.coefAt_eq
#print axioms OnBytes.Slice.coefAt_empty
#print axioms OnBytes.Slice.coefAt_add
#print axioms OnBytes.Slice.coefAt_addForm
#print axioms OnBytes.Slice.coefAt_addRun
#print axioms OnBytes.Slice.coefAt_addUnit
#print axioms OnBytes.Slice.readE_foldl_if
