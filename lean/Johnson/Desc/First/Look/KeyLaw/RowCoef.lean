-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/RowCoef.lean: the coefficients of a row of the statement's type
(OnBytes.Row, by its own Row.coefficient), read in the field: of a row with a target alone; what a
single entry and a mask form add; and an entry of a vector of product form, read.

Main names:
  readPairs, pairsVal_eq, entry_read: a vector of product form.
  rd_addUnit, rd_addMasks, target_addMasks, rd_bare: a row's coefficients and target.

Limits. Nothing on a term on a table.

-/
import Johnson.Desc.First.Look.KeyLaw.Readings
import OnBytes.Iop.RowLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid

open OnBytes OnBytes.Slice Finset

/-- Pairs, read. -/
def readPairs (ps : List (E × E)) : List (GE × GE) := ps.map fun p => (readE p.1, readE p.2)

/-- The product of the halves that a number's bits pick, read. -/
theorem pairsVal_eq : ∀ (ps : List (E × E)) (n : ℕ),
    pairsVal Model.Reading.gl ps n = pairsAt (readPairs ps) n
  | [], _ => rfl
  | p :: ps, n => by
    show Model.Reading.gl.val (if n % 2 == 1 then p.2 else p.1) *
        pairsVal Model.Reading.gl ps (n / 2) =
      (if n % 2 = 1 then readE p.2 else readE p.1) * pairsAt (readPairs ps) (n / 2)
    rw [pairsVal_eq ps]
    by_cases h : n % 2 = 1
    · rw [if_pos h, if_pos (beq_iff_eq.2 h)]
      rfl
    · rw [if_neg h, if_neg fun hb => h (beq_iff_eq.1 hb)]
      rfl

/-- An entry of a vector of product form, read. -/
theorem entry_read (v : Tensor) (hv : v.denseVars = []) (n : ℕ) :
    readE (v.entry n) = readE v.scalar * pairsAt (readPairs v.pairs) n := by
  have h := Tensor.entry_val Model.Reading.gl v n
  rw [pairsVal_eq] at h
  unfold Tensor.denseVal at h
  rw [hv] at h
  simp only [List.isEmpty_nil, if_true, mul_one] at h
  exact h

/-- What one single entry adds to a coefficient. -/
theorem rd_addUnit (r : Row) (o' : ℕ) (part' : Part) (i' : ℕ) (c : E) (o : ℕ) (part : Part)
    (idx : ℕ) :
    readE ((r.addUnit o' part' i' c).coefficient o part idx) =
      readE (r.coefficient o part idx) +
        (if o' = o ∧ part' = part then (if i' = idx then readE c else 0) else 0) := by
  have h1 := Row.coefficient_val Model.Reading.gl (r.addUnit o' part' i' c) o part idx
  have h2 := Row.coefficient_val Model.Reading.gl r o part idx
  have e : (r.addUnit o' part' i' c) = { r with units := r.units.push ⟨o', part', i', c⟩ } := rfl
  rw [e] at h1
  simp only [Array.toList_push, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero] at h1
  show Model.Reading.gl.val _ = Model.Reading.gl.val _ + _
  rw [e, h1, h2]
  show _ = _ + (if o' = o ∧ part' = part then
    (if i' = idx then Model.Reading.gl.val c else 0) else 0)
  ring

/-- **What a mask form adds to a coefficient.** -/
theorem rd_addMasks : ∀ (m : MaskForm) (r : Row) (o : ℕ) (part : Part) (idx : ℕ),
    readE ((r.addMasks m).coefficient o part idx) = readE (r.coefficient o part idx) +
      (m.map fun p => if p.1.oracle = o ∧ Part.mask = part then
        (if p.1.index = idx then readE p.2 else 0) else 0).sum
  | [], r, o, part, idx => by
    show readE (r.coefficient o part idx) = _
    rw [List.map_nil, List.sum_nil, add_zero]
  | p :: m, r, o, part, idx => by
    show readE (((r.addUnit p.1.oracle .mask p.1.index p.2).addMasks m).coefficient o part idx) = _
    rw [rd_addMasks m, rd_addUnit, List.map_cons, List.sum_cons, add_assoc]

/-- A mask form leaves the target. -/
theorem target_addMasks : ∀ (m : MaskForm) (r : Row), (r.addMasks m).target = r.target
  | [], _ => rfl
  | p :: m, r => by
    show ((r.addUnit p.1.oracle .mask p.1.index p.2).addMasks m).target = _
    rw [target_addMasks m]
    rfl

/-- A row with a target alone has the coefficient 0 everywhere. -/
theorem rd_bare (t : E) (o : ℕ) (part : Part) (idx : ℕ) :
    readE (({ target := t } : Row).coefficient o part idx) = 0 := by
  have h := Row.coefficient_val Model.Reading.gl ({ target := t } : Row) o part idx
  simp at h
  exact h

end Lk6.Mid

#print axioms Lk6.Mid.entry_read
#print axioms Lk6.Mid.rd_addMasks
#print axioms Lk6.Mid.target_addMasks
#print axioms Lk6.Mid.rd_bare
