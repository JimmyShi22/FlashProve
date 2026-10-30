-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieRead.lean: THE TABLE'S
MACHINE ELEMENTS, READ, AGAINST THE KIND'S LAW'S READINGS IN THE FIELD: first part: forms over
hidden values. The table of the key file's joints says "the form a is worth 0" by
machine elements (hidden, affAt, Zero: Johnson/Desc/Key/KeyK3W.lean); the law of the kind's own
block reads the same form as a public value and a form in mask entries (valOf, mfOf, rowA:
Johnson/Desc/First/Look/KeyLaw/Statement.lean). Read into the field they are one.

Main names:
  read_hidden, read_affAt: the hidden value under a slot, and a form's worth, read.
  zero_iff_rowA: at "two elements are the same where they read alike": the form's worth reads 0
    exactly if the row rowA has its target as its value at the mask entries, read.

Object: definitions of two groups of files; no block's text.
User: none yet (meant: the tie of the claims at the border between the kind's block and the layer).
Letters: G, a ledger · home, the table of homes · mk, the mask entries · a, a form.

Limits. Forms over hidden values alone. Nothing on the planes or the keys. Nothing on soundness.

-/
import Johnson.Desc.Key.KeyK3Items
import Johnson.Desc.First.Look.KeyLaw.GroupSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TieRead
open OnBytes OnBytes.Slice
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc.Key (hidden affAt)
open VerifiableInference.Desc.K3.KeyLaw (mfOf valOf rowA valueF)

variable (G : Fork) (home : Array Slot) (mk : Slot → E)

/-- The hidden value under a slot, read. -/
theorem read_hidden (j : ℕ) : readE (hidden G home mk j) =
    readE (G.vp.getD j zeroE) - readE (G.mf.getD j zeroE) * readE (mk (home.getD j default)) := by
  unfold VerifiableInference.Desc.Key.hidden
  rw [readE_sub, readE_mul]

theorem read_fold : ∀ (l : List (ℕ × E)) (c : E),
    readE (l.foldl (fun s t => addE s (mulE t.2 (hidden G home mk t.1))) c) =
      readE c + (l.map fun t => readE t.2 * readE (hidden G home mk t.1)).sum
  | [], c => by simp
  | t :: l, c => by
    rw [List.foldl_cons, read_fold l, readE_add, readE_mul, List.map_cons, List.sum_cons]
    ring

/-- **A form's worth, read**: its public value less its form in mask entries. -/
theorem read_affAt (a : Aff) : readE (affAt G home mk a) =
    valOf G a - ((mfOf G (fun n => home.getD n default) a).map fun p =>
      p.2 * readE (mk p.1)).sum := by
  unfold affAt valOf mfOf
  rw [← Array.foldl_toList, read_fold, List.map_map]
  have e : ∀ l : List (ℕ × E),
      (l.map fun t => readE t.2 * readE (hidden G home mk t.1)).sum =
        (l.map fun t => readE t.2 * readE (G.vp.getD t.1 zeroE)).sum -
          (l.map ((fun p : Slot × GE => p.2 * readE (mk p.1)) ∘ fun t : ℕ × E =>
            (home.getD t.1 default, readE t.2 * readE (G.mf.getD t.1 zeroE)))).sum := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.map_cons,
        List.sum_cons, ih, read_hidden]
      simp only [Function.comp]
      ring
  rw [e]
  ring

/-- **The form's worth reads 0 exactly if the kind's law's row holds at the mask entries, read.** -/
theorem zero_iff_rowA (mu d : ℕ) (bit : ℕ → ℕ → GE) (a : Aff) :
    readE (affAt G home mk a) = readE zeroE ↔
      valueF mu d (rowA G (fun n => home.getD n default) a) (fun s => readE (mk s)) bit =
        (rowA G (fun n => home.getD n default) a).target := by
  rw [read_affAt, readE_zero]
  unfold valueF rowA PscF.scaleForm
  simp only [List.map_map, List.map_nil, List.sum_nil, add_zero]
  have e : ∀ l : PscF.MaskForm,
      (l.map ((fun p : Slot × GE => p.2 * readE (mk p.1)) ∘ fun t : Slot × GE =>
        (t.1, -1 * t.2))).sum = - (l.map fun p => p.2 * readE (mk p.1)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp, ih]
      ring
  rw [e]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

end Johnson.RunOne.Law.TieRead

#print axioms Johnson.RunOne.Law.TieRead.read_affAt
#print axioms Johnson.RunOne.Law.TieRead.zero_iff_rowA
