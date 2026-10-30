-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/K15Rows.lean: beneath K15's law: the two constraints that K15 calls by name
(Desc.K14.recGamma and
Desc.K14.locX, Johnson/Desc/K14/Text.lean) ARE, under the clauses that stand in front of them, the
library's pure row functions
foldeqRecordRow and foldeqColumnRow at foldeqSymbol (OnBytes/Iop/Foldeq.lean), of which the
library's facts on a link's rows
speak. Two equations between pure functions; no program is run.
-/
import Johnson.Desc.K14.Text

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Params

/-- A sum by foldlM over look-ups that are all there is the sum by foldl over getD. -/
theorem foldlM_lookups {α : Type} (f : α → Nat → Option α) (g : α → Nat → α) (n : Nat)
    (h : ∀ a r, r < n → f a r = some (g a r)) (a : α) :
    (List.range n).foldlM f a = some ((List.range n).foldl g a) := by
  induction n generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldlM_append, List.foldl_append,
      ih (fun a r hr => h a r (Nat.lt_succ_of_lt hr))]
    simp [h _ k (Nat.lt_succ_self k)]

/-- (loc_x) is the library's row of a column, at the library's fold of that column: where the column
has a symbol for each
weight. -/
theorem locX_eq (S : FoldeqShape) (x : Nat) (w : Array E) (column : Array F) (u : FoldedRow)
    (h : w.size ≤ column.size) :
    Desc.K14.locX S x w column u = foldeqColumnRow S x (foldeqSymbol w column) u := by
  have hs : (List.range w.size).foldlM
      (fun s r =>
        do pure (maddS s (← column[r]?) (← w[r]?))) zeroE = some (foldeqSymbol w column) := by
    unfold foldeqSymbol
    apply foldlM_lookups
    intro a r hr
    have hc : r < column.size := Nat.lt_of_lt_of_le hr h
    simp [Array.getD, hc, hr]
  unfold Desc.K14.locX foldeqColumnRow
  simp only [hs]
  rfl

/-- (rec_gamma) is the library's row of a record's answer: where the seed's point and the record
have the shape's sizes, there
is a weight for each row, and the answer is one of the shape's. -/
theorem recGamma_eq (S : FoldeqShape) (seed : SampleSeed) (i : Nat) (w y : Array E) (u : FoldedRow)
    (hz : seed.z.length = S.index.cubeBits) (hy : y.size = S.index.rows * S.index.answers)
    (hw : S.index.rows ≤ w.size) (hi : i < S.index.answers) :
    Desc.K14.recGamma S.index seed i w y u = foldeqRecordRow S seed y i w u := by
  have hs : (List.range S.index.rows).foldlM
      (fun t r => do pure (maddE t (← w[r]?) (← y[r * S.index.answers + i]?))) zeroE =
      some ((List.range S.index.rows).foldl
        (fun t r => maddE t (w.getD r zeroE) (y.getD (r * S.index.answers + i) zeroE)) zeroE) := by
    apply foldlM_lookups
    intro a r hr
    have h1 : r < w.size := Nat.lt_of_lt_of_le hr hw
    have h2 : r * S.index.answers + i < y.size := by
      rw [hy]
      calc
        r * S.index.answers + i < r * S.index.answers + S.index.answers := Nat.add_lt_add_left hi _
        _ = (r + 1) * S.index.answers := (Nat.succ_mul _ _).symm
        _ ≤ S.index.rows * S.index.answers := Nat.mul_le_mul_right _ hr
    simp [Array.getD, h1, h2]
  unfold Desc.K14.recGamma foldeqRecordRow
  simp only [hs, hz, hy, List.foldl_flatMap, List.foldl_map, beq_self_eq_true, Bool.and_self, guard,
      if_true]
  rfl

end Desc.K15

#print axioms Desc.K15.locX_eq
#print axioms Desc.K15.recGamma_eq
