-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/CsVals.lean: what the code switch reads of the three folded words is what the format
computes from an opened column.

After a fold, the library's code switch reads the three folded words of a stage (`wordMid` in
OnBytes/Slice/Stage.lean) at drawn positions. The format's verifier has no folded words: it opens
the column of the stage's tree at the position and folds the column's three parts itself
(`yOf` in Fmt/M1Cs.lean). This file proves that both get the same three elements of the field.

Main theorems, for a claim R whose point has as many coordinates as the stage has row variables.
 `mid_main`    the main rows, folded at the whole point.
 `mid_mask`    the carried mask rows, folded at the point's first h coordinates.
 `mid_fresh`   the fresh mask rows, folded likewise.
A word of mask rows has a symbol at each position of the tree (`ldRep`, OnBytes/Slice/LinkAt.lean),
and it is taken from the column at that position. So `mid_mask` and `mid_fresh` hold also where the
mask code is shorter than the main code.

Not claimed. That the columns at two positions that are equal modulo the mask code's length hold
the same mask symbols: nothing here asks it, and the format's verifier does not test it.
-/
import OnBytes.Slice.Stage
import OnBytes.Slice.LdOfFacts
import OnBytes.Slice.SimCs

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-- A part of a column, folded over the vertices of the cube at a point that is read from a list:
the same sum over the numbers of the vertices, with the weights of OnBytes/Slice/SimBasic.lean. -/
private theorem fold_sum (k : ℕ) (g : List Fmt.M1.E) (γ : Fin k → GE)
    (hγ : ∀ t, γ t = lst g t.val) (v : Array Fmt.M1.E) :
    ∑ b : Fin k → Bool, Alg.eqk γ b * vec v (Sz.rowNo b) =
      ∑ b ∈ Finset.range (2 ^ k), eqW k (lst g) b * vec v b := by
  have h1 : γ = fun t : Fin k => lst g t.val := funext hγ
  rw [sum_range_cube, h1]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [eqW_rowNo]

/-- The first of the three folded words at a position is the format's fold of the main part of the
column there. -/
theorem mid_main (s : Sg) (R : Fmt.M1.SRow) (hg : R.g.length = s.h + s.g) (col : ℕ → Fmt.M1.Col)
    (x : s.Ps) :
    s.cMid.T (wordMid s col (ptL _ R.g)) x (.inl ()) =
      toE (Fmt.M1.yOf .two s.h R (col x.val)).1 := by
  show ∑ b : Fin (s.h + s.g) → Bool,
      Alg.eqk (ptL (s.h + s.g) R.g) b * vec (col (posIn s.C x).val).main (Sz.rowNo b) = _
  rw [posIn_self, toE_yOf_main, hg]
  exact fold_sum (s.h + s.g) R.g _ (fun _ => rfl) _

/-- The second of the three folded words at a position is the format's fold of the carried mask part
of the column there. -/
theorem mid_mask (s : Sg) (R : Fmt.M1.SRow) (hg : R.g.length = s.h + s.g)
    (col : ℕ → Fmt.M1.Col) (x : s.Ps) :
    s.cMid.T (wordMid s col (ptL _ R.g)) x (.inr (.inl ())) =
      toE (Fmt.M1.yOf .two s.h R (col x.val)).2.1 := by
  show ∑ b : Fin s.h → Bool,
      Alg.eqk (preP s (ptL (s.h + s.g) R.g)) b * vec (col x.val).mask (Sz.rowNo b) = _
  rw [toE_yOf_mask, hg, Nat.min_eq_left (Nat.le_add_right s.h s.g)]
  exact fold_sum s.h R.g _ (fun _ => rfl) _

/-- The third of the three folded words at a position is the format's fold of the fresh mask part of
the column there. -/
theorem mid_fresh (s : Sg) (R : Fmt.M1.SRow) (hg : R.g.length = s.h + s.g)
    (col : ℕ → Fmt.M1.Col) (x : s.Ps) :
    s.cMid.T (wordMid s col (ptL _ R.g)) x (.inr (.inr ())) =
      toE (Fmt.M1.yOf .two s.h R (col x.val)).2.2 := by
  show ∑ b : Fin s.h → Bool,
      Alg.eqk (preP s (ptL (s.h + s.g) R.g)) b * vec (col x.val).fresh (Sz.rowNo b) = _
  rw [toE_yOf_fresh, hg, Nat.min_eq_left (Nat.le_add_right s.h s.g)]
  exact fold_sum s.h R.g _ (fun _ => rfl) _

end OnBytes.Slice

#print axioms OnBytes.Slice.mid_main
#print axioms OnBytes.Slice.mid_mask
#print axioms OnBytes.Slice.mid_fresh
