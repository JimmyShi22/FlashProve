-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkCsSym.lean: the symbols that the program folds out of an opened column are the long
symbols of the three folded words.

After a fold the verifier reads the three folded rows at drawn positions. The program puts the
symbols of an opened column into tables, one row of the group to an entry, and folds each table at
the fold's point (OnBytes/Iop/Fold.lean: `foldLow`). The library speaks of three folded words
(OnBytes/Slice/Stage.lean: `wordMid`) and of their long symbols at a position: the three elements
that the words show there, by `LdCode.T` (Cb/Ld/LdRel.lean). This file shows that the two agree, if
the program's table has the entries of the format's column at that position.

Main theorems: `sym_main` (the main rows, at the whole point), `sym_mask`, `sym_fresh` (the carried
and the fresh mask rows, at the point's first h coordinates).

Not claimed. Nothing on how the program makes its tables from the opened columns, and nothing on
which columns a view shows.
-/
import OnBytes.Slice.CsVals
import OnBytes.Slice.BlkFoldVec

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run
open Fmt.M1 (SRow Col)

/-- A record of the format that holds the program's point, and nothing else. -/
def pointRow (gamma : List E) : SRow :=
  ⟨#[], #[], #[], Fmt.Fld.zeroE, gamma.map E.triple⟩

/-- That record's point, entry by entry, is the program's. -/
theorem lst_pointRow (gamma : List E) : lst (pointRow gamma).g = readL gamma :=
  funext fun i => (readL_eq_lst gamma i).symm

/-- That record's point has as many coordinates as the program's. -/
theorem length_pointRow (gamma : List E) : (pointRow gamma).g.length = gamma.length :=
  List.length_map _

/-- The first entry of a table of 2^|g| entries, folded at g, is the sum of the table's entries,
each times its weight `eqW` at g. -/
theorem readE_foldAll (g : List E) (t : Array E) (hsz : t.size = 2 ^ g.length) :
    readE ((foldLow t g).getD 0 zeroE)
      = ∑ b ∈ Finset.range (2 ^ g.length), eqW g.length (readL g) b * readV t b := by
  have h := readV_foldLowB_of g t 1 (by rw [hsz, Nat.one_mul]) 0
  simp only [Nat.mul_zero, Nat.add_zero] at h
  exact h

variable (s : Sg) (col : ℕ → Col) (gamma : List E) (hg : gamma.length = s.h + s.g) (x : s.Ps)
  (t : Array E)
include hg

/-- The main rows. The first folded word shows at the position x the first entry of the table t,
folded at the whole point, if t has the 2^(h + g) entries of the main part of the column at x. -/
theorem sym_main (hsz : t.size = 2 ^ (s.h + s.g))
    (ht : ∀ b, b < 2 ^ (s.h + s.g) → readV t b = vec (col x.val).main b) :
    s.cMid.T (wordMid s col (readP _ gamma)) x (.inl ())
      = readE ((foldLow t gamma).getD 0 zeroE) := by
  have hg' : (pointRow gamma).g.length = s.h + s.g := (length_pointRow gamma).trans hg
  rw [readE_foldAll gamma t (by rw [hsz, hg]), readP_eq_ptL]
  refine (mid_main s (pointRow gamma) hg' col x).trans ?_
  rw [toE_yOf_main, lst_pointRow, length_pointRow]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [ht b (by rw [← hg]; exact Finset.mem_range.1 hb)]

/-- The first entry of a table of 2^h entries, folded at the point's first h coordinates, is the sum
of the table's entries, each times its weight `eqW` at these coordinates. -/
theorem readE_foldLowPart (hsz : t.size = 2 ^ s.h) :
    readE ((foldLow t (gamma.take s.h)).getD 0 zeroE)
      = ∑ b ∈ Finset.range (2 ^ s.h), eqW s.h (readL gamma) b * readV t b := by
  have hl : (gamma.take s.h).length = s.h := by
    rw [List.length_take, hg]
    omega
  rw [readE_foldAll (gamma.take s.h) t (by rw [hsz, hl]), hl]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [eqW_congr s.h (readL (gamma.take s.h)) (readL gamma) b fun i hi => readL_take s.h gamma i hi]

/-- The carried mask rows. The second folded word shows at x the first entry of t, folded at the
point's first h coordinates, if t has the 2^h entries of the carried mask part of the column
at x. -/
theorem sym_mask (hsz : t.size = 2 ^ s.h)
    (ht : ∀ b, b < 2 ^ s.h → readV t b = vec (col x.val).mask b) :
    s.cMid.T (wordMid s col (readP _ gamma)) x (.inr (.inl ()))
      = readE ((foldLow t (gamma.take s.h)).getD 0 zeroE) := by
  have hg' : (pointRow gamma).g.length = s.h + s.g := (length_pointRow gamma).trans hg
  rw [readE_foldLowPart s gamma hg t hsz, readP_eq_ptL]
  refine (mid_mask s (pointRow gamma) hg' col x).trans ?_
  rw [toE_yOf_mask, lst_pointRow, hg', Nat.min_eq_left (Nat.le_add_right s.h s.g)]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [ht b (Finset.mem_range.1 hb)]

/-- The fresh mask rows. The third folded word shows at x the first entry of t, folded at the
point's first h coordinates, if t has the 2^h entries of the fresh mask part of the column at x. -/
theorem sym_fresh (hsz : t.size = 2 ^ s.h)
    (ht : ∀ b, b < 2 ^ s.h → readV t b = vec (col x.val).fresh b) :
    s.cMid.T (wordMid s col (readP _ gamma)) x (.inr (.inr ()))
      = readE ((foldLow t (gamma.take s.h)).getD 0 zeroE) := by
  have hg' : (pointRow gamma).g.length = s.h + s.g := (length_pointRow gamma).trans hg
  rw [readE_foldLowPart s gamma hg t hsz, readP_eq_ptL]
  refine (mid_fresh s (pointRow gamma) hg' col x).trans ?_
  rw [toE_yOf_fresh, lst_pointRow, hg', Nat.min_eq_left (Nat.le_add_right s.h s.g)]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [ht b (Finset.mem_range.1 hb)]

end OnBytes.Slice

#print axioms OnBytes.Slice.lst_pointRow
#print axioms OnBytes.Slice.length_pointRow
#print axioms OnBytes.Slice.readE_foldAll
#print axioms OnBytes.Slice.sym_main
#print axioms OnBytes.Slice.readE_foldLowPart
#print axioms OnBytes.Slice.sym_mask
#print axioms OnBytes.Slice.sym_fresh
