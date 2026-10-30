-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FoldRows.lean: THE ROWS THAT A FOLD CARRIES ON, ON THE PROGRAM's OWN ELEMENTS:
the library's fold of a table (OnBytes.foldLow, OnBytes/Iop/Fold.lean: the arithmetic that the
library's verifier of a fold calls) reads, in the field, as the sumcheck library's foldV
(Cb/Ld/LdRel.lean); and with it the three folded messages and the three folded tails (foldMsg,
foldTl, Johnson/Prover/Link/FoldEnc.lean). NO FUNCTION WITH CODE IS DEFINED HERE: the library's is
called.

Main names (namespace Johnson.Prover.Link).
  TabFits n l T   THE NAMED PREMISE: the table T has l stretches of 2^n entries. A public shape.
      tabFits_iff: the same with the factors as FoldSizes has them.
  tabRead n l T   the table, read in the field, by vertex and place: entry p of row b at the index b
      + 2^n p.
  foldLowOnce_eq   the library's one step, written with every entry read inside the table: its
      stand-in 0 for an entry beyond the end is never read.
  foldV_reads   entry c of the folded table reads as foldV at the point that the list reads as.
  size_foldLow_fits   the folded table has l entries.
  preP_reads   the point's first h coordinates are the list's first h members'.
  foldMsg_reads, foldTl_reads   THE THREE FOLDED MESSAGES, THE THREE FOLDED TAILS, from three tables
      each.

By calls: readV_foldLowB_of, size_foldLowB (OnBytes/Slice/BlkFoldVec.lean); sum_range_cube,
eqW_rowNo (OnBytes/Slice/SimBasic.lean). Kin: toE_dot_fold (Johnson/Prover/Link/FoldWordsLaw.lean)
holds the like sum for the format's fold, on triples of words.

Limits. OUTSIDE TabFits THE VALUES MEAN NOTHING: of a table that is no whole number of stretches the
library's fold leaves the last entries out, without a word. No premise on the words: readE reads any
three words. The tails are taken as tables with the row in the low bits of the index, like the
messages. What stands in the tables is the caller's: nothing is said here of sampled values. COST:
the table is halved variable by variable: about twice its size in operations of the field. Tests:
Johnson/Prover/Link/FoldRowsToy.lean. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.Link.FoldEnc
import OnBytes.Slice.BlkFoldVec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice Cb

/-- **The table has l stretches of 2^n entries.** A public shape. -/
def TabFits (n l : ℕ) (T : Array E) : Prop := T.size = l * 2 ^ n

/-- The table, read in the field, by vertex and place. -/
def tabRead (n l : ℕ) (T : Array E) : (Fin n → Bool) × Fin l → GE :=
  fun x => readV T (Sz.rowNo x.1 + 2 ^ n * x.2.val)

/-- The same premise with the factors the other way round, as FoldSizes
(Johnson/Prover/Link/FoldWordsOf.lean) has them. -/
theorem tabFits_iff (n l : ℕ) (T : Array E) : TabFits n l T ↔ T.size = 2 ^ n * l := by
  unfold TabFits
  rw [Nat.mul_comm]

theorem foldLowOnce_inside (v : Array E) (i : ℕ) (h : i < v.size / 2) : 2 * i + 1 < v.size := by
  omega

/-- **The library's one step, with every entry read inside the table**: its stand-in 0 for an entry
beyond the end is never read. -/
theorem foldLowOnce_eq (v : Array E) (g : E) :
    foldLowOnce v g = Array.ofFn (n := v.size / 2) fun i =>
      maddE (v[2 * i.val]'(by have := foldLowOnce_inside v i.val i.isLt; omega)) g
        (subE (v[2 * i.val + 1]'(foldLowOnce_inside v i.val i.isLt))
          (v[2 * i.val]'(by have := foldLowOnce_inside v i.val i.isLt; omega))) := by
  unfold foldLowOnce
  refine congrArg (Array.ofFn (n := v.size / 2)) (funext fun i => ?_)
  have h1 := foldLowOnce_inside v i.val i.isLt
  have h0 : 2 * i.val < v.size := by omega
  have e0 : v.getD (2 * i.val) zeroE = v[2 * i.val] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h0, Option.getD_some]
  have e1 : v.getD (2 * i.val + 1) zeroE = v[2 * i.val + 1] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1, Option.getD_some]
  show maddE (v.getD (2 * i.val) zeroE) g
    (subE (v.getD (2 * i.val + 1) zeroE) (v.getD (2 * i.val) zeroE)) = _
  rw [e0, e1]

/-- **Entry c of the folded table reads as foldV.** -/
theorem foldV_reads (n l : ℕ) (T : Array E) (g : List E) (hg : g.length = n) (hT : TabFits n l T)
    (c : Fin l) : readV (foldLow T g) c.val = foldV (readP n g) (tabRead n l T) c := by
  subst hg
  rw [readV_foldLowB_of g T l hT, sum_range_cube]
  exact Finset.sum_congr rfl fun β _ => by rw [eqW_rowNo]; rfl

theorem size_foldLow_fits (n l : ℕ) (T : Array E) (g : List E) (hg : g.length = n)
    (hT : TabFits n l T) : (foldLow T g).size = l := by
  rw [size_foldLowB, hg, hT, Nat.mul_div_cancel _ (Nat.two_pow_pos n)]

section Stage
variable (s : Sg)

theorem preP_reads (g : List E) : preP s (readP (s.h + s.g) g) = readP s.h (g.take s.h) := by
  funext i
  show readL g i.val = readL (g.take s.h) i.val
  unfold readL
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt i.isLt]

/-- **THE THREE FOLDED MESSAGES**, from the main table, the mask table and the third table. -/
theorem foldMsg_reads (TM TZ TF : Array E) (g : List E) (hg : g.length = s.h + s.g)
    (hM : TabFits (s.h + s.g) s.C.l TM) (hZ : TabFits s.h s.Z.l TZ) (hF : TabFits s.h s.Z.l TF) :
    foldMsg s (Sum.elim (tabRead (s.h + s.g) s.C.l TM) (tabRead s.h s.Z.l TZ))
        (tabRead s.h s.Z.l TF) (readP (s.h + s.g) g) =
      Sum.elim (fun c => readV (foldLow TM g) c.val)
        (Sum.elim (fun c => readV (foldLow TZ (g.take s.h)) c.val)
          fun c => readV (foldLow TF (g.take s.h)) c.val) := by
  have h2 : (g.take s.h).length = s.h := by rw [List.length_take, hg]; omega
  funext j
  rcases j with c | c | c
  · exact (foldV_reads _ _ TM g hg hM c).symm
  · show foldV (preP s (readP (s.h + s.g) g)) _ c = _
    rw [preP_reads]
    exact (foldV_reads _ _ TZ _ h2 hZ c).symm
  · show foldV (preP s (readP (s.h + s.g) g)) _ c = _
    rw [preP_reads]
    exact (foldV_reads _ _ TF _ h2 hF c).symm

/-- **THE THREE FOLDED TAILS**, from three tables of tails. -/
theorem foldTl_reads (RM RZ RF : Array E) (g : List E) (hg : g.length = s.h + s.g)
    (hM : TabFits (s.h + s.g) s.C.r RM) (hZ : TabFits s.h s.Z.r RZ) (hF : TabFits s.h s.Z.r RF) :
    foldTl s (Sum.elim (tabRead (s.h + s.g) s.C.r RM) (tabRead s.h s.Z.r RZ))
        (tabRead s.h s.Z.r RF) (readP (s.h + s.g) g) =
      Sum.elim (fun c => readV (foldLow RM g) c.val)
        (Sum.elim (fun c => readV (foldLow RZ (g.take s.h)) c.val)
          fun c => readV (foldLow RF (g.take s.h)) c.val) := by
  have h2 : (g.take s.h).length = s.h := by rw [List.length_take, hg]; omega
  funext j
  rcases j with c | c | c
  · exact (foldV_reads _ _ RM g hg hM c).symm
  · show foldV (preP s (readP (s.h + s.g) g)) _ c = _
    rw [preP_reads]
    exact (foldV_reads _ _ RZ _ h2 hZ c).symm
  · show foldV (preP s (readP (s.h + s.g) g)) _ c = _
    rw [preP_reads]
    exact (foldV_reads _ _ RF _ h2 hF c).symm

end Stage

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.tabFits_iff
#print axioms Johnson.Prover.Link.foldLowOnce_inside
#print axioms Johnson.Prover.Link.foldLowOnce_eq
#print axioms Johnson.Prover.Link.foldV_reads
#print axioms Johnson.Prover.Link.size_foldLow_fits
#print axioms Johnson.Prover.Link.preP_reads
#print axioms Johnson.Prover.Link.foldMsg_reads
#print axioms Johnson.Prover.Link.foldTl_reads
