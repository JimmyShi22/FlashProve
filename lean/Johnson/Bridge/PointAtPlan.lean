-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/PointAtPlan.lean: the shared point of the test on a stored table, at a table of the
planner's. From a yes of two tests on numbers, the library's condition on the fold and the planner's
cover of the block's error for N requests hold at one count.

`point_both` (Johnson/Bridge/PointBoth.lean) has the pair under twenty hypotheses. Six of them
follow from a yes of `linPointTest` (OnBytes/Tie/Pv/LinPortB.lean), a test in the planner's own
arithmetic. Nine more, which speak of numbers alone, follow from a yes of one more test here,
`foldTest`: the code's sizes, the two radii in order and below the distance, the radius below the
Johnson radius. Five remain. `Sz.RadJ` (OnBytes/Slice/LinkRecBchks.lean) has the clauses of
`foldTest` as a proposition on the link's sizes.
Main names, in the namespace `Cb.Bridge`:
  `codeOfSize c`: the planner's code as a code of the format.
  `foldTest T e eM`: the test. `foldTest_sound`: what a yes gives.
  `point_both_of_tests`: the pair from a yes of both tests, for every test P on a table under that
    code with the radii e and eM.
  `foldTest_full`, `foldTest_small`: a yes, evaluated in the kernel, at the tables `recordTable` and
    `smallRecordTable` (OnBytes/Params/) and the radii 2,852,142,980 and 6,137,119.
  `foldTest_full_beyond`, `foldTest_small_beyond`, `foldTest_long`: the test can say no: just beyond
    the Johnson radius at both tables, and at a code of length 2^33.
`point_both_of_tests` rests on the files under ThirdParty/, through `Cb.Bridge.bchks46At`: files
adapted from ArkLib and Mathlib
(lean/LIMITS.md, L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.
Limits: the test P is a parameter. That its matrix is the format's, that its numbers of row and
column variables are the table's and the sizes', that the field has as many elements as the setting
says, and what `close` has tested of the round are hypotheses. `linPointTest` is evaluated nowhere
here. A yes of `foldTest` alone says nothing on the size of the count: it says yes up to the last
radius below the Johnson radius, where, by arithmetic outside Lean, the count at `recordTable` is
above the number of all fold points. The radius is kept small by `linPointTest`; that the price is
small is not said here. That `ptCount` at these tables and radii is the count of
Johnson/Bridge/PointFull.lean and PointSmall.lean [neither is in this library] is not shown here.
That a proof file's plan has
these tables and radii is not shown. The condition speaks of the tables without a collision at the
record's seed. Nothing on the soundness of the check of a file.

-/
import Johnson.Bridge.PointBoth
import OnBytes.Params.EntryStagesRecord
import OnBytes.Params.EntryStagesRecordSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Bridge
open Iop Prob Cb Cb.Ood _root_.Run Blocks OnBytes OnBytes.Slice OnBytes.Params Cb.Pv Cb.Pv.Lin

/-- The planner's code as a code of the format. -/
def codeOfSize (c : CodeSize) : Fmt.M1.Code := ⟨c.logN, c.ell, c.r⟩

/-- The test on the code's sizes and the two radii. -/
def foldTest (T : TableSize) (e eM : ℕ) : Bool :=
  decide (T.code.logN ≤ 32) && decide (0 < T.code.r + T.code.ell - 1) &&
    decide (T.code.r + T.code.ell ≤ 2 ^ T.code.logN) && decide (0 < e) && decide (e ≤ eM) &&
    decide (eM < 2 ^ T.code.logN - (T.code.r + T.code.ell) + 1) &&
    decide (2 ^ T.code.logN * (2 ^ T.code.logN - (2 ^ T.code.logN - (T.code.r + T.code.ell) + 1)) <
      (2 ^ T.code.logN - e) ^ 2)

/-- What a yes of the test gives. -/
theorem foldTest_sound {T : TableSize} {e eM : ℕ} (h : foldTest T e eM = true) :
    (wordOf T.code).n = 2 ^ (codeOfSize T.code).a ∧
      (wordOf T.code).k = (codeOfSize T.code).r + (codeOfSize T.code).l - 1 ∧
      (codeOfSize T.code).a ≤ 32 ∧ 0 < (codeOfSize T.code).r + (codeOfSize T.code).l - 1 ∧
      (codeOfSize T.code).r + (codeOfSize T.code).l ≤ 2 ^ (codeOfSize T.code).a ∧ 0 < e ∧ e ≤ eM ∧
      eM < 2 ^ (codeOfSize T.code).a - ((codeOfSize T.code).r + (codeOfSize T.code).l) + 1 ∧
      InJohnson (2 ^ (codeOfSize T.code).a)
        (2 ^ (codeOfSize T.code).a - ((codeOfSize T.code).r + (codeOfSize T.code).l) + 1) e := by
  unfold foldTest at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h
  refine ⟨rfl, ?_, a0, a1, a2, a3, a4, a5, a6⟩
  show T.code.k = T.code.r + T.code.ell - 1
  unfold CodeSize.k CodeSize.dim
  have hne : (T.code.ell + T.code.r == 0) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  rw [hne]
  simp only [Bool.false_eq_true, if_false]
  omega

/-- **The condition on the fold and the planner's cover for at most N requests, at one count, from
a yes of two tests**; five hypotheses on the block P and the round remain. -/
theorem point_both_of_tests {s : Setting} {T : TableSize} {x : LinSize} (c : Scope) {N : ℕ}
    {J Y : Type} [Fintype J]
    (P : LdLinP GE (Fin (2 ^ (codeOfSize T.code).a))
      (Fin ((codeOfSize T.code).r + (codeOfSize T.code).l)) J Y)
    (h1 : foldTest T P.e' P.D.X.eM = true) (h2 : linPointTest s T x P.e' N = true)
    (hG : P.D.X.G = genOf (codeOfSize T.code)) (hv : P.D.X.v = T.v) (hkl : P.D.klo = x.kLo)
    (hq : Fintype.card GE = s.cardE) (hg : (linPoint s T x).Good s c) :
    P.FoldErr (fun f rec => ¬ P.D.X.Coll f rec.1) (ptCount T P.e' s.cardE) ∧
      Covered s c (P.errPtB (ptCount T P.e' s.cardE) N, Fintype.card P.D.Pt) (linPoint s T x) := by
  obtain ⟨hn, hw, ha, hk, hr, he, hle, hM, hJ⟩ := foldTest_sound h1
  unfold linPointTest at h2
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h2
  obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, _⟩, a5⟩, a6⟩, a7⟩, _⟩ := h2
  have ej := linProx_johnson (s := s) (T := T) x a1 a2
  have hd : EnclR (linProx s T x).delta (1 - (wordOf T.code).agreeAt (linM T x) true) := by
    rw [ej]
    exact enclR_johnson_delta _ _ _
  have hrad : (P.e' : ℝ) ≤
      (1 - (wordOf T.code).agreeAt (linM T x) true) * ((wordOf T.code).n : ℝ) :=
    le_trans (by exact_mod_cast a6) (lowerRadius_le hd a5)
  exact point_both (codeOfSize T.code) P c hn hw hv ha hk hr hG he hle hM hJ a1 a2 a3 hrad a7 hq
    hkl hg

/-! ### the test at `recordTable` and `smallRecordTable`, and that it can say no -/

theorem foldTest_full : foldTest recordTable 2852142980 2852142980 = true := by decide +kernel

theorem foldTest_small : foldTest smallRecordTable 6137119 6137119 = true := by decide +kernel

/-- Just beyond the Johnson radius the test says no. -/
theorem foldTest_full_beyond : foldTest recordTable 2909855953 2909855953 = false := by
  decide +kernel

theorem foldTest_small_beyond : foldTest smallRecordTable 6164247 6164247 = false := by
  decide +kernel

/-- At a code of length 2^33 the test says no, whatever the radii. -/
theorem foldTest_long (e eM : ℕ) :
    foldTest { recordTable with code := { recordTable.code with logN := 33 } } e eM = false := by
  unfold foldTest
  simp

end Cb.Bridge

#print axioms Cb.Bridge.foldTest_sound
#print axioms Cb.Bridge.point_both_of_tests
#print axioms Cb.Bridge.foldTest_full
#print axioms Cb.Bridge.foldTest_small
#print axioms Cb.Bridge.foldTest_full_beyond
#print axioms Cb.Bridge.foldTest_small_beyond
#print axioms Cb.Bridge.foldTest_long
