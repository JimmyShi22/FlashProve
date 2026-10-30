-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/FirstStateTest.lean: the proposition `StateAt`
(Johnson/Desc/K12/Honest/FirstState.lean) as a test with code, `stateB`, so that it can be checked
at a value by an evaluation, and the theorem that the test's "true" gives `StateAt`. `StateAt` says
that a first stage's state holds the members' rows at the layout's blocks, and 0 elsewhere. General
in the stage, the plain data, the state and the rows. Definitions with code and theorems. It depends
on no frame for an honest side: no file under Johnson/Desc/ProofFile/Honest/ is among its imports,
direct or indirect.

In the list: a is a stage of the proximity test (`Fmt.M1.Stage`, Fmt/M1Types.lean): the code `a.C`
for main rows, the code `a.Z` for mask rows, and numbers, of which `a.k` and `a.h` are read here. A
code (`Fmt.M1.Code`, Fmt/M1Codes.lean) has messages of `l` entries and tails of `r` entries. Dp is
the plain data of a group (`Plain`, Johnson/Desc/K12/Law/FirstOk.lean); read here are its list of
members `Dp.mems` and its layout `Dp.L`. A member (`Seat1`, same file) is an oracle message as a
part of a tree; `sh.mainRows` and `sh.maskRows` are its numbers of main and mask rows, and its
number j is its position in the list. `oM Dp.L j` and `oZ Dp.L j` (same file) are the first rows of
member j's blocks in the main and the mask table, 0 where the layout names none. P is a state (`PS`,
Johnson/Prover/Link/BodyState.lean): what a prover holds at a stage, as functions of numbers: the
main table `tabM`, the mask table `tabZ`, their rows' tails `tM` and `tZ`, the fresh table's rows
`fM` and tails `fT`. Entry e of row b is `P.tabM (b + 2 ^ kk a * e)` in the main table and
`P.tabZ (b + 2 ^ a.h * e)` in the mask table; `kk a` (FirstOk.lean) is `a.h + (a.k - a.h)`. R is the
rows as plain functions of numbers (`PlainRows`, Johnson/Desc/K12/Honest/FirstRows.lean): each
member's main rows `M`, their tails `T`, its mask rows `Z`, their tails `ZT`; the fresh table's rows
`F` and tails `FT`.

  `stateAt_of`: if `stateB a Dp P R` is true, `StateAt a Dp P R` holds. No other hypothesis
  `stateB a Dp P R`: a definition: the test. It has four parts, and all must pass. (1) For every
    member j and every i below its number of main rows: row `oM Dp.L j` + i of the main table agrees
    with `R.M j i` below `a.C.l`, and that row's tail with `R.T j i` below `a.C.r`; the same for its
    mask rows, with `oZ`, the mask table, `R.Z`, `R.ZT` and `a.Z`. (2) Every row b < 2 ^ `kk a` of
    the main table lies in some member's block of main rows, or the row is 0 below `a.C.l` and its
    tail is 0 below `a.C.r`. (3) The same for every row b < 2 ^ `a.h` of the mask table, with mask
    rows and `a.Z`. (4) For every b < 2 ^ `a.h`: `P.fM b` agrees with `R.F b` below `a.Z.l`, and
    `P.fT b` with `R.FT b` below `a.Z.r`
  `inBlockB o n b`: a definition: `InBlock o n b` (FirstState.lean) as a test: the row number b lies
    in the block of n rows from row o on
  `rowB n f g`: a definition: the functions f and g agree at every number below n; two values are
    compared by `sameE` (Johnson/Desc/K12/Honest/FirstTest.lean)
  `row_of`: if `rowB n f g` is true, then f e = g e for every e < n
  `any_false`: if b lies in no member's block (`InBlock`), the search over the members by `inBlockB`
    returns false. General in the two functions that give a block's first row and its number of rows

By what. `row_of` follows from `same_of` and `all_range` (both in FirstTest.lean). `stateAt_of`
unfolds `stateB` and proves the eight fields of `StateAt` one by one, by `all_range` and `row_of`.
It gets a member's part of the test by `mem_zipIdx_get` (Johnson/Desc/K12/Law/FirstOkLaw.lean). At
the two fields on rows in no member's block it removes the search by `any_false`.

Limits. A "true" of the test at a value is an evaluation by Lean's evaluator, outside the kernel.
Nothing is evaluated here; `#guard` lines in Johnson/Desc/ProofFile/Honest/K12/ToyGroup.lean and
ToyTrees.lean evaluate the test at small made-up values, through `At.state` and `At.stateUp`
(ToyAt.lean, same folder). The test runs over every row of the tables and every entry below the
codes' lengths: it is for small sizes. Entries at or beyond these lengths are not compared. Only the
direction from the test to `StateAt` is stated. Nothing on completeness, on soundness or on what is
hidden.
-/
import Johnson.Desc.K12.Honest.FirstState
import Johnson.Desc.K12.Honest.FirstTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open H2K.First
open Johnson.Prover.Link (PS)

/-- `InBlock o n b` as a test: the row number b lies in the block of n rows from row o on. -/
def inBlockB (o n b : ℕ) : Bool := decide (o ≤ b) && decide (b < o + n)

/-- The functions f and g agree at every number below n. -/
def rowB (n : ℕ) (f g : ℕ → GE) : Bool := (List.range n).all fun e => sameE (f e) (g e)

theorem row_of {n : ℕ} {f g : ℕ → GE} (h : rowB n f g = true) (e : ℕ) (he : e < n) : f e = g e :=
  same_of (all_range h e he)

/-- `StateAt` as a test. -/
def stateB (a : Fmt.M1.Stage) (Dp : Plain) (P : PS) (R : PlainRows) : Bool :=
  (Dp.mems.zipIdx.all fun s =>
    ((List.range s.1.sh.mainRows).all fun i =>
      rowB a.C.l (fun e => P.tabM (oM Dp.L s.2 + i + 2 ^ kk a * e)) (R.M s.2 i) &&
      rowB a.C.r (P.tM (oM Dp.L s.2 + i)) (R.T s.2 i)) &&
    (List.range s.1.sh.maskRows).all fun i =>
      rowB a.Z.l (fun e => P.tabZ (oZ Dp.L s.2 + i + 2 ^ a.h * e)) (R.Z s.2 i) &&
      rowB a.Z.r (P.tZ (oZ Dp.L s.2 + i)) (R.ZT s.2 i)) &&
  ((List.range (2 ^ kk a)).all fun b =>
    (Dp.mems.zipIdx.any fun s => inBlockB (oM Dp.L s.2) s.1.sh.mainRows b) ||
    (rowB a.C.l (fun e => P.tabM (b + 2 ^ kk a * e)) (fun _ => 0) &&
      rowB a.C.r (P.tM b) fun _ => 0)) &&
  ((List.range (2 ^ a.h)).all fun b =>
    (Dp.mems.zipIdx.any fun s => inBlockB (oZ Dp.L s.2) s.1.sh.maskRows b) ||
    (rowB a.Z.l (fun e => P.tabZ (b + 2 ^ a.h * e)) (fun _ => 0) &&
      rowB a.Z.r (P.tZ b) fun _ => 0)) &&
  (List.range (2 ^ a.h)).all fun b => rowB a.Z.l (P.fM b) (R.F b) && rowB a.Z.r (P.fT b) (R.FT b)

/-- If b lies in no member's block, the search over the members returns false. -/
theorem any_false (Dp : Plain) (first : ℕ → ℕ) (rows : Seat1 → ℕ) (b : ℕ)
    (h : ∀ j : Fin Dp.mems.length, ¬ InBlock (first j.val) (rows (Dp.mems.get j)) b) :
    (Dp.mems.zipIdx.any fun s => inBlockB (first s.2) (rows s.1) b) = false := by
  rw [List.any_eq_false]
  rintro ⟨s, i⟩ hs hb
  rw [List.mem_zipIdx_iff_getElem?] at hs
  have hs' : Dp.mems[i]? = some s := hs
  obtain ⟨hi, hsi⟩ := List.getElem?_eq_some_iff.1 hs'
  simp only [inBlockB, Bool.and_eq_true, decide_eq_true_eq] at hb
  refine h ⟨i, hi⟩ ?_
  show InBlock (first i) (rows Dp.mems[i]) b
  rw [hsi]
  exact hb

/-- **The test's "true" gives `StateAt`.** -/
theorem stateAt_of {a : Fmt.M1.Stage} {Dp : Plain} {P : PS} {R : PlainRows}
    (hB : stateB a Dp P R = true) : StateAt a Dp P R := by
  simp only [stateB, Bool.and_eq_true] at hB
  obtain ⟨⟨⟨hM, hfM⟩, hfZ⟩, hF⟩ := hB
  have hm : ∀ j : Fin Dp.mems.length, _ := fun j =>
    List.all_eq_true.1 hM _ (mem_zipIdx_get Dp.mems j)
  simp only [Bool.and_eq_true] at hm
  refine ⟨fun j i e hi he => ?_, fun j i q hi hq => ?_, fun j i e hi he => ?_,
    fun j i q hi hq => ?_, fun b hb hfree => ?_, fun b hb hfree => ?_, fun b e hb he => ?_,
    fun b q hb hq => ?_⟩
  · have h := all_range (hm j).1 i hi
    rw [Bool.and_eq_true] at h
    exact row_of h.1 e he
  · have h := all_range (hm j).1 i hi
    rw [Bool.and_eq_true] at h
    exact row_of h.2 q hq
  · have h := all_range (hm j).2 i hi
    rw [Bool.and_eq_true] at h
    exact row_of h.1 e he
  · have h := all_range (hm j).2 i hi
    rw [Bool.and_eq_true] at h
    exact row_of h.2 q hq
  · have h := all_range hfM b hb
    rw [any_false Dp (oM Dp.L) (·.sh.mainRows) b hfree, Bool.false_or, Bool.and_eq_true] at h
    exact ⟨fun e he => row_of h.1 e he, fun q hq => row_of h.2 q hq⟩
  · have h := all_range hfZ b hb
    rw [any_false Dp (oZ Dp.L) (·.sh.maskRows) b hfree, Bool.false_or, Bool.and_eq_true] at h
    exact ⟨fun e he => row_of h.1 e he, fun q hq => row_of h.2 q hq⟩
  · have h := all_range hF b hb
    rw [Bool.and_eq_true] at h
    exact row_of h.1 e he
  · have h := all_range hF b hb
    rw [Bool.and_eq_true] at h
    exact row_of h.2 q hq

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.row_of
#print axioms ProofFile.Honest.K12.any_false
#print axioms ProofFile.Honest.K12.stateAt_of
#print axioms ProofFile.Honest.K12.inBlockB
#print axioms ProofFile.Honest.K12.rowB
#print axioms ProofFile.Honest.K12.stateB
