-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB8/Typed.lean: the numbers of a key file's three later proximity tests' places,
which Written.lean in this folder has "by formula", are these typed numbers. A tool, and closed
statements by evaluations in Lean's kernel.

Why. Johnson/Desc/K12/Law/PlacesKeyFull.lean (`H2K.Member.piKUFull`, `piKOFull`, `piKWFull`) has the
three places as typed numbers, made by a program off a print of Lean's evaluator of
`Key.laterPlaces` at the library's full-size texts of the three public files. That file is not
imported here. The typed sides here were typed by hand after that file's text: the seven numbers of
`nums`, idx, answers and early; the first group after the groups of the first tenants there. So
where both files lie, the tie is one evaluation a place.

Main names.
  `Same7`, `SameP`; `nums_of_same`, `place_of_same`: two tests' numbers, and two places' numbers,
    are one if they agree field by field: so that the kernel is asked for a conjunction.
  `uT rows`, `oT`, `wT`: the typed places. `u_typed`, `o_typed`, `w_typed`: the formulas give them.
  `u_bent`, `o_bent`, `w_bent`: the same tests with one value moved on the typed side (65 rows for
    66; the first group 5 for 6; no idx) say no.

A name that ends in `_bent`: the same test with one value changed, at which it says no: so the test
is seen to be able to fail.

Limits. It holds formulas at typed sizes against typed numbers. That the typed numbers are that
file's rests on a reading by hand, and that they are what `Key.laterPlaces` returns rests on that
print: no theorem. chain and start are typed alike on both sides here: that file has no start. The
ranges' place has no typed value there. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB8.Written

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB8

/-! ## The tool -/

/-- Two tests' numbers agree field by field. -/
def Same7 (N N' : H2U.TestNums) : Prop :=
  N.rows = N'.rows ∧ N.work = N'.work ∧ N.stages = N'.stages ∧ N.ownMask = N'.ownMask ∧
    N.first = N'.first ∧ N.free = N'.free ∧ N.firstTree = N'.firstTree

instance (N N' : H2U.TestNums) : Decidable (Same7 N N') := by
  unfold Same7
  infer_instance

theorem nums_of_same {N N' : H2U.TestNums} (h : Same7 N N') : N = N' := by
  cases N
  cases N'
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  simp only at a b c d e f g
  subst a b c d e f g
  rfl

/-- Two places' numbers agree field by field. -/
def SameP (x y : H2U.PlaceNums) : Prop :=
  x.chain = y.chain ∧ x.start = y.start ∧ Same7 x.nums y.nums ∧ x.idx = y.idx ∧
    x.firstGroup = y.firstGroup ∧ x.answers = y.answers ∧ x.early = y.early

instance (x y : H2U.PlaceNums) : Decidable (SameP x y) := by
  unfold SameP
  infer_instance

theorem place_of_same {x y : H2U.PlaceNums} (h : SameP x y) : x = y := by
  cases x
  cases y
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  have c' := nums_of_same c
  simp only at a b c' d e f g
  subst a b c' d e f g
  rfl

/-! ## The typed places -/

/-- The folded row's place, typed; its rows as a letter, for the test that can fail. -/
def uT (rows : Nat) : H2U.PlaceNums :=
  { chain := 2, start := 8
    nums :=
      { rows := rows, work := 32
        stages :=
          [⟨⟨24, 4194304, 97⟩, ⟨13, 64, 146⟩, 7, 0, 97⟩,
            ⟨⟨21, 131072, 52⟩, ⟨12, 256, 52⟩, 5, 2, 52⟩, ⟨⟨17, 8192, 52⟩, ⟨12, 256, 52⟩, 4, 2, 52⟩,
            ⟨⟨13, 512, 52⟩, ⟨12, 256, 52⟩, 4, 2, 52⟩, ⟨⟨14, 512, 49⟩, ⟨14, 1024, 49⟩, 0, 0, 49⟩]
        ownMask := false, first := [(⟨24, 324, false, 0⟩, .own 0), (⟨13, 3, false, 2⟩, .own 2)]
        free := 3, firstTree := 0 }
    idx := [(0, 0), (1, 1), (2, 1), (3, 1), (4, 2)], firstGroup := 2, answers := 1, early := true }

/-- Omega's place, typed. -/
def oT : H2U.PlaceNums :=
  { chain := 2, start := 43
    nums :=
      { rows := 3, work := 32
        stages :=
          [⟨⟨22, 262144, 98⟩, ⟨13, 64, 146⟩, 4, 0, 49⟩, ⟨⟨18, 16384, 49⟩, ⟨14, 128, 49⟩, 4, 3, 49⟩,
            ⟨⟨14, 1024, 49⟩, ⟨13, 64, 49⟩, 4, 3, 49⟩, ⟨⟨15, 1024, 39⟩, ⟨15, 512, 39⟩, 0, 0, 39⟩]
        ownMask := true, first := [(⟨22, 36, false, 1⟩, .own 1), (⟨13, 3, false, 2⟩, .own 2)]
        free := 7, firstTree := 0 }
    idx := [(5, 0), (6, 3), (7, 4), (8, 5)], firstGroup := 6, answers := 1, early := true }

/-- The own test's place, typed. -/
def wT : H2U.PlaceNums :=
  { chain := 3, start := 0
    nums :=
      { rows := 5, work := 32
        stages :=
          [⟨⟨22, 262144, 98⟩, ⟨13, 256, 49⟩, 5, 1, 49⟩, ⟨⟨18, 16384, 49⟩, ⟨15, 128, 49⟩, 4, 3, 49⟩,
            ⟨⟨15, 2048, 49⟩, ⟨14, 64, 49⟩, 3, 3, 49⟩, ⟨⟨13, 256, 41⟩, ⟨13, 64, 41⟩, 3, 3, 41⟩,
            ⟨⟨15, 256, 29⟩, ⟨15, 256, 29⟩, 0, 0, 29⟩]
        ownMask := false
        first := [(⟨13, 3, false, 0⟩, .taken 0 0), (⟨22, 12, false, 5⟩, .taken 0 5),
          (⟨22, 36, false, 1⟩, .taken 1 1)]
        free := 0, firstTree := 7 }
    idx := [(5, 6), (6, 7), (9, 8), (10, 9), (11, 10)], firstGroup := 5, answers := 1
    early := true }

/-! ## The closed statements -/

theorem u_typed : laterPlacesFull.U = uT 66 := place_of_same (by decide +kernel)

theorem o_typed : laterPlacesFull.O = some oT :=
  congrArg some (place_of_same (x := (laterPlacesFull.O.getD wT)) (by decide +kernel))

theorem w_typed : laterPlacesFull.W = wT := place_of_same (by decide +kernel)

/-- With 65 rows for 66 on the typed side the test says no. -/
theorem u_bent : decide (SameP laterPlacesFull.U (uT 65)) = false := by decide +kernel

/-- With 5 for 6 as the first group on the typed side: no. -/
theorem o_bent :
    decide (SameP (laterPlacesFull.O.getD wT) { oT with firstGroup := 5 }) = false := by
  decide +kernel

/-- With an empty list idx on the typed side: no. -/
theorem w_bent : decide (SameP laterPlacesFull.W { wT with idx := [] }) = false := by
  decide +kernel

end Johnson.KB8

#print axioms Johnson.KB8.nums_of_same
#print axioms Johnson.KB8.place_of_same
#print axioms Johnson.KB8.u_typed
#print axioms Johnson.KB8.o_typed
#print axioms Johnson.KB8.w_typed
#print axioms Johnson.KB8.u_bent
#print axioms Johnson.KB8.o_bent
#print axioms Johnson.KB8.w_bent
