-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/SliceFoldl.lean: a fold over the characters of a string's slice is the fold over the
list of its characters; and `String.toNat?` in a form that Lean's kernel can evaluate, with the
equation between the two, at all strings.

Adapted from Lean 4's core library (toolchain v4.29.1): `String.Slice.isNat`, `String.Slice.toNat?`.
What is theirs: the two routines' text, as Lean prints their bodies. What is ours: the same text
over a list of characters (`isNatL`, `toNatL`) and the laws. `slice_foldl` copies no text of the
library: it calls two of its theorems by name. `isNatL`'s docstring restates one comment of theirs.
Licence of the adapted text, from the toolchain's own file LICENSE (71 lines;
sha256 8b28515ffffc5c0fe2807d8ae3735b00b324d9b7ce807dd63ff6ac8922fbce7e): its first lines are
"Apache License 2.0 (Apache)", "Apache License", "Version 2.0, January 2004".
The adapted file's own header, from the toolchain's sources
(src/lean/Init/Data/String/Slice.lean, 1121 lines, sha256
17a6b40832a0e135badbdf43e51e90bbabb6a16832e22ee07ad24d54f55cd07f; the two definitions stand at its
lines 903 and 942):
  Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Henrik Böving, Markus Himmel

Why. `String.toNat?` and `String.isNat` (and their likes on slices) are folds `String.Slice.foldl`,
which is `Std.Iter.fold` over the slice's iterator of characters. Asked by `decide +kernel` whether
`"12".toNat?` is `some 12`, Lean reports that the instance "did not reduce to `isTrue` or
`isFalse`": the kernel's check fails, at an input so small that no limit can be at work (seen at
this one string). Our reading: beneath the fold (found by listing the constants that its definition
reaches) stands `WellFounded.extrinsicFix`, whose text asks classically whether its relation is
well-founded, and that question is not evaluated there. So a closed statement whose evaluation
reaches such a fold is not had that way. No theorem of the library (toolchain v4.29.1, as far as our
tree imports it) names `String.toNat?`, `String.isNat` or `String.Slice.foldl`.

Main names.
  `slice_foldl`: `String.Slice.foldl f a s = s.copy.toList.foldl f a`: from the library's
    `String.Slice.toList_chars` and `Std.Iter.foldl_toList`.
  `slice_isEmpty`: a slice is empty just if its list of characters is.
  `isNatL cs`: the library's test on a list of characters. By reading its fold (no lemma says it
    here): it accepts just where the list is not empty, every character is a digit '0' to '9' or
    '_', the first is not '_', no two '_' stand side by side, and the last is a digit.
  `toNatL cs`: `none` where `isNatL` rejects; else the digits read in base ten, every '_' passed
    over.
  `toNat?_eq`: `s.toNat? = toNatL s.toList`; `isNat_eq`; `slice_toNat?_eq`, `slice_isNat_eq`: the
    same for slices, over `s.copy.toList`. No premise at any.
How to use it: `simp only [toNat?_eq, slice_toNat?_eq]` (it reaches under binders), then
`decide +kernel`.
Tests: `tests` (eleven strings: the empty one, letters, three digits, '_' inside, in front, behind
and doubled, two digits that are not ASCII, a blank in front, zeros in front); `under_a_binder`;
`numerals` (the 26 numerals "0" to "25"); negative: `twelve_no`. In `tests` and `numerals` the bare
`String.toNat?` under `List.map` is no instance of the law: `List.map` is laid open first.

Limits. The laws unfold four definitions of the library by name: another toolchain may spell them
otherwise. What `isNatL` accepts is said above by reading, not by a lemma. No import: Lean's own
library alone.

-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds

universe u

/-- **A fold over a slice's characters is the fold over the list of its characters.** -/
theorem slice_foldl {α : Type u} (f : α → Char → α) (a : α) (s : String.Slice) :
    String.Slice.foldl f a s = s.copy.toList.foldl f a := by
  show Std.Iter.fold f a s.chars = _
  rw [← String.Slice.toList_chars]
  exact Std.Iter.foldl_toList.symm

/-- A slice is empty just if its list of characters is. -/
theorem slice_isEmpty (s : String.Slice) : s.isEmpty = s.copy.toList.isEmpty := by
  rw [Bool.eq_iff_iff, ← String.Slice.copy_eq_empty_iff, List.isEmpty_iff,
    String.toList_eq_nil_iff]

/-- `String.Slice.isNat` on a list of characters. The four flags of its fold: is this the first
character; was the last one '_'; was the last one a digit; has every test so far held. -/
def isNatL (cs : List Char) : Bool :=
  if cs.isEmpty then false
  else
    let r := cs.foldl (fun (x : Bool × Bool × Bool × Bool) c =>
      (false, decide (c = '_'), c.isDigit,
        x.2.2.2 && (c.isDigit || decide (c = '_')) && !(x.1 && decide (c = '_')) &&
          !(x.2.1 && decide (c = '_')))) (true, false, false, true)
    r.2.2.2 && r.2.2.1

/-- `String.Slice.toNat?` on a list of characters. -/
def toNatL (cs : List Char) : Option Nat :=
  if isNatL cs then
    some (cs.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) 0)
  else none

/-- `String.Slice.isNat` is `isNatL` of the slice's characters. -/
theorem slice_isNat_eq (s : String.Slice) : s.isNat = isNatL s.copy.toList := by
  simp only [String.Slice.isNat, isNatL, slice_foldl, slice_isEmpty]

/-- `String.Slice.toNat?` is `toNatL` of the slice's characters. -/
theorem slice_toNat?_eq (s : String.Slice) : s.toNat? = toNatL s.copy.toList := by
  simp only [String.Slice.toNat?, String.Slice.isNat, toNatL, isNatL, slice_foldl, slice_isEmpty]

/-- `String.isNat` is `isNatL` of the string's characters. -/
theorem isNat_eq (s : String) : s.isNat = isNatL s.toList := by
  rw [String.isNat, slice_isNat_eq, String.copy_toSlice]

/-- **`String.toNat?` is `toNatL` of the string's characters**, at all strings. -/
theorem toNat?_eq (s : String) : s.toNat? = toNatL s.toList := by
  rw [String.toNat?, slice_toNat?_eq, String.copy_toSlice]

/-- Eleven strings. -/
theorem tests :
    ["", "abc", "123", "1_0", "_1", "1_", "1__0", "\u0661\u0662", " 1", "007",
      "12"].map String.toNat? =
      [none, none, some 123, some 10, none, none, none, none, none, some 7, some 12] := by
  simp only [List.map, toNat?_eq]
  decide +kernel

/-- Under a binder: the law is rewritten inside the function that is mapped. -/
theorem under_a_binder :
    ["7", "x", "40"].map (fun s => (s.toNat?).getD 99) = [7, 99, 40] := by
  simp only [toNat?_eq]
  decide +kernel

/-- A negative test: "12" is not read as 13. -/
theorem twelve_no : "12".toNat? ≠ some 13 := by
  simp only [toNat?_eq]
  decide +kernel

/-- The 26 numerals from "0" to "25" are read as their numbers. -/
theorem numerals :
    ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12", "13", "14", "15",
      "16", "17", "18", "19", "20", "21", "22", "23", "24", "25"].map String.toNat? =
      (List.range 26).map some := by
  simp only [List.map, toNat?_eq]
  decide +kernel

end Johnson.Unfolds

#print axioms Johnson.Unfolds.slice_foldl
#print axioms Johnson.Unfolds.slice_isEmpty
#print axioms Johnson.Unfolds.slice_isNat_eq
#print axioms Johnson.Unfolds.slice_toNat?_eq
#print axioms Johnson.Unfolds.isNat_eq
#print axioms Johnson.Unfolds.toNat?_eq
#print axioms Johnson.Unfolds.tests
#print axioms Johnson.Unfolds.under_a_binder
#print axioms Johnson.Unfolds.twelve_no
#print axioms Johnson.Unfolds.numerals
