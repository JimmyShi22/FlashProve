-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinAnswersKnown.lean: a test of the out-of-domain (OOD) answers of the committer that
runs (`Bind.Twin.answers`, Johnson/Bind/Twin.lean) at a toy shape with TWO answers a row, against
sums that were computed outside Lean. Tests alone: each is a #guard, which Lean's evaluator runs
when the file is compiled; a #guard leaves no theorem.

Why. The statements of Johnson/Bind/TwinAnswers.lean hold for every number of answers a row, and are
taken at a shape with one. Here the number is two: so the test feels which seed goes with which
block of three pads, and the order "by row, within a row by seed".
The shape: 2 rows; 10 entries in a row's message, of which 4 are plain and 6 are pads; 2 answers.
Two seeds, each a point of two coordinates and a factor. The committer itself would sample points of
four coordinates at this shape; `answers` takes the seeds as they are given, and the four places
fill the cube of two. One plain entry is the prime plus 5 and one pad is the prime minus 1.
The four expected triples: answer i of row b is the sum over the places q < 4 of eq(q; z_i) times
the entry (b, q), plus the factor of seed i times pad(b, 3 i) + pad(b, 3 i + 1) X + pad(b, 3 i + 2)
X^2, in the field of p = 2^64 - 2^32 + 1 elements extended by X^3 = 2; eq(q; z) is the product over
t of z_t where bit t of q is 1 and of 1 - z_t where it is 0. They were computed by a short program
written for this test, in another language, with whole numbers of any size, before this file was
first compiled.
A second shape, with 11 entries in a row's message: 5 plain places, and points of four coordinates,
as the committer samples them there: so the places leave the cube partly empty, as the full size's
do, and the factors 1 - z_t at the coordinates above the places' bits are felt. Its four sums were
computed by three programs of three writers, which agree.
Negative tests: with the two seeds swapped, with the two blocks of pads swapped, and with the two
rows swapped the lists part; at the second shape, with each point cut to three coordinates.
Limits. Two toy shapes, one table. No pad from the prime on. No value here was computed by the
programs (the C++ implementation that comes with this Lean code). Table and seeds are synthetic:
written in this file: no model's weights enter. The programs that computed the sums are not in the
repository.

-/
import Johnson.Bind.Twin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin
namespace AnswersKnown

open Fmt (Ext)

/-- The toy shape: two rows, four plain entries, two answers a row. -/
def shape : Shape := ⟨3, 10, 1, 1, 2, 4⟩

/-- The plain entries. -/
def entry (b e : Nat) : UInt64 :=
  if b = 1 ∧ e = 3 then 18446744069414584326 else UInt64.ofNat (1000 * (b + 1) + 7 * e + 1)

/-- The pads. -/
def pad (b k : Nat) : UInt64 :=
  if b = 0 ∧ k = 4 then 18446744069414584320 else UInt64.ofNat (500 * (b + 1) + 11 * k + 2)

/-- The table. Tails and salts are not read by the answers. -/
def table : Table := ⟨entry, fun _ _ => 0, pad, fun _ => ByteArray.empty⟩

/-- The two seeds. -/
def seeds : List (List Ext × Ext) :=
  [([(3, 5, 7), (11, 13, 17)], (19, 23, 29)), ([(31, 37, 41), (43, 47, 53)], (59, 61, 67))]

/-- The four sums, computed outside Lean: row 0 under seed 0, under seed 1; row 1 likewise. -/
def expected : List Ext :=
  [(64572, 51902, 36600),
    (101205, 108131, 69676),
    (18446744069413934848, 18446744069414016579, 18446744069414267140),
    (18446744069396544471, 18446744069399938027, 18446744069404403399)]

#guard answers shape table seeds == expected
-- negative tests: the seeds swapped; the blocks of pads swapped; the rows swapped
#guard !(answers shape table seeds.reverse == expected)
#guard !(answers shape { table with pad := fun b k => pad b ((k + 3) % 6) } seeds == expected)
#guard !(answers shape { table with entry := fun b => entry (1 - b), pad := fun b => pad (1 - b) }
  seeds == expected)

/-- The second shape: five plain entries; the committer's points have four coordinates there. -/
def shape5 : Shape := ⟨3, 11, 1, 1, 2, 4⟩

/-- Two seeds with points of four coordinates. -/
def seeds5 : List (List Ext × Ext) :=
  [([(3, 5, 7), (11, 13, 17), (71, 73, 79), (83, 89, 97)], (19, 23, 29)),
    ([(31, 37, 41), (43, 47, 53), (101, 103, 107), (109, 113, 127)], (59, 61, 67))]

/-- The four sums at the second shape, computed outside Lean. -/
def expected5 : List Ext :=
  [(18446744034001396445, 18446744040980415268, 18446744047002277968),
    (18446742441470502514, 18446742772198542117, 18446743042342526552),
    (18446743925268939641, 18446743953805806132, 18446743978190219611),
    (18446737635666094200, 18446738943165582022, 18446740010320727828)]

#guard shape5.cube == 4 && shape5.plain == 5
#guard answers shape5 table seeds5 == expected5
-- negative test: each point cut to three coordinates
#guard !(answers shape5 table (seeds5.map fun y => (y.1.take 3, y.2)) == expected5)

end AnswersKnown
end Bind.Twin
