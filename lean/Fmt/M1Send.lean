-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1Send.lean: the linear equation (the sample row) that the verifier keeps when it samples a sent
oracle message at a drawn point: block SEND of the first toy.

When the prover of the first toy (a product test) sends an oracle message, the verifier takes a
sample of it (the format page calls it an out-of-domain sample): it draws a random point and a
factor, and the prover answers with one element. The verifier tests nothing at that moment; it
writes down one linear equation, the sample row, which later blocks carry on. This file gives that
row as a total function that computes. It is generic in the field and in the sizes, and serves all
three sendings of the toy. Definitions, and tests at tiny sizes (some at the sizes of the toy's
first sending: part 2 of this head). No Mathlib.

The words. The first toy is a small test protocol of the programs: the prover claims a_i b_i = c_i
for every i, for three rows a, b, c of one oracle message. A block is one step of that protocol,
written here as the verifier's function of what was sent and drawn. eq(j; z) is the multilinear
equality polynomial at the index j: the product over t of z_t if bit t of j is 1 (bit 0 the lowest),
else of 1 - z_t (`eqTab`, Fmt/M1Types.lean).

Sources.
  Written from part 1 of the programs' description of the toy ("the programs": the C++
    implementation that comes with this Lean code). This file's sources include no proof file made
    by the programs and no known answer of theirs for a test, so the tests in this file are this
    library's own.
  Where that description gives the toy's first sending alone, questions were put, and the programs'
  answers
    (their annex on SEND; one writer's, read from their code, nothing run for it) say yes to all of
    the following.
      One rule holds for both tables: every coordinate between a table's own and the top one stands
        at 0, so the factor "between" is there for a main table with fewer than a - 1 variables too.
      The same formula holds at the second and third sending, whose tables have 2^k' main rows and
        2^h' mask rows over the extension field.
      The pad stands at the mask table's last index.
      The words that ride along (a fold's fresh mask, the masking word) have no answer, no row and
        no ledger, and do not count for the number of coordinates.
      An entry of a main table over the base field is read as (m, 0, 0).
      The ledger is all indices but the last, increasing.
      The order in the batching block BAT is: the three rows of the sum-check as they were added,
        then the sample row, with row number i under the power i.
  The seed of a sample is the format page's rule R6.9 (docs/format/FORMAT.md, which comes with the
  programs);
    what is used of that rule here (a point, then one factor that is not 0) reads the same in two
    editions of the page, neither of them the one that ships.
  Proof files made by the programs are judged by the decision that uses this row: those
    tests are gathered in Fmt/M1FullProg.lean (the verdict on each file; nineteen values that the
    decision computes on its way, compared with the programs' own list). (Exactly: the values of
    `targets`; see Limits in the head of Fmt/M1Targets.lean.)

What SEND does (part 1, section 1 of that description). The prover sends an oracle message:
main rows and mask rows. The verifier draws a point z of a coordinates and then a factor beta
that is not 0. The prover answers with one element y. The verifier computes nothing but one
row (`GRow`, Fmt/M1Types.lean), a linear equation on the message behind the oracle message:
      the sum over the main table of c[j] m[j]  +  the sum over the mask table of d[i] s[i]  =  y.
The tables. 2^b rows form one vector: the entry of row r at place p has the index r + 2^b p. The
main table has 2^Am entries, the mask table 2^Az, and a = max(Am, Az) + 1 (`nCoord`). Both are
thought of as laid into one cube of a variables: the main table where the top variable is 0, the
mask table where it is 1; in both, the variables between the table's own and the top one are 0.

1. What the file contains.
   `sampleRow f Am Az z beta y`
      c[j] = (1 - z_(a-1)) · the product of (1 - z_t) over Am ≤ t < a - 1 · eq(j; z_0 .. z_(Am-1))
      d[i] = z_(a-1) · the product of (1 - z_t) over Az ≤ t < a - 1 · eq(i; z_0 .. z_(Az-1))
             for every i but the last
      d[2^Az - 1] = beta      the pad: the last place of the last mask row; it has no weight under z
      t = y
   `ledger Az`: the mask entries that later blocks may take, in the order in which they are handed
      out: 0, 1, .., 2^Az - 2 (all but the pad).
   At the toy: the first sending has Am = 2 + 12 = 14 (three rows a, b, c and a fourth that nobody
   sends, which counts as 0), Az = 5 and a = 15, so sixteen elements are drawn.
   The batching block BAT (part 1, section 2) is not here. It is `sumRows` of Fmt/M1Types.lean at
   the one drawn element and the four rows in their order: the three rows that the sum-check hands
   on, then this sample row; the first row stands under the power 0.

2. What is checked when the file compiles (#guard). The main test computes the row's left side a
second way: both tables are laid into one cube of a variables, the pad's entry is taken out, and the
cube is weighted by eq over all a variables; beta times the pad's entry is added; that must be the
row's left side. It is run with the mask table smaller than the main table (the toy's case), as
large, and larger, and it fails, as it must, at another beta and at another table. Further: the
numbers of coordinates of the toy's three sendings, if its tables have 14 and 5, 12 and at most 12,
11 and at most 11 index bits; at the first sending's sizes the lengths, the pad, the target and the
ledger; one entry of each table by the description's formula, written out by hand; at a corner of
the cube the row picks one entry; BAT's order of powers.

3. Theorems. None. Nothing is proved in this file.

4. What is not claimed.
   That the answer is spelled as it must be, and that beta is not 0, are the matter of the reader of
   a file and of the rule for drawing, not of this file.
   It is not claimed here that this is the row that the programs compute. It is a reading of their
   description and answers; the tests named under "Sources" compare verdicts and values on the
   programs' own files.
   No statement on soundness follows from this file.
-/
import Fmt.M1Types

namespace Fmt.M1

/-- the number of coordinates of a sample's point -/
def nCoord (Am Az : Nat) : Nat := max Am Az + 1

/-- coordinate t of a point; 0 beyond its end -/
def coE (z : List E) (t : Nat) : E := z.getD t Fld.zeroE

/-- the product of 1 - z_t over lo ≤ t < hi -/
def frontE (f : Fld) (z : List E) (lo hi : Nat) : E :=
  (List.range (hi - lo)).foldl (fun acc t => f.mulE acc (f.subE Fld.oneE (coE z (lo + t)))) Fld.oneE

/-- The sample row of a sent oracle message; part 1 of the head writes out its entries. -/
def sampleRow (f : Fld) (Am Az : Nat) (z : List E) (beta y : E) : GRow where
  c := pv f (f.mulE (f.subE Fld.oneE (coE z (nCoord Am Az - 1))) (frontE f z Am (nCoord Am Az - 1)))
    (z.take Am)
  d := (pv f (f.mulE (coE z (nCoord Am Az - 1)) (frontE f z Az (nCoord Am Az - 1)))
      (z.take Az)).setIfInBounds
    (2 ^ Az - 1) beta
  t := y

/-- the mask entries that later blocks may take, in the order handed out -/
def ledger (Az : Nat) : List Nat := List.range (2 ^ Az - 1)

/-! ## Tests -/

namespace SendG

/-- made-up elements -/
def el (f : Fld) (n : Nat) : E :=
  (f.red (1000003 * n + 17), f.red (n * n + 5 * n + 3), f.red (7919 * n + 1))
def pt (f : Fld) (a : Nat) : List E := (List.range a).map fun t => el f (t + 1)
def tab (f : Fld) (n s : Nat) : Array E := Array.ofFn (n := n) fun i => el f (s + 31 * i.val)

/-- the row's left side at tables that are written out -/
def lhs (f : Fld) (R : GRow) (m s : Array E) : E := f.addE (dot f R.c m) (dot f R.d s)

/-- The row's left side, computed the second way (part 2 of the head). -/
def cubeWay (f : Fld) (Am Az : Nat) (z : List E) (beta : E) (m s : Array E) : E :=
  f.addE (dot f (eqTab f z) (Array.ofFn (n := 2 ^ nCoord Am Az) fun J =>
      if J.val < 2 ^ Am then ent m J.val
      else if 2 ^ (nCoord Am Az - 1) ≤ J.val ∧ J.val + 1 < 2 ^ (nCoord Am Az - 1) + 2 ^ Az then
        ent s (J.val - 2 ^ (nCoord Am Az - 1))
      else Fld.zeroE))
    (f.mulE beta (ent s (2 ^ Az - 1)))

def agree (f : Fld) (Am Az : Nat) : Bool :=
  lhs f (sampleRow f Am Az (pt f (nCoord Am Az)) (el f 90) (el f 91))
      (tab f (2 ^ Am) 200) (tab f (2 ^ Az) 400) ==
    cubeWay f Am Az (pt f (nCoord Am Az)) (el f 90) (tab f (2 ^ Am) 200) (tab f (2 ^ Az) 400)

end SendG

open SendG in
#guard agree .two 3 1 && agree .two 4 2 && agree .two 3 0 && agree .one 3 1
open SendG in
#guard agree .two 3 3 && agree .one 2 2 && agree .two 0 0
open SendG in
#guard agree .two 1 3 && agree .two 0 2 && agree .one 1 4
-- the two ways differ, as they must, at another beta and at another table
open SendG in
#guard lhs .two (sampleRow .two 3 1 (pt .two 4) (el .two 90) (el .two 91)) (tab .two 8 200) (tab .two 2 400) != cubeWay .two 3 1 (pt .two 4) (el .two 92) (tab .two 8 200) (tab .two 2 400)
open SendG in
#guard lhs .two (sampleRow .two 3 1 (pt .two 4) (el .two 90) (el .two 91)) (tab .two 8 200) (tab .two 2 400) != cubeWay .two 3 1 (pt .two 4) (el .two 90) (tab .two 8 201) (tab .two 2 400)
-- the numbers of coordinates of the toy's three sendings, if its tables have 14 and 5, 12 and at
-- most 12, 11 and at most 11 index bits (tested at 14 and 5, 12 and 9, 11 and 10): one less than
-- the elements drawn (16, 14, 13: a test of Fmt/M1Dec.lean)
#guard (nCoord 14 5, nCoord 12 9, nCoord 11 10) = (15, 13, 12)
-- at the toy's first sending: the lengths; the pad; the target; the ledger
open SendG in
#guard ((sampleRow .two 14 5 (pt .two 15) (el .two 90) (el .two 91)).c.size, (sampleRow .two 14 5 (pt .two 15) (el .two 90) (el .two 91)).d.size) = (16384, 32)
open SendG in
#guard ent (sampleRow .two 14 5 (pt .two 15) (el .two 90) (el .two 91)).d 31 = el .two 90 && (sampleRow .two 14 5 (pt .two 15) (el .two 90) (el .two 91)).t = el .two 91
#guard (ledger 5).length = 31 && (ledger 5).take 29 = List.range 29 && !(ledger 5).contains 31
-- one entry of each table by the text's formula, written out by hand:
-- c[j] = (1 - z_14) eq(j; z_0 .. z_13); d[i] = z_14 (1 - z_5) .. (1 - z_13) eq(i; z_0 .. z_4)
open SendG in
#guard ent (sampleRow .two 14 5 (pt .two 15) (el .two 90) (el .two 91)).c 9999 = Fld.two.mulE (Fld.two.subE Fld.oneE (el .two 15)) (eqAt .two ((pt .two 15).take 14) 9999)
open SendG in
#guard ent (sampleRow .two 14 5 (pt .two 15) (el .two 90) (el .two 91)).d 19 = Fld.two.mulE (Fld.two.mulE (el .two 15) ((List.range 9).foldl (fun acc t => Fld.two.mulE acc (Fld.two.subE Fld.oneE (el .two (t + 6)))) Fld.oneE)) (eqAt .two ((pt .two 15).take 5) 19)
-- at a corner of the cube the row picks one entry: of the main table (top coordinate 0), of the
-- mask table (top coordinate 1)
#guard (sampleRow .two 2 1 [Fld.oneE, Fld.zeroE, Fld.zeroE] (9, 0, 0) (0, 0, 0)).c = #[Fld.zeroE, Fld.oneE, Fld.zeroE, Fld.zeroE]
#guard (sampleRow .two 2 1 [Fld.zeroE, Fld.zeroE, Fld.oneE] (9, 0, 0) (0, 0, 0)).d = #[Fld.oneE, (9, 0, 0)]
-- BAT: `sumRows` puts the first row under the power 0, the fourth under the third power
open SendG in
#guard (sumRows .two (el .two 8) [⟨#[], #[], el .two 1⟩, ⟨#[], #[], el .two 2⟩, ⟨#[], #[], el .two 3⟩, ⟨#[], #[], el .two 4⟩]).t
  = Fld.two.addE (el .two 1) (Fld.two.mulE (el .two 8) (Fld.two.addE (el .two 2) (Fld.two.mulE (el .two 8) (Fld.two.addE (el .two 3) (Fld.two.mulE (el .two 8) (el .two 4))))))

end Fmt.M1
