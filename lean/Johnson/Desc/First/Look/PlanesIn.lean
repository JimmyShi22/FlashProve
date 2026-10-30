-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/PlanesIn.lean: the kind "lookup" (K3): THE TEST «THE CELLS OF THE PLANES OF
THE COUNTS LIE IN THE MATRIX THAT IS TO HOLD THEM», as a function of the public record and a link's
number. Definitions alone, with code. No proof. Without Mathlib.

Why. The lookup on a link's calls leaves claims on the planes of its counts. They are cells of one
matrix of the link's smallness test's list: row below 2 ^ lm, column below NC * 2 ^ (kT + 5 - lm). A
description that reads such a cell where the list has no such matrix, row or column reads nothing
that was committed. The test asks, on public data alone, that the list has them.

Main names:
  `planeCellsB tl fs lm iB`: five comparisons: 5 ≤ lm; lm ≤ kT + 5; the list has a matrix number iB;
    it has 2 ^ lm rows or more; it has NC * 2 ^ (kT + 5 - lm) columns or more.
  `iBAt X i`: the number of that matrix in link i's list, by lookAt's own split of i: NHf + 2 at the
    head, (matIx y).iB at a layers' link, NAs + 2 at an attention link.
  `planesInAt X i digits`: the test at link i's lookup: at the calls: planeCellsB at the record that
    tlAt gives, AT THE SHAPE THAT THE LOOKUP's OWN PARAMETERS MAKE (placeAt's p.shape: the numbers
    by which the block hears) and their lm, and at iBAt; `some false` where the parameters make no
    shape; none where placeAt, tlAt or iBAt is none. AT THE DIGITS: `some true`: NOTHING IS ASKED
    THERE.

Limits. THE TEST SPEAKS OF ROOM: other matrices of a list may pass it too; that number iBAt is the
planes' matrix is read off the verifier program's layouts (the library's own tests name the same
numbers: OnBytes/Tie/Pv/Lookup/Ends/FoPlaneNums.lean, FoLookLayerReads.lean). AT THE DIGITS the
planes are no matrix of the list but an array of the link's own (32 rows): this test has nothing to
say of them. The like comparison there (that array's rows and columns against the counts' bits) is
so far a test under the closed caller of the digits' lookup, and no clause of a test on the plan.
The powers of two are reached only behind the two bounds on lm, and kT is a made shape's: the test
on a call refuses a table of more than 2 ^ 16 rows (read off its text; no theorem here). Nothing on
the cells that the keys read.
That the test says yes at every record that Verify.publicOf returns:
Johnson/Desc/First/Look/K3CallerPlanesAt.lean (planesInAt_law: wherever placeAt returns).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.LookKind
import Johnson.Desc.First.Look.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- **The five comparisons.** tl: the record of the link's smallness test. fs: the lookup's numbers.
lm: the logarithm of the rows of the packed planes. iB: the matrix's number in the list. -/
def planeCellsB (tl : HTailF2) (fs : Forest.Shape) (lm iB : Nat) : Bool :=
  decide (5 ≤ lm) && decide (lm ≤ fs.kT + 5) && decide (iB < tl.NM) &&
    decide (2 ^ lm ≤ (tl.mats.getD iB {}).m) &&
    decide (fs.NC * 2 ^ (fs.kT + 5 - lm) ≤ (tl.mats.getD iB {}).k)

/-- The number of the planes' matrix in link i's list of matrices. -/
def iBAt (X : Verify.Public) (i : Nat) : Option Nat :=
  let step := if X.p4 then 2 else 1
  if i == step * X.NGr then some (X.hS.NHf + 2)
  else if i % step == 0 then some (Layer.matIx X.y).iB
  else X.A[i / step]?.map fun a => a.S.cf.NAs + 2

/-- **The test at link i's lookup, of the public record alone.** -/
def planesInAt (X : Verify.Public) (i : Nat) (digits : Bool) : Option Bool :=
  if digits then some true else
  (placeAt X i false).bind fun p =>
    (tlAt X i).bind fun tl => (iBAt X i).map fun iB =>
      match p.shape with
      | some fs => planeCellsB tl fs p.lm iB
      | none => false

end VerifiableInference.Desc.First.Look
