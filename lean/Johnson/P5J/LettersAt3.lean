-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/LettersAt3.lean: THREE PARAMETERS OF THE COMPOSED MEANING (`MgData`,
Johnson/Desc/Sound/MgAll.lean) THAT `At.𝔇At` (LettersRec.lean) LEAVES OPEN, EACH AT ANOTHER FILE's
TERM OFF THE PUBLIC PARAMETERS. Three definitions; two equations, proved by the make.

  `At.d1 Zp`       := `FillP1.d1At Zp` (Johnson/Top/H0/Fill/D1At.lean): the public numbers for the
    pending claim on the committed table.
  `At.mat13 Zp nR` := `K13.Law.matOfCells nR (P13 Zp).lin.kCol`
    (Johnson/Desc/K13/Law/MatOfCells.lean): the committed table's cells as a matrix by row and by
    the bits of the column's number. `At.P13 Zp`: LettersAt2.lean.
  `At.rq Zp`       := `Kinds.Head.AtZ.rqAt Zp` (Johnson/Desc/Kinds/Head/AtZ.lean): the request that
    the words of the public part's request spell.
  `lin_one`: `(P13 Zp).lin = (d1 Zp).lin`: the two files' terms read one field of the public
    parameters.
  `built_one`: `Zp.p.built.links = Zp.made.p.built.links`: the two paths to the built segments
    (d1At's; `At.𝔇At`'s) are one.
DEFAULTS THAT ANSWER IN SILENCE, ALL IN THOSE FILES' TEXTS: `d1At`'s ncl: 0 at a segment's number
that the list of built segments does not hold · `matOfCells`' `cellAtNo`: 0 at a row or a column
outside the table (nR is the structure's free index; the columns run below 2 ^ kCol): the named
test: nR ≤ the table's rows and 2 ^ (P13 Zp).lin.kCol ≤ its columns · `K13.whereOf`: `fromOf`
answers 0, and the three numbers of proof of work answer 0, where the table of stretches has no such
step: the named test: `(K13.fromOf? Zp).isSome` (the kind's own sub-protocol asks it in its test on
the list of rounds). THE OTHER PARAMETERS: digitsPart: LettersRec3.lean · cr1: LettersAt4.lean
· headPart: LettersAt3Head.lean · uA: LettersAt3Arm.lean · uH: LettersAt3HeadArm.lean · uL:
LettersAt3Lay.lean · wt: LettersAt4.lean · rad3,
seat3: Rad3Seat3At.lean.
Limits. Definitions. NO EXAMPLE shows that a sentence over these terms can be met. Nothing on
soundness.

-/
import Johnson.P5J.LettersRec
import Johnson.P5J.LettersAt2
import Johnson.Top.H0.Fill.D1At
import Johnson.Desc.K13.Law.MatOfCells
import Johnson.Desc.Kinds.Head.AtZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc.Sound (CellsQ)

variable (Zp : ProofFile.Pub)

/-- The public numbers for the pending claim on the committed table. -/
def d1 : VerifiableInference.Desc.First.FillP1.PubData :=
  VerifiableInference.Desc.First.FillP1.d1At Zp

/-- The committed table's cells as a matrix. -/
def mat13 (nR : ℕ) : CellsQ OnBytes.Flat.numsFull.rows (colsAt OnBytes.Flat.numsFull) → Fin nR →
    (Fin (P13 Zp).lin.kCol → Bool) → OnBytes.Slice.GE :=
  fun c => VerifiableInference.Desc.K13.Law.matOfCells nR (P13 Zp).lin.kCol c

/-- The request that the public part's words spell, as the output head's sub-protocols read it. -/
@[reducible] def rq : ProofFile.InstPub → VerifiableInference.Desc.Kinds.Head.Request :=
  VerifiableInference.Desc.Kinds.Head.AtZ.rqAt Zp

theorem lin_one : (P13 Zp).lin = (d1 Zp).lin := rfl

theorem built_one : Zp.p.built.links = Zp.made.p.built.links := rfl

end P5J.At

#print axioms P5J.At.lin_one
#print axioms P5J.At.built_one
