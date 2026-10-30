-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/LotFilled.lean: the honest side of the kind "lookup" (K3): the
lot's entry as one term. Definitions with code, three theorems by rfl, a sheet's lines.

Terms. Honest/K3/GLOSSARY.md ("lot", "half", "filling", "sources", "owner, borrowed matrix"). In
this file: a sheet is a list of lines of text, as in Honest/K3/LotSheet.lean.

What is defined and shown.
  `rowLotAt`: the lot's honest side at letters that may read the public part.
  `sourcesAt`: where keys and bits come from, at a public part: by the public part's own numbers,
    the head's public data tied to it, a borrowed matrix read under its owner's segment and name
    (`tiedOwnSources`, Honest/K3/WitOwner.lean).
  `theLot`: the lot's honest side, as a function of three readers alone: the trace's cells, the
    index's weights, and the instance's covered positions with the token that is checked at each. At
    each site of the public part: the kind's row, seated, at the summands that fold tables
    (`fastFill`, Honest/K3/LotRow.lean), at `sourcesAt` of the very public part that the halves are
    handed.
  `theLotSpec`: the same at the specification's summands (`specFill`): in the place of `theLot`,
    never beside it: both bear the lot's one name.
  `theLot_is`, `theLotSpec_is`, `theLot_name`: at each public part the halves are those of
    `lookLotFast` and `lookLot` (LotRow.lean) at that public part's sources; the name is the lot's.
  `shapeTests`: one more test at a site: the library's test on the shape's numbers (`FoNums.ok`).
  `filledSheet`, `filledSheetLines`: the sheet of LotRow.lean at `theLot` itself, with that test.

Which of the two is the part. `theLot`. Its summands are written whole in this folder
(Honest/K3/JobsFast.lean). Those of `theLotSpec` are fields of the library's structure of jobs
(`Job`, Johnson/HonestTrace/LookDefs.lean). That the two send the same is not said in this file, nor
in a file that it imports; the head of LotRow.lean says what is shown of it.

On `FoNums.ok`. Here it is a test: it shows something only where a program evaluates it. The sheet
evaluates it at every site.

A group's number and a segment's. `Who.layers g` and `Who.attention g` bear the group's number,
`Who.digits` the link's (`whoOf`, LotRow.lean). A reader of cells is asked by the segment's number:
the sources make it of the group's number by themselves (Honest/K3/WitPlan.lean).

Imported. Honest/K3/LotRow.lean, Honest/K3/WitOwner.lean.

Users. Honest/K3/SeatFits.lean, Honest/K3/LotDigitsFast.lean and Honest/K3/Law/LotKind.lean import
this file.

Limits. The three readers are letters: whoever seats the lot gives them. The sheet reads places,
numbers of rounds, cuts, addresses, names and counts of stretches: no summand is evaluated in it and
no value that a part sends is read.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.LotRow
import Johnson.Desc.ProofFile.Honest.K3.WitOwner

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open VerifiableInference.Desc (Block)

variable {V W X S Cl : Type} {W₀ Rc Xi Tr : Type}

/-- The lot's honest side at letters that may read the public part. -/
def rowLotAt (A : Pub → Fill W) : HLot V W X :=
  { name := lotName
    halves := fun Z G => (rowLot (A Z)).halves Z G }

/-- Where keys and bits come from, at a public part. -/
def sourcesAt (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) : Sources W₀ Xi Tr :=
  tiedOwnSources Z.p.X cells weights req

/-- **The lot's honest side.** Here cells is the trace's reader, weights the index's, and req gives,
of the instance, the covered positions and the token that is checked at each. -/
def theLot (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) :
    HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  rowLotAt fun Z => fastFill (sourcesAt cells weights req Z)

/-- The same at the specification's summands: in the place of `theLot`, never beside it. -/
def theLotSpec (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) :
    HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  rowLotAt fun Z => specFill (sourcesAt cells weights req Z)

/-- At each public part the halves are those of `lookLotFast` at that public part's sources. -/
theorem theLot_is (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (G : Ground) :
    (theLot (Rc := Rc) (X := X) cells weights req).halves Z G =
      (lookLotFast (sourcesAt cells weights req Z)).halves Z G := rfl

/-- At each public part the halves are those of `lookLot` at that public part's sources. -/
theorem theLotSpec_is (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (G : Ground) :
    (theLotSpec (Rc := Rc) (X := X) cells weights req).halves Z G =
      (lookLot (sourcesAt cells weights req Z)).halves Z G := rfl

/-- Its name is the lot's, at every public part. -/
theorem theLot_name (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) :
    (theLot (Rc := Rc) (X := X) cells weights req).name = (K3Lot.lot Z).name := rfl

/-- One more test at a site. -/
def shapeTests (s : Site) : List (String × Bool) :=
  [(s!"link {s.link}, " ++ (if s.digits then "digits" else "calls") ++
      ": the library's test on the shape's numbers says yes", FoNums.ok s.shape)]

/-- **The sheet at `theLot` itself**: the lot's tests and alterations (`sheetOf`,
Honest/K3/LotSheet.lean) at the term `theLot`; the sides and the stretches of coins at its halves
and at the letters of which they are made; the test on the shapes' numbers, with an alteration:
every shape's tree of depth 0. If fast is true: `theLot`; else `theLotSpec`. -/
def filledSheet (fast : Bool) (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (G : Ground)
    (bs : List (Block S Cl)) : List String :=
  let src := sourcesAt cells weights req Z
  let A : Fill (Local W₀ Unit Xi Tr) := if fast then fastFill src else specFill src
  let L : HLot (Local W₀ Unit Xi Tr) (Local W₀ Unit Xi Tr) Unit :=
    if fast then theLot cells weights req else theLotSpec cells weights req
  let sites := lookSites Z
  let ts := sideTests (rowSides (V := Local W₀ Unit Xi Tr) (X := Unit) (Pb := Unit) A bs sites)
  let cs := coinTests (sites.zip (L.halves Z G))
  let ns := sites.flatMap shapeTests
  let flat := sites.map fun s => { s with shape := { s.shape with dT := 0 } }
  sheetOf Z G bs L ++
    [s!"SIDES: yes {ts.length - (failing ts).length} of {ts.length}"] ++
    (failing ts).map ("NO: " ++ ·) ++
    [s!"COINS: yes {cs.length - (failing cs).length} of {cs.length}"] ++
    (failing cs).map ("NO: " ++ ·) ++
    [s!"SHAPES' NUMBERS: yes {ns.length - (failing ns).length} of {ns.length}"] ++
    (failing ns).map ("NO: " ++ ·) ++
    [bendLine "every site's shape: a tree of depth 0" sites.length
      (failing (flat.flatMap shapeTests))]

/-- The same, as a function of the three public files. Here o stands for the format's second hash function.
-/
def filledSheetLines (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (fast : Bool) (cells : Tr → Cells)
    (weights : W₀ → Weights) (req : Xi → OnBytes.Model.Head.Covered × Array Nat) : List String :=
  match pureRoad.pub o pol lay KL with
  | .error e => ["NO PUBLIC PART: " ++ e]
  | .ok Z =>
    match blankBy pureRoad.links Z with
    | none => ["NO RECORDS OF THE SEGMENTS for a request of zeros"]
    | some G =>
      match onlineDescription o pol lay KL with
      | .error e => ["NO DESCRIPTION: " ++ e]
      | .ok F => filledSheet fast cells weights req Z G F.first.blocksInOrder

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.theLot_is
#print axioms ProofFile.Honest.K3.theLotSpec_is
#print axioms ProofFile.Honest.K3.theLot_name
