-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/Part.lean: the honest side of the kind "the smallness test" (K8),
in the form of Honest/Frame.lean. The kind's own text does not hold what the prover sends
(Johnson/Desc/First/K8/Hear.lean): this file holds it. DEFINITIONS, WITH CODE. NO THEOREM. THE LEAN
HERE CLAIMS NOTHING ON COMPLETENESS, SOUNDNESS OR HIDING; two paragraphs below word a limit on
hiding, on paper, in a reviewer's own words.

What is sent. Nothing: one round, in which the matrix is drawn. The half is a row of one part, which
takes no coin and is handed no run of another part's coins. The move refuses, as a fault of the
text, if the half was handed names for another number of matrices than the place has.
The stops. The first never stops. THE SECOND: behind the round: a combination of a row of cells
leaves its window (`leaves`, Johnson/Desc/K8/Honest/Window.lean): then its two digits do not give it
back, and the claims that tie the array of digits, which the next block sends, to the cells need not
hold. It reads the drawn matrix and the cells.
ON THE SECOND STOP, in words that are kept to the letter in this
head: "The honest prover stops at K8's round if some combination leaves the window. At a valid input
with all cells at most 128 in size, and over a uniform challenge matrix, that has probability at
most 2^-178 a session at the full-size shapes [on paper; the tail bound: Prob/Window.lean,
pr_win_le]. The set hangs on the hidden cells, so no simulator can reproduce it: its measure is a
term of the error."
BEHIND IT, MORE WORDS OF THE SAME REVIEWER, set here to the letter as it signed them for this head:
"That is one session's number: N sessions multiply it, and N counts every slot begun: served, failed
or sent again. It is K8's share of the stops alone: the term in the error is the sum of all parts'
shares." AND, signed to stand only as long as it is true of these files: "The number is a
calculation on paper: no theorem of this file states it."
TWO NUMBERS STAND IN THIS HEAD, AND THEY DIFFER IN REACH: the reviewer's number is, in its own
words, of "a session at the full-size shapes"; THE STATED SHARE below is of one place.

  `signedOf`      a cell, as the witness's reader yields it, as an integer
  `SmallAsk`      what the part is handed: of the prover's input the cells of the place's matrices;
                   of the half's public data for how many matrices it has a name
  `cellsAtOf`     the cells of the place's matrices, off the witness's reader
  `windowBits`, `windowShare`   THE STATED SHARE of the second stop
  `smallPart`     the part
  `smallFits`, `drawnFits`   TWO TESTS WITH CODE FOR THE SEAT, the first on public data, the second
                   on the round's drawn entries: see WHERE A DEFINITION PADS
  `askOfInput`    that structure, of the prover's input
  `smallHalf`     the kind's half at a place
  `smallLot`      the halves at the places at which the proof file's description seats the kind's
                   blocks, under the name of the lot that seats them
                   (Johnson/Desc/ProofFile/Lot/K8.lean)

THE STATED SHARE, AND WHERE ITS NUMBERS COME FROM. It is a number that is written down; nothing here
bounds the stop by it. For one matrix with m rows of cells and k columns the format's condition on
range checks (docs/format/FORMAT.md, 16.1, condition 7) counts
  (14426 * range^2) div (10000 * k * (bound - 1)^2) - 1 - ceil_log2 m - ceil_log2 tau   bits,
with range = 2^17 and bound = 129: it takes every cell to be below 129 in absolute value. The share
is the sum over the place's matrices of 1 of 2^bits. (That page's cap at 2^30 bits is never met at
these constants.) The library has a bound of this shape for its own range check (stated in
Cb/Gen/RngAlg.lean, `Spec.pr_event_le`; proved in Cb/Gen/RngAlgProofs.lean, by Prob/Window.lean).
In this file no theorem ties it to this stop: Honest/K8/ShareLaw.lean holds the number, for cells
that are at most 128 in absolute value, over uniform written verifier messages of the one round.

WHICH MATRIX IS WHICH. A place's list of matrices holds matrices of the segment itself and of
earlier segments. The half is handed, for each matrix of the list: the number of the segment that
owns it; its name there AS THE VERIFIER's OWN PLAN LAYS IT (the field `TMat.name`,
OnBytes/Model/Frame.lean): where the format's pages name a whole matrix that the plan cuts in parts,
the part's name: so the witness's reader takes it (`Cells`, Honest/ForKinds.lean); and its first
column under that name. These are public data; they are a parameter here.

WHERE A DEFINITION PADS. `cellsAtOf` yields 0 for a matrix beyond the list of names; `windowShare`
cuts the longer of two lists; `entry`, `comb`, `leaves` and `cellsSmall`
(Johnson/Desc/K8/Honest/Window.lean) read 0 beyond a list's end, and `entry` reads 0 BEYOND THE
DRAWN ENTRIES. Two tests with code say when none of these is reached: `smallFits`, on public data:
as many names, and as many numbers of rows, as the place has matrices; `drawnFits`, on the round: as
many drawn entries as the matrices have columns times the number of combinations. WHERE `smallFits`
SAYS NO THE PART's MOVE REFUSES, OR A MATRIX HAS NO ROWS AND THE STOP IS SILENT, or the place has
more numbers of rows than matrices, which the stop never walks and `allRows` counts: so it is a
premise at the seat. That under the two tests none of these is reached is this head's reading; no
lemma says it. NOT UNDER THE TWO TESTS: `digitAt` yields 0 beyond the array's rows and columns, and
`partLength`, `readOf` and `readAt` (Johnson/Desc/K8/Honest/Arrays.lean) read 0 beyond a list's end:
whoever lays these arrays asks their sizes (for the digits: Honest/K8/ZzData.lean).

WHERE THE PROVER PROGRAM DOES OTHERWISE. This part gives up at a combination outside its window. The
program sets a flag there and goes on with digits that are cut to their ranges
(prover/hiding/tail_f.cuh: `kf_zz_plain`); by its comments that request then gets no proof. The
format's page asks for fixed values
behind a failed range check
(docs/format/FORMAT.md, section 16).

FOR WHOEVER SPENDS THIS FILE: three terms of the reviewer whose words stand above, in this head's
words. The number 2^-178 goes nowhere without what rides on it: it is of one session; N sessions
multiply it; it is K8's share of the stops and no sum; it stands over the verifier's uniform
challenges, at cells of at most 128 in size, and on paper. `hidShare` is a stated number and no
bound: a law that spends it names the law that bounds the stop by it, and the premise on the cells,
which is to be paid from "the input is valid". A premise "nothing stops at this part" narrows the
input: the measure of the stop's set is a term of the error.

WRITTEN A FURTHER TIME. `bitsFor` has the text of five definitions of the library: `ceilLog2`
(OnBytes/Iop/Ground.lean) · `clog2` (OnBytes/Params/Group.lean) · `logUp` (Fmt/Places.lean) · `clog`
(Fmt/ParsedTies.lean) · `bitsFor` (Johnson/Desc/First/Look/ShapeOwn.lean): none is called here.
`signedOf` is, on the base field, what the library's `signedOf` (Johnson/Goal/Meaning/HidBase.lean)
is on an element's first coordinate; a third of that name reads a word
(Johnson/Desc/Kinds/Law/SymbolCells.lean). `windowBits` has the terms of the count in the library's
text of the format's gate (OnBytes/Params/Gate.lean), at range 2^17 and bound 129: here in natural
numbers, cut off at 0, without that text's tests and cap. SHORT NAMES THAT STAND ELSEWHERE, FOR
OTHER THINGS: `windowBits` (Johnson/WholeKey/CoinLaws.lean) · `smallFits`
(Johnson/Desc/First/Batch/SmallFits.lean).

OF THE PATHS THAT THIS HEAD NAMES: docs/format/FORMAT.md and prover/hiding/tail_f.cuh are pages
outside this library; Honest/K8/ShareLaw.lean and Honest/K8/ZzData.lean are files which this library
may not hold.

Limits. That an honest cell is below 129 in absolute value is not said here; without it the stated
share means nothing: so the number is not one "at every input". Nothing holds a matrix's name, owner
or first column against the format's pages: a wrong one reads other cells, in silence. What an
honest prover lays into the cells that this test alone reads (the format fixes no choice) is the
witness's reader's matter. Behind the stop nothing is said of what is sent.
The reviewer whose words stand above signed these words, not this file.
-/
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.ProofFile.Lot.K8
import Johnson.Desc.K8.Honest.Window

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open VerifiableInference.Desc.First.K8 (Par)
open VerifiableInference.Desc.First.K8.Honest (CellsAt leaves)

variable {W₀ Rc Xi Tr X : Type}

/-- An element of the base field as the integer of least absolute value that is read as it: a
negative cell enters the field as a negative integer. -/
def signedOf (x : Cb.Gl.F) : Int :=
  if 2 * x.val < Code.pGold then (x.val : Int) else (x.val : Int) - (Code.pGold : Int)

/-- What the part is handed: the cells are of the prover's input; `named` is of the half's public
data. -/
structure SmallAsk where
  /-- the cells of the place's matrices: the matrix's number in the place's list, the row, the
  column -/
  cell : CellsAt
  /-- for how many matrices the half was handed a name -/
  named : Nat

/-- The least number of bits that number the numbers below n. -/
def bitsFor (n : Nat) : Nat := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- The format's count for one matrix, in bits; cut off at 0. -/
def windowBits (rows columns combinations : Nat) : Nat :=
  14426 * (2 ^ OnBytes.Model.lbz) ^ 2 / (10000 * columns * 128 ^ 2) - 1 - bitsFor rows -
    bitsFor combinations

/-- The stated share of the second stop at a place: a number that is written down, no bound. -/
def windowShare (p : Par) : Odds :=
  (p.ms.zip p.ks).foldl (fun s x => s.plus ⟨1, 2 ^ windowBits x.1 x.2 p.tau⟩) ⟨0, 1⟩

/-- The second stop: in front of the round nothing; behind it the window. The length of the drawn
entries is not tested here (`drawnFits`). The string names matrix, row and combination: a notice of
the prover's own, meant to be shown to nobody: no move of this part sends it. -/
def smallHid (p : Par) (v : SmallAsk) (_front own : List Fmt.Drawn) : Option String :=
  own.head?.bind fun d =>
    (leaves p v.cell d.trits.toArray).map fun x =>
      s!"a combination leaves its window: matrix {x.1}, row {x.2.1}, combination {x.2.2}"

/-- **The part**: one round, in which nothing is sent. -/
def smallPart (p : Par) : Part SmallAsk SmallAsk Unit :=
  { takes := ⟨0, 0⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := smallHid p
    badShare := ⟨0, 1⟩, hidShare := windowShare p
    moves := [⟨fun _ _ t =>
      if t.input.named == p.ks.length then .ok ⟨[], []⟩
      else .error "the matrices that are named are not as many as the place's", fun t => t.own⟩] }

/-- **A public premise at the seat**: the half was handed a name for each of the place's matrices,
and the place has a number of rows of cells for each. Where the first fails the part's move refuses;
where the second fails a matrix is read as having no row. -/
def smallFits (P : Par × List (Nat × String × Nat)) : Bool :=
  P.2.length == P.1.ks.length && P.1.ms.length == P.1.ks.length

/-- A test on the round's drawn entries: as many as the matrices have columns, times the number of
combinations: so that no entry is read beyond them. -/
def drawnFits (p : Par) (trits : List Int) : Bool :=
  trits.length == p.ks.foldl (· + ·) 0 * p.tau

/-- The cells of the place's matrices, off the witness's reader. mats: for each matrix of the
place's list: its owner's number, its name, its first column there. A matrix beyond the list has the
cells 0. At a name that is no label the cells are what the reader yields there. -/
def cellsAtOf (C : Cells) (mats : List (Nat × String × Nat)) : CellsAt := fun mu i c =>
  match mats[mu]? with
  | some m => signedOf (C.cell m.1 m.2.1 i (m.2.2 + c))
  | none => 0

/-- What the part is handed, of the prover's input and the list of names. cells: the witness's
reader. Of the input it reads the witness's cells alone. The part's move refuses where the list is
shorter or longer than the place's. -/
def askOfInput (cells : Tr → Cells) (mats : List (Nat × String × Nat)) (w : Local W₀ Rc Xi Tr) :
    SmallAsk :=
  { cell := cellsAtOf (cells w.trace) mats, named := mats.length }

/-- **The kind's half** at a place: of the place's numbers and its list of matrices. -/
def smallHalf (cells : Tr → Cells) :
    KindHalf (Par × List (Nat × String × Nat)) (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  fun P =>
    ⟨⟨1, some P.1.link, P.1.piece, .K8⟩,
      [(smallPart P.1).lift (askOfInput cells P.2) (askOfInput cells P.2) (fun _ => ())
        fun x _ => x]⟩

/-- **The lot's honest side**: a half at each segment, at the numbers at which the lot makes its
block there. mats: each segment's list of matrices, of the public data. THE NAME IS WRITTEN A SECOND
TIME HERE: a program that prints `lotsLacking` shows whether the two strings still agree. -/
def smallLot (cells : Tr → Cells)
    (mats : Pub → Ground → OnBytes.Model.Stages.LinkH → Nat → List (Nat × String × Nat)) :
    HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  { name := "the smallness test"
    halves := fun Z G =>
      G.built.toList.zipIdx.map fun y => smallHalf cells (k8Par Z G y.1 y.2, mats Z G y.1 y.2) }

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.signedOf
#print axioms ProofFile.Honest.K8.SmallAsk
#print axioms ProofFile.Honest.K8.bitsFor
#print axioms ProofFile.Honest.K8.windowBits
#print axioms ProofFile.Honest.K8.windowShare
#print axioms ProofFile.Honest.K8.smallHid
#print axioms ProofFile.Honest.K8.smallPart
#print axioms ProofFile.Honest.K8.smallFits
#print axioms ProofFile.Honest.K8.drawnFits
#print axioms ProofFile.Honest.K8.cellsAtOf
#print axioms ProofFile.Honest.K8.askOfInput
#print axioms ProofFile.Honest.K8.smallHalf
#print axioms ProofFile.Honest.K8.smallLot
