-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/MaskEntryStatement.lean: THE STATEMENT, AND NO PROOF: "AT AN UNMARKED STATEMENT
INSIDE THE PROMISE OF THE TABLE OF JOINTS AT A BORDER, THE MASK ENTRY THAT THE READER OF THE ROWS ON
THE COMMITTED TABLE OF WEIGHTS READS THROUGH THE VERIFIER's STATE, AT THE INDEX MASKS' MESSAGE AND
THE ENTRY THAT ITS LEDGER HANDS OUT NEXT, IS ONE ENTRY OF THE WITNESS's OWN TABLE AT A SEAT, A ROW
AND A PLACE OF THE PUBLIC PARAMETERS". Definitions alone, one of them a test with code. The proof
stands beside: Johnson/Road/K4/Rec/MaskEntry.lean.

WHO SPENDS IT. The line wo of K4's row (Johnson/Road/K4/K4LinesWo.lean) has a premise hmask: at
every unmarked statement b inside the promise behind K4's sub-protocol and every witness w: (rw (Z,
b.1) w).mask ⟨im₀, v⟩ is the value's message at one of its entries. The term that is meant for rw is
`rwBook arr mat` (Johnson/Desc/K13/Law/ReaderByBook.lean), which reads the witness through the
state's own statement and book. `MaskEntryIs` takes the state out of the left side. THE RIGHT SIDE
OF hmask (THE VALUE's) IS NOT TOUCHED HERE.

THE CHAIN. "K12.msgShapes", "K12.bookInOrder" and "K12.seatsCarried", with the promise's clause on
the book: the table that the reader reads at message number im is the witness's own table at the
shape and the seat of the public parameters (`tabFirst_at_door`,
Johnson/Desc/Sound/WordsAtDoor.lean). "In order": the codes. The entry's number is `takenNo` at the
shape's mask rows m₀ and k, the number of the segments in front that leave a row: that is row k %
m₀, place k / m₀ (`takenNo_eq`, OnBytes/Iop/LedgerPlaces.lean), and it lies within the mask table
where k is below the count of free entries (`takenNo_lt`, `tableSize_mask`:
Johnson/Desc/K13/Law/LedgerWithin.lean).

  `EBook0`: AN EQUATION of the meaning's field pub at "K12.bookInOrder", at first tree 0.
  `maskItems`, `openMaskB M links ps j`: the three items; A TEST: they are open at border j.
  `maskFitsB cs M L n t im k`: A TEST: im is below n; the first n places of the list of (tree, part)
    name trees below t; the list of shapes has at im a shape with a mask row and an answer, and k is
    below its count of free entries at the codes cs.
  **`MaskEntryIs`**.

OBJECT: none of its own. USER: meant: hmask, at j := k + 1. LETTERS, filled by nobody: N, Mg, Z,
links, ps, j, m, M, L, cs, fvs, arr, mat.

Limits. A SENTENCE: NOTHING IS PROVED HERE. THE FOUR PREMISES ON THE MEANING ARE SHOWN AT NO TERM.
THE TWO TESTS HAVE BEEN EVALUATED NOWHERE. THAT THE COMPOSED MEANING's READER IS `rwBook arr mat` IS
NOT SAID HERE. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED BY THIS. Nothing on
soundness.
-/
import Johnson.Desc.K13.Law.ReaderByBook
import Johnson.Road.K4.Rec.NextEntryStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart Pub More Meaning Numbers pubSets)
open VerifiableInference.Desc.K12.Door (atFirstBook placesBelowB)
open VerifiableInference.Desc.K13.Law (rwBook)
open VerifiableInference.Desc.Sound (Frame MsgT onQ)
open Johnson.Desc.First.Walk.Tied (rowsBefore)

/-- What the item K12.bookInOrder says, at first tree 0. -/
def EBook0 {P W : Type} (Mg : Meaning P W) : Prop :=
  ∀ a : P × S, Mg.pub (.more none "K12.bookInOrder") a = atFirstBook 0 a.2

/-- The three public items that are spent. -/
def maskItems : List Pub :=
  [.more none "K12.msgShapes", .more none "K12.bookInOrder", .more none "K12.seatsCarried"]

/-- A TEST: the three are open at border j. M: the filling of the door. -/
def openMaskB (M : More) (links : List ModelPart) (ps : List Place) (j : ℕ) : Bool :=
  maskItems.all fun q => ((pubSets M links ps)[j]?.getD []).contains q

/-- A TEST on the public parameters. n: the number of oracle messages; t: of trees; im: the
message's number; k: how many entries are taken. -/
def maskFitsB (cs : Codes) (M : List OracleShape) (L : LaidP) (n t im k : ℕ) : Bool :=
  decide (im < n) && placesBelowB L n t &&
    match M[im]? with
    | none => false
    | some sh =>
      decide (0 < sh.maskRows) && decide (1 ≤ sh.answers) &&
        decide (k <
          Send.freeMaskEntries sh.maskRows (cs.mask.getD sh.maskCode default).ell sh.answers)

/-- **THE STATEMENT.** -/
def MaskEntryIs : Prop :=
  ∀ (P Cells Tok : Type) (Fr : Frame) (N : Numbers)
    (Mg : Meaning P (VerifiableInference.Desc.Wit Cells Tok MsgT)) (Z : P) (links : List ModelPart)
    (ps : List Place) (j m : ℕ) (M : List OracleShape) (L : LaidP) (cs : Codes)
    (fvs : List Bool) (sh : OracleShape) (q : ℕ × ℕ),
    EShapes Mg M → EBook0 Mg → ESeats Mg L → ECodes Mg cs →
    openMaskB Mg.more links ps j = true →
    maskFitsB cs M L (N.msgsAt ps[j]?) (N.treesAt ps[j]?) N.indexNo (rowsBefore fvs m) = true →
    M[N.indexNo]? = some sh → L.places[N.indexNo]? = some q →
    ∀ b : S × Fr.E.Str, onQ N Mg links ps (fun s => (Z, s)) j b → b.1.failed = none →
      ∀ (nR kC : ℕ) (arr : ℕ → ℕ → ℕ) (mat : Cells → Fin nR → (Fin kC → Bool) → GE)
        (w : VerifiableInference.Desc.Wit Cells Tok MsgT),
        (rwBook arr mat (Z, b.1) w).mask
            ⟨N.indexNo, nextNoP M (N.msgsAt ps[j]?) N.indexNo fvs m⟩ =
          w.tab cs sh (arr q.1 q.2) q.1 q.2 true (rowsBefore fvs m % sh.maskRows)
            (rowsBefore fvs m / sh.maskRows)

end OnBytes.Road.K4.Rec
