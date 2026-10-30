-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/WitFits.lean: the honest side of the kind "lookup" (K3): tests with
code on public data that reject the shapes at which the filling of the letters `Sources`, or a term
beneath it, fills in a value in silence. Definitions with code, and theorems: an acceptance gives
the hypothesis.

Terms. Honest/K3/GLOSSARY.md.

Why. The filling (Honest/K3/WitOwner.lean) and the terms that it calls are total functions. At some
public shapes they fill in a value where nothing is due: a sampled matrix that is shorter than the
smallness test's columns ask counts as 0 beyond its end; a digit that stands in no row of its range
table is counted at row 0; a matrix number beyond a link's list reads 0; a digit's place beyond ZZ's
rows or columns reads 0; a mark of a borrowed matrix beyond its owner's list reads the name "". Each
test here rejects one such shape. They are functions of plain public data: tl, the structure of a
smallness test; a public part X; a link's number.

What is defined and shown.
  1 `hasPlan`: the public part has a plan at the link (else tlOf X link is the empty structure).
  2 `tritsDueOf`, `tritsDue`, `tritsFitB`: how many matrix entries the smallness test's round must
    sample: (the sum of the matrices' columns) times tau; a declared number is that number. The
    verifier's own planner makes the same number for the round "RNG" (`rngRound`,
    OnBytes/Tie/Pv/Tail/Plan.lean, at `smallSize tl`, OnBytes/Model/RoundSizes.lean); the tie:
    `tritsDueOf_eq_planner` (Honest/K3/Law/TiesSealedFits.lean [not in this library]).
  3 `mzFitsB`, `mzFitsB_holds`: tl.mz is the number of all rows of cells: `MzFits`
    (Johnson/HonestTrace/DigitsAtTrace.lean).
  4 `colsFitB`, `digitsOk`: the library's test on the digits' columns (`DgP.colsTest`,
    OnBytes/Tie/Pv/Lookup/Digits/PortCols.lean); there is a matrix; the list has as many matrices as
    are counted; with `hasPlan`: `digitsOk`.
  5 `tablesFitB`: the lookup on the digits has two calls, on the range tables of 2 ^ 10 and of 2 ^ 8
    rows, each with the padding row 0.
  6 `piecesFitB`, `piecesFitB_holds`: a test whose acceptance gives `Fo.ZPlan.FromPieces`
    (OnBytes/Tie/Pv/Lookup/Ends/FoZPlaced1.lean): the library's own maker of the two calls
    (`HTailF2.piecesF`, OnBytes/Model/Tail.lean), run on tl itself, returns the ten fields that tl
    has. `FromPieces` asks that some structure's maker returns them: that a rejection by the test
    refutes it is neither shown nor said.
  7 `namesDue`, `namesFitB`: a link's list has the names, in the order, that the layout's numbers
    ask: so every matrix number that names a matrix of the layout lies in the list.
  8 `markFitsB`, `marksFitB`: each borrowed entry's mark names an entry of the list of a group of
    layers in front of the link, which that group owns; every entry begins at column 0.
  9 `listFitsB`: 7 and 8.
  10 `tailFitsB`, `tailFitsB_holds`: the library's test on the pieces of the two calls
    (`DgP.tailTest`, OnBytes/Tie/Pv/Lookup/Digits/PortLaws.lean): a piece has tl.mz columns and lies
    in the rows below tau.
  11 `featuresG`, `featuresA`, `featuresH`, `featuresFitB`: a feature's number is turned into a
    matrix number by a division: no divisor is 0, and the features that the layout counts have room
    in their family's matrices: so no computed number leaves the family.
In each of the theorems with "_holds" or "_eq" in their names the hypothesis is: the test accepts;
it bears the letter `h` in five of the six; `samePieces_eq` has it without a name.

Imported, through Honest/K3/WitOwner.lean: Johnson/HonestTrace/DigitsAtTrace.lean.

Users. The theorems that are stated of this filling's keys, bits and rounds take these tests, or
what an acceptance by them gives, as hypotheses. Honest/K3/SeatFits.lean, Honest/K3/BzTie.lean,
Honest/K3/WitFitsGuards.lean [not in this library], Honest/K3/WitPlaysFits.lean
[not in this library], Honest/K3/WitAttnPlayBig.lean [not in this library],
Honest/K3/WitAttnPlayQa.lean [not in this library] and Honest/K3/WitHeadPlayNF.lean
[not in this library] import this file.

Limits. `featuresFitB` goes by the layout's own counts of features (a tensor's first feature, limbs,
instances and features; the streams' limbs and channels; attention's places of "as"; the head's
counts): that a key's term asks no instance or feature beyond its tensor's counts is not tested
here: it is a matter of the calls' layouts against the tensors' counts, which the library's own
maker of the public part puts together: the one test that reaches it is that the public part is what
that maker returns of the public files (`madeB`, Honest/K3/SeatFits.lean). The columns of a matrix
are not tested against the reader of cells: what a reader answers beyond a matrix's shape is a
matter of the reader. That a round samples as many matrix entries as it declares is the frame's own
test on a challenge. `piecesFitB` rejects every small structure: the maker asks 2 ^ 10 keys in a
call. No test here reads a cell, a weight or a coin.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.WitOwner
import Johnson.Desc.First.Look.K3Borders
import Johnson.Desc.First.Att.Door.ShapeSame
import OnBytes.Tie.Pv.Lookup.Digits.PortCols
import OnBytes.Tie.Pv.Lookup.Digits.PortLaws
import OnBytes.Tie.Pv.Lookup.Ends.FoZPlaced1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes.Model (HTailF2 TMat Piece CallZ)
open OnBytes.HonestTrace (MzFits)
open OnBytes.Road (Hd.shapeA)
open ProofFile.Honest.K8 (parOfTail)
open VerifiableInference.Desc.First.K8.Honest (allRows)
open VerifiableInference.Desc.K3 (sameCall sameShapeAll)

/-! ## 1 A plan at the link -/

/-- The public part has a plan at the link: the head's; or, by the link's number, a group's layers'
or its attention's. -/
def hasPlan (X : OnBytes.Model.Verify.Public) (link : ℕ) : Bool :=
  link == linkH X ||
    (if link % stepOf X == 0 then (X.G[link / stepOf X]?).isSome
     else (X.A[link / stepOf X]?).isSome)

/-! ## 2 The sampled matrix's length -/

/-- The number of matrix entries that the smallness test's round must sample: tau for each column of
each matrix. -/
def tritsDueOf (tl : HTailF2) : ℕ := (tl.mats.toList.map (·.k)).sum * tl.tau

/-- The same at a link of a public part. -/
def tritsDue (X : OnBytes.Model.Verify.Public) (link : ℕ) : ℕ := tritsDueOf (tlOf X link)

/-- A round's declared number of matrix entries is the number that is due. -/
def tritsFitB (tl : HTailF2) (declared : ℕ) : Bool := declared == tritsDueOf tl

/-! ## 3 The rows of cells -/

/-- tl.mz is the number of all rows of cells of tl's matrices. -/
def mzFitsB (tl : HTailF2) : Bool := tl.mz == allRows (parOfTail tl)

/-- An acceptance gives `MzFits`. -/
theorem mzFitsB_holds (tl : HTailF2) (h : mzFitsB tl = true) : MzFits tl := by
  unfold mzFitsB at h
  exact beq_iff_eq.1 h

/-! ## 4 The digits' columns -/

/-- The library's test on the digits' columns accepts; there is a matrix; the list has as many
matrices as are counted. -/
def colsFitB (tl : HTailF2) : Bool :=
  OnBytes.DgP.colsTest tl && decide (0 < tl.NM) && decide (tl.NM = tl.mats.size)

/-- `hasPlan` and `colsFitB` at a link, as one test. -/
def digitsOk (X : OnBytes.Model.Verify.Public) (link : ℕ) : Bool :=
  hasPlan X link && colsFitB (tlOf X link)

/-! ## 5 The two range tables -/

/-- A call on the range table of 2 ^ k rows with the padding row 0: no written table, no flag. -/
def rangeCallB (c : OnBytes.Model.Call) (k : ℕ) : Bool :=
  c.k == k && c.t0 == 0 && c.fn == 0 && c.tau.isNone

/-- Two calls: the low digits' on 2 ^ 10 rows, the high digits' on 2 ^ 8. -/
def tablesFitB (tl : HTailF2) : Bool :=
  tl.f9.calls.size == 2 && rangeCallB (tl.f9.calls.getD 0 {}) 10 &&
    rangeCallB (tl.f9.calls.getD 1 {}) 8

/-! ## 6 The whole of `FromPieces` -/

/-- Two pieces are the same: read by the whole constructor. -/
def samePiece : Piece → Piece → Bool
  | ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ =>
    a1 == b1 && a2 == b2 && a3 == b3 && a4 == b4 && a5 == b5 && a6 == b6 && a7 == b7 &&
      a8 == b8 && a9 == b9 && a10 == b10

theorem samePiece_eq {a b : Piece} (h : samePiece a b = true) : a = b := by
  cases a
  cases b
  simp only [samePiece, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
  rfl

/-- Two lists of pieces are the same: as long, and one by one. -/
def samePieces : List Piece → List Piece → Bool
  | [], [] => true
  | a :: as, b :: bs => samePiece a b && samePieces as bs
  | _, _ => false

theorem samePieces_eq : ∀ {a b : List Piece}, samePieces a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [samePieces] at h
  | _ :: _, [], h => by simp [samePieces] at h
  | a :: as, b :: bs, h => by
    simp only [samePieces, Bool.and_eq_true] at h
    rw [samePiece_eq h.1, samePieces_eq h.2]

/-- Two calls with their pieces are the same. -/
def sameCallZ (a b : CallZ) : Bool :=
  sameCall a.call b.call && samePieces a.pieces.toList b.pieces.toList

theorem sameCallZ_eq {a b : CallZ} (h : sameCallZ a b = true) : a = b := by
  unfold sameCallZ at h
  rw [Bool.and_eq_true] at h
  cases a with
  | mk ac ap =>
  cases b with
  | mk bc bp =>
  have e1 : ac = bc := H2K5.Door.sameCall_eq h.1
  have e2 : ap = bp := Array.toList_inj.1 (samePieces_eq h.2)
  rw [e1, e2]

/-- **A test with code whose acceptance gives `FromPieces`**: the library's maker of the two calls,
run on tl itself, returns, and the ten fields that the library's tests read are tl's. -/
def piecesFitB (tl : HTailF2) : Bool :=
  match tl.piecesF with
  | .ok p =>
    decide (tl.ix = p.ix) && decide (tl.blocks = p.blocks) && sameCallZ tl.z1 p.z1 &&
      sameCallZ tl.z2 p.z2 && decide (tl.gtTree = p.gtTree) && decide (tl.NM = p.NM) &&
      decide (tl.tau = p.tau) && decide (tl.lidb = p.lidb) && decide (tl.mz = p.mz) &&
      sameShapeAll tl.f9 p.f9
  | .error _ => false

/-- **An acceptance gives `Fo.ZPlan.FromPieces`.** -/
theorem piecesFitB_holds (tl : HTailF2) (h : piecesFitB tl = true) : Fo.ZPlan.FromPieces tl := by
  unfold piecesFitB at h
  split at h
  · rename_i p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
    exact ⟨tl, p, hp, ⟨⟨h1, h2, sameCallZ_eq h3, sameCallZ_eq h4, h5, h6⟩, h7, h8, h9,
      H2K5.Door.sameShapeAll_eq h10⟩⟩
  · exact absurd h (by simp)

/-! ## 7 The list's names -/

/-- n names: a stem with the numbers 0 to n - 1. -/
def partNames (stem : String) (n : ℕ) : List String :=
  (List.range n).map fun p => stem ++ toString p

/-- The names that the layout's numbers ask of a link's list, in the list's order. The head: the
parts of hf; hd, hr, bH, the stream. A group's layers: the parts of af and of ad; ar, b, qa, the
stream that goes out, the stream that comes in. A group's attention: the parts of as; ah, ao, bA,
qa. -/
def namesDue (X : OnBytes.Model.Verify.Public) (link : ℕ) : List String :=
  if link == linkH X then partNames "hf" X.hS.NHf ++ ["hd", "hr", "bH", "xbL"]
  else if link % stepOf X == 0 then
    partNames "af" (X.y.parts.getD 0 0) ++ partNames "ad" (X.y.parts.getD 1 0) ++
      ["ar", "b", "qa", "xbO", "xbI"]
  else partNames "as" (Hd.shapeA X (link / stepOf X)).cf.NAs ++ ["ah", "ao", "bA", "qa"]

/-- The link's list has these names, in this order, and no more. -/
def namesFitB (X : OnBytes.Model.Verify.Public) (link : ℕ) : Bool :=
  (tlOf X link).mats.toList.map (·.name) == namesDue X link

/-! ## 8 The borrowed entries' marks -/

/-- An entry that is not borrowed begins at column 0 of its own array. A borrowed entry's mark names
a group of layers (not sub-proof 0; a group that there is) whose link stands in front of this link,
and an entry of that link's list which that group owns; it begins at column 0. An entry of another
kind than 0 or 1 is rejected. -/
def markFitsB (X : OnBytes.Model.Verify.Public) (link : ℕ) (M : TMat) : Bool :=
  if M.kind == 0 then M.ttOff == 0
  else
    M.kind == 1 && decide (256 ≤ M.aId) && decide (M.aId / 256 - 1 < X.NGr) &&
      decide (linkG X (M.aId / 256 - 1) < link) && M.ttOff == 0 &&
      (((tlOf X (linkG X (M.aId / 256 - 1))).mats[M.aId % 256]?).any fun O => O.kind == 0)

/-- Every entry of the link's list passes. -/
def marksFitB (X : OnBytes.Model.Verify.Public) (link : ℕ) : Bool :=
  (tlOf X link).mats.toList.all (markFitsB X link)

/-! ## 9 The list -/

/-- The names and the marks. -/
def listFitsB (X : OnBytes.Model.Verify.Public) (link : ℕ) : Bool :=
  namesFitB X link && marksFitB X link

/-! ## 10 The pieces of the two calls -/

/-- The library's test on the shape of the lookup on the digits, `OnBytes.DgP.tailTest`: among its
clauses: every piece of both calls has tl.mz columns, at most as many as its stretch's width, lies
in the rows below tau, and its stretch lies inside its call's keys. -/
def tailFitsB (tl : HTailF2) : Bool := OnBytes.DgP.tailTest tl

/-- An acceptance gives the library's `TailOK`. -/
theorem tailFitsB_holds (tl : HTailF2) (h : tailFitsB tl = true) : OnBytes.DgP.TailOK tl :=
  OnBytes.DgP.tailOK_of_test h

/-! ## 11 The features' room -/

/-- The matrices of family mu of a group's layers: the parts of af and of ad; one of ar, one of qa.
-/
def famParts (y : OnBytes.Model.Layer.Lay) (mu : ℕ) : ℕ := if mu < 2 then y.parts.getD mu 0 else 1

/-- The features that one matrix of family mu holds. -/
def famUnit (y : OnBytes.Model.Layer.Lay) (mu : ℕ) : ℕ :=
  y.kcol.getD mu 0 * (y.mrow.getD mu 0 / y.T)

/-- A group's layers: there is a token; every tensor lies in one of the four families, a matrix of
which holds a feature, and its features end inside the family; a stream's matrix holds a feature,
and the stream's limbs of all channels have room in it. -/
def featuresG (y : OnBytes.Model.Layer.Lay) : Bool :=
  decide (0 < y.T) &&
    (y.ten.all fun X => decide (X.mat < 4) && decide (0 < famUnit y X.mat) &&
      decide (X.OFF + X.nl * X.cnt * X.J ≤ famParts y X.mat * famUnit y X.mat)) &&
    decide (0 < y.kxb * (y.mxb / y.T)) && decide (y.h.xl * y.h.d ≤ y.kxb * (y.mxb / y.T))

/-- A group's attention: "as" has a part, a part has a column, and the five planes' places of all
layers and pairs have room in the parts. The other matrices are asked by fixed numbers. -/
def featuresA (S : OnBytes.Attention.Shape) : Bool :=
  decide (0 < S.cf.NAs) && decide (0 < S.kAs / S.cf.NAs) &&
    decide (5 * S.Lam * S.HA * (2 ^ S.nM + 2 ^ S.nD) ≤
      2 ^ S.cf.lmS * (S.kAs / S.cf.NAs * S.cf.NAs))

/-- The head (its number of positions is a power of two, so it is not 0): a matrix of hf, hd, hr and
the stream's holds a feature; the features that the layout counts have room: hf's in its parts,
hd's, hr's and the stream's tensor's in one matrix each. -/
def featuresH (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL)
    (b : OnBytes.Model.Head.Border) : Bool :=
  decide (0 < L.k * (L.m / h.T)) &&
    decide (L.filled ≤ h.NHf * (L.k * (L.m / h.T))) && decide (0 < L.kD * (L.mD / h.T)) &&
    decide (L.fillD ≤ L.kD * (L.mD / h.T)) && decide (0 < L.kR * (L.mR / h.T)) &&
    decide (L.fillR ≤ L.kR * (L.mR / h.T)) && decide (0 < b.kxb * (b.mxb / h.T)) &&
    decide (b.off + ((b.nl - 1) * b.cnt + 1) * b.J ≤ b.kxb * (b.mxb / h.T))

/-- The test of the link's sort. -/
def featuresFitB (X : OnBytes.Model.Verify.Public) (link : ℕ) : Bool :=
  if link == linkH X then featuresH X.hS X.HLy (OnBytes.Model.Verify.borderOf X.y)
  else if link % stepOf X == 0 then featuresG X.y
  else featuresA (Hd.shapeA X (link / stepOf X))

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.tailFitsB_holds
#print axioms ProofFile.Honest.K3.mzFitsB_holds
#print axioms ProofFile.Honest.K3.samePiece_eq
#print axioms ProofFile.Honest.K3.samePieces_eq
#print axioms ProofFile.Honest.K3.sameCallZ_eq
#print axioms ProofFile.Honest.K3.piecesFitB_holds
