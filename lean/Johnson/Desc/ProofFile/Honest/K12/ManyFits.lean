-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ManyFits.lean

What it defines. For a job of a proximity test on a group of several oracle messages (ManyJob,
RunMany.lean): the job's own rows as plain functions (plainMany), the job's own trees' columns by
the tree's number in the verifier's book (colsMany), and one test with code on public things alone
(manyFitsB): the first stage, the members' public numbers, the job's list of trees, and the shape of
the plain data that the verifier's guard makes (PlainS,
Johnson/Desc/K12/Honest/Shape/TestDoor.lean). manyFitsS: the same test at what the guard makes on
the thin shape of the state in front. Definitions alone; the law is in ManyFitsLaw.lean.

Names.
  memRows, plainMany   member j's own lists at its own random values; the rows as plain functions.
  colsMany   the column functions.
  pieceLen, wordsBefore   how many words a piece of a tree's column has; how many stand in front of
      the first piece of a given kind.
  memFitsB, apartB₂, treeFitsB, seatFitsB, manyFitsB   the test, clause by clause.
  manyFitsS   on the thin shape.

Limits. Main rows over the extension field alone: the test is false at a member that has main rows
and whose shape says base. A member that is kept is not told apart here (the guard's own clauses
refuse it). That the test is true is shown at no parameters here. Nothing on completeness, on
soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunMany
import Johnson.Desc.ProofFile.Honest.K12.PlanB
import Johnson.Desc.K12.Honest.Shape.TestDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice (lst)
open Fmt.M1 (Stage)
open Fmt.M1.Own (PSt)
open VerifiableInference.Desc.K12 (P12 T12)
open H2K.First (Plain Seat1 oM oZ skM skZ)
open ProofFile.Honest.K12 (PlainRows TestCoins stA)
open ProofFile.Honest.Sh (PlainS ThinSh batThin gpOfS logAtS widthAtS)

variable {W X : Type}

/-- Member j's own lists, at its own random values; empty lists where there is no member j. -/
def memRows (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins) (j : ℕ) : PSt :=
  match A.mems[j]? with
  | some m => m.rows w fr (C.mem j)
  | none => { M := [], Rh := [], W := [], Sg := [], P := [], Pi := [] }

/-- **The job's own rows, as plain functions.** Member, row, place. The fresh table's: as the first
stage's state holds them. -/
def plainMany (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins) : PlainRows where
  M := fun j i e => lst ((memRows A w fr C j).M.getD i []) e
  T := fun j i q => lst ((memRows A w fr C j).Rh.getD i []) q
  Z := fun j i e => lst ((memRows A w fr C j).W.getD i []) e
  ZT := fun j i q => lst ((memRows A w fr C j).Sg.getD i []) q
  F := (A.toRun.toTest.first w fr C).fM
  FT := (A.toRun.toTest.first w fr C).fT

/-- **The job's own trees' columns**, by the tree's number in the book: ts lists these numbers in
the order of the job's trees. At a number that is not listed: the column of the job's tree number
ts.length, if the job has so many trees; else the empty column. -/
def colsMany (A : ManyJob W X) (ts : List ℕ) (w : W) (fr : Front X) (C : TestCoins) (u x : ℕ) :
    List UInt64 :=
  (((A.toRun.toTest.trees₀ w fr C.mem (A.toRun.toTest.first w fr C))[ts.idxOf u]?).map
    (·.2 x)).getD []

/-- The number of words of a piece of a column: three for each row. -/
def pieceLen (s : Stage) (ms : List MemShape) (q : Piece) : ℕ := 3 * (selsOf s ms q).length

/-- The number of words in front of the first piece q of a list; none where q is not in it. -/
def wordsBefore (s : Stage) (ms : List MemShape) (q : Piece) : List Piece → Option ℕ
  | [] => none
  | r :: l => if r = q then some 0 else (wordsBefore s ms q l).map (pieceLen s ms r + ·)

/-- Member j's public numbers are the seat's and the layout's; its blocks lie within the tables. -/
def memFitsB (s : Stage) (L : OnBytes.GroupLayout) (j : ℕ) (m : MemShape) (x : Seat1) : Bool :=
  x.sh.mainRows == m.mainRows && x.sh.maskRows == m.maskRows &&
    (m.mainRows == 0 || (!m.base && x.sh.mainDeg != 1 && oM L j == m.mainFirst)) &&
    (m.maskRows == 0 || oZ L j == m.maskFirst) &&
    decide (m.mainFirst + m.mainRows ≤ 2 ^ s.k) && decide (m.maskFirst + m.maskRows ≤ 2 ^ s.h)

/-- No two blocks (first row, number of rows) overlap. -/
def apartB₂ (bs : List (ℕ × ℕ)) : Bool :=
  bs.zipIdx.all fun a => bs.zipIdx.all fun b =>
    a.2 == b.2 || a.1.2 == 0 || b.1.2 == 0 || decide (a.1.1 + a.1.2 ≤ b.1.1) ||
      decide (b.1.1 + b.1.2 ≤ a.1.1)

/-- The job's tree number i has the book's depth and width at the number u. -/
def treeFitsB (s : Stage) (ms : List MemShape) (D : PlainS) (T : ℕ × List Piece) (u : ℕ) : Bool :=
  T.1 == logAtS D.book u && (T.2.map (pieceLen s ms)).sum == widthAtS D.book u

/-- In the job's tree that stands at the seat's tree, the words in front of the piece q number n. -/
def seatFitsB (s : Stage) (ms : List MemShape) (trees : List (ℕ × List Piece)) (ts : List ℕ)
    (t : ℕ) (q : Piece) (n : ℕ) : Bool :=
  match trees[ts.idxOf t]? with
  | some T => wordsBefore s ms q T.2 == some n
  | none => false

/-- **The test.** -/
def manyFitsB (s : Stage) (ms : List MemShape) (trees : List (ℕ × List Piece)) (D : PlainS) :
    Bool :=
  decide (s.h ≤ s.k) && D.mems.length == ms.length &&
    ((ms.zip D.mems).zipIdx.all fun y => memFitsB s D.L y.2 y.1.1 y.1.2) &&
    apartB₂ (ms.map fun m => (m.mainFirst, m.mainRows)) &&
    apartB₂ (ms.map fun m => (m.maskFirst, m.maskRows)) &&
    decide D.ts.Nodup && D.ts.length == trees.length &&
    ((trees.zip D.ts).all fun y => treeFitsB s ms D y.1 y.2) &&
    ((ms.zip D.mems).zipIdx.all fun y =>
      (y.1.1.mainRows == 0 ||
        seatFitsB s ms trees D.ts y.1.2.t (.main y.2) (skM y.1.2.tsh y.1.2.part)) &&
      (y.1.1.maskRows == 0 ||
        seatFitsB s ms trees D.ts y.1.2.t (.mask y.2) (skZ y.1.2.tsh y.1.2.part))) &&
    seatFitsB s ms trees D.ts D.fresh.t .fresh (skZ D.fresh.tsh D.fresh.part)

/-- **The test at what the guard makes on the thin shape of the state in front.** -/
def manyFitsS (p : P12) (ms : List MemShape) (trees : List (ℕ × List Piece)) (a₀ : ThinSh) : Bool :=
  match batThin p a₀ with
  | some aB =>
    match aB.pass with
    | .claim L =>
      match gpOfS p aB (stA p) L with
      | some D => manyFitsB (stA p) ms trees D
      | none => false
    | _ => false
  | none => false

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.memRows
#print axioms ProofFile.Honest.K12.Light.plainMany
#print axioms ProofFile.Honest.K12.Light.colsMany
#print axioms ProofFile.Honest.K12.Light.pieceLen
#print axioms ProofFile.Honest.K12.Light.wordsBefore
#print axioms ProofFile.Honest.K12.Light.memFitsB
#print axioms ProofFile.Honest.K12.Light.apartB₂
#print axioms ProofFile.Honest.K12.Light.treeFitsB
#print axioms ProofFile.Honest.K12.Light.seatFitsB
#print axioms ProofFile.Honest.K12.Light.manyFitsB
#print axioms ProofFile.Honest.K12.Light.manyFitsS
