-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/SmallLaw.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: WHERE
NO COMBINATION LEAVES ITS WINDOW, EVERY SINGLE EQUATION OF THE TEST's TIES AND READS HOLDS AT A
TABLE OF CELLS THAT IS MADE OF THE CELLS, AND THE DIGITS ARE IN THEIR TABLES: AS STATEMENTS ALONE:
definitions of type Prop. NO THEOREM HERE: the proofs of six are Honest/K8/SmallLawProofs.lean's. No
statement of this library concludes `Spec.readAt_tab` as it stands here; its sum stands at every
place of the tables as `tieThird_sent` (Johnson/HonestTrace/ReadsTie.lean), under `ParFits` and
`TablesLie` in the stead of `inARow`. LEMMAS ON THE HONEST PROVER's ARRAYS; NONE OF THE LIBRARY's
GOALS.

The two sentences behind the kind's round are the library's own: every row of `rowsTail`
(OnBytes/Tie/Pv/Tail/EndRows.lean) is 0 at the table: the body of `SmallAt`
(Johnson/Desc/First/K8/LawItems.lean); and `DigitsOf` (Johnson/Desc/First/K8/DigitsOf.lean). The
soundness side goes from these two to the sentence in front, but for an error. Here the way forward.

WHAT IS ASKED OF THE TABLE A (array, row, column), at integers a, one for each cell:
  `TieBy tl A a`    the symbol arrays' cells are the packing of a; every entry of the vector of
                     reads that a table of the closed list names is the weighted sum of its stretch
                     of a: THE SECOND AND THIRD CLAUSE OF `TieOf`, at a by name
  `ZzBy tl A a`     the cells of the array of digits, IN ITS tau ROWS AND 2 mz COLUMNS, are
                     `digitAt` at a and at the drawn matrix that lies in tl; of cells beyond
                     nothing is asked
WHAT IS ASKED OF THE VERIFIER's STATE OF THE TEST tl, behind the draw:
  `DrawLaid tl`    the digits' columns fit the matrices' rows (`DigitColsFit`,
                     Honest/K8/AddressLaw.lean: the library's own test with code); the first columns
                     of the drawn matrix are the place's; every drawn entry is -1, 0 or 1
  `Port.Fits tl`    the library's: the shapes fit the matrices
  `allOnThird tl`   every table of the closed list lies on the third vector of reads
THE STATEMENTS:
  `Spec.tieOf_of_tieBy`   `TieBy` at integers below twice the shift gives `TieOf`
  `Spec.zz_back`     in the field: low + 2^10 high - 2^17 is the combination
  `Spec.ties_zero`, `Spec.reads_zero`   each single tie, each single equation of a read, is 0
  `Spec.digits_in`   `DigitsOf`: WITH NO PREMISE ON THE WINDOW OR ON THE DRAWN MATRIX
  **`Spec.small_of_honest`**   the two sentences together
  `Spec.readAt_tab`  `readAt` (Johnson/Desc/K8/Honest/Arrays.lean) meets `TieBy`'s clause on the
                     reads, where the list's parts are laid in a row (`inARow`)
Limits. One place; plain data: no block, no frame, no message. NOT SAID HERE, AND OWED: that a state
behind the draw has `DrawLaid` and a list laid in a row (by reading, the kind's own yes lays the
first columns and the entries, and holds the list against the place's shapes); that a plan's state
passes the library's test on the digits' columns; that the arrays which a prover sends are such a
table: from `zzOf` to `ZzBy`, from the packed cells to `TieBy`'s first clause; and the way from
these two sentences to a table of joints' own items.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.AddressLaw
import Johnson.Desc.K8.Honest.Arrays
import Johnson.Desc.First.K8.LawItems
import Johnson.Desc.First.K8.DigitsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail OnBytes.Tie.Pv.Tail.Port
open VerifiableInference.Desc.First.K8 (Par firstColumns TieOf DigitsOf)
open VerifiableInference.Desc.First.K8.Honest

/-- A table of cells: array, row, column. -/
abbrev TableE : Type := ℕ → ℕ → ℕ → Cb.Gl.E

/-- The symbol arrays and the vector of reads are made of the integers a. -/
def TieBy (tl : HTailF2) (A : TableE) (a : CellsAt) : Prop :=
  (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
    ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
      A (tl.gtTree.getD μ 0) i' c =
        ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => a μ i c) i' : ℤ) :
          Cb.Gl.E)) ∧
  (∀ (n : ℕ) (Fn : HFun), tl.funs[n]? = some Fn → ∀ c sg pos, tl.tabAt Fn c sg = some pos →
    A (u3Of tl) 0 pos =
      ∑ j ∈ Finset.range Fn.len,
        Reading.gl.val (Fn.phi.getD j zeroE) * ((a Fn.mat (sg * Fn.len + j) c : ℤ) : Cb.Gl.E))

/-- The array of digits, in its tau rows and 2 mz columns, is made of the integers a and of the
drawn matrix that lies in tl. -/
def ZzBy (tl : HTailF2) (A : TableE) (a : CellsAt) : Prop :=
  ∀ u, u < tl.tau → ∀ col, col < 2 * tl.mz →
    A tl.ix.ZZ u col = ((digitAt (parOfTail tl) a tl.cfF u col : ℕ) : Cb.Gl.E)

/-- What is asked of the verifier's state of the test, behind the draw. -/
structure DrawLaid (tl : HTailF2) : Prop where
  /-- the digits' columns fit the matrices' rows of cells -/
  digits : DigitColsFit tl
  /-- the first columns of the drawn matrix -/
  first : tl.cfFirst = firstColumns (parOfTail tl)
  /-- every drawn entry -/
  trits : ∀ n, tl.cfF.getD n 0 = -1 ∨ tl.cfF.getD n 0 = 0 ∨ tl.cfF.getD n 0 = 1

/-- Every table of the closed list lies on the third vector of reads. -/
def allOnThird (tl : HTailF2) : Prop := ∀ Fn ∈ tl.funs.toList, Fn.tree = 2

/-- The list's parts are laid in a row from entry e on: each begins where the one in front ends. -/
def inARow (p : Par) : Nat → List HFun → Bool
  | _, [] => true
  | e, f :: fs => f.start == e && inARow p (e + partLength p f) fs

namespace Spec

/-- States: at integers below twice the shift it is the library's sentence in front of the draw. -/
def tieOf_of_tieBy : Prop :=
  ∀ (tl : HTailF2) (A : TableE) (a : CellsAt), TieBy tl A a →
    (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k → ∀ i, i < (tl.mats.getD μ {}).m →
      |a μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) → TieOf tl A

/-- States: in the field the two digits of a row of cells give its combination back. -/
def zz_back : Prop :=
  ∀ (tl : HTailF2) (A : TableE) (a : CellsAt), DigitColsFit tl → ZzBy tl A a →
    leaves (parOfTail tl) a tl.cfF = none →
    ∀ μ, μ < tl.NM → ∀ u, u < tl.tau → ∀ i, i < (tl.mats.getD μ {}).m →
      A tl.ix.ZZ u ((tl.zzCol μ 0 0).getD 0 + i) +
          (2 : Cb.Gl.E) ^ 10 * A tl.ix.ZZ u ((tl.zzCol μ 1 0).getD 0 + i) - (2 : Cb.Gl.E) ^ 17 =
        ((comb (parOfTail tl) a tl.cfF μ i u : ℤ) : Cb.Gl.E)

/-- States: each single tie is 0. -/
def ties_zero : Prop :=
  ∀ (tl : HTailF2) (A : TableE) (a : CellsAt), DrawLaid tl → Fits tl → TieBy tl A a →
    ZzBy tl A a → leaves (parOfTail tl) a tl.cfF = none →
    ∀ r ∈ tieRows (K := Cb.Gl.E) tl 0, r.2 A = 0

/-- States: each single equation of a read is 0. -/
def reads_zero : Prop :=
  ∀ (tl : HTailF2) (A : TableE) (a : CellsAt), DrawLaid tl → allOnThird tl → TieBy tl A a →
    ZzBy tl A a → leaves (parOfTail tl) a tl.cfF = none →
    ∀ r ∈ readRowsFrom Reading.gl tl 0 0 (readsList tl tl.funs), r.2 A = 0

/-- States: the digits are in their tables: whatever lies in the place of the drawn matrix. -/
def digits_in : Prop :=
  ∀ (tl : HTailF2) (A : TableE) (a : CellsAt), DigitColsFit tl → ZzBy tl A a → DigitsOf tl A

/-- **States: where no combination leaves its window, both sentences behind the draw hold.** -/
def small_of_honest : Prop :=
  ∀ (tl : HTailF2) (A : TableE) (a : CellsAt), DrawLaid tl → Fits tl → allOnThird tl →
    TieBy tl A a → ZzBy tl A a → leaves (parOfTail tl) a tl.cfF = none →
    (∀ r ∈ rowsTail Reading.gl tl tl.funs 0, r.2 A = 0) ∧ DigitsOf tl A

/-- States: the vector of reads as a function of the cells meets the clause on the reads. -/
def readAt_tab : Prop :=
  ∀ (tl : HTailF2) (a : CellsAt), inARow (parOfTail tl) 0 tl.funs.toList = true →
    ∀ (n : ℕ) (Fn : HFun), tl.funs[n]? = some Fn → ∀ c sg pos, tl.tabAt Fn c sg = some pos →
      Reading.gl.val (readAt (parOfTail tl) tl.funs.toList a pos) =
        ∑ j ∈ Finset.range Fn.len,
          Reading.gl.val (Fn.phi.getD j zeroE) * ((a Fn.mat (sg * Fn.len + j) c : ℤ) : Cb.Gl.E)

end Spec

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.TableE
#print axioms ProofFile.Honest.K8.TieBy
#print axioms ProofFile.Honest.K8.ZzBy
#print axioms ProofFile.Honest.K8.DrawLaid
#print axioms ProofFile.Honest.K8.allOnThird
#print axioms ProofFile.Honest.K8.inARow
#print axioms ProofFile.Honest.K8.Spec.tieOf_of_tieBy
#print axioms ProofFile.Honest.K8.Spec.zz_back
#print axioms ProofFile.Honest.K8.Spec.ties_zero
#print axioms ProofFile.Honest.K8.Spec.reads_zero
#print axioms ProofFile.Honest.K8.Spec.digits_in
#print axioms ProofFile.Honest.K8.Spec.small_of_honest
#print axioms ProofFile.Honest.K8.Spec.readAt_tab
