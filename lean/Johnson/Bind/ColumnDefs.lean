-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ColumnDefs.lean: THE LIBRARY'S HONEST ENCODER OF A STORED TABLE AND THE RUNNING
COMMITTER'S ENCODER, FACE TO FACE: the statements, general in the sizes. Definitions of propositions
alone: nothing is proved here (the proofs: Johnson/Bind/Column.lean, Johnson/Bind/Digits.lean).

Why. A committer is written as mathematics over the library's honest side of a stored table
(`codingCells`, Johnson/Flat/CodingCells.lean): a matrix of cells becomes words, the words become
messages in the field, the messages become words again, and the format's own function for a symbol
(`Fmt.M1.symF`) encodes them. A committer that runs (Johnson/Bind/Twin.lean) lays its table's rows
as lists of words and encodes them with the same function. If the order of a row's entries, the
place of its pads or the place of its random tail parted between the two, leaves of the two hash
trees would part. The statements here say that they do not. They name no hash function, no query and
no string: this is the part of the comparison that is free of hashing.

Main names (namespace `Bind.Column`).
  `Agree sh S cut`: the running committer's shape sh has the a, l, r and v of the library's sizes S,
    and its pads begin at cut. The salt's length is compared with nothing here.
  `RowsBack S`: words that are read in the field as messages and written as words again are the same
    words, at a row that the table has, if there are as many as a message has entries and each is
    below the prime.
  `RowsResidues S`: the same with no condition on the words: a list that is too short counts as
    filled with 0, one that is too long as cut, and a word counts as its residue modulo the prime.
  **`ColumnAgrees S Z cut N sh`**: at every matrix of cells, all tails, pads and salts given as raw
    words by address, and every position: the library's honest table has there the position's number
    and the running committer's column.
  `EncIsHonestTab S Z cut N`: the encoder of the object over `codingCells`, whatever the three
    protocols and their provers, is that honest table.
  **`EntryAgrees S Z cut N`**: at a matrix of cells that are the casts of integers, the word that
    the library lays at (row b, entry e) with pads of 0 is given by a text without the field: the
    least residue of the integer at (e / 2^kLo, b 2^kLo + e % 2^kLo), or 0 where the matrix has no
    such cell.

Limits. Statements alone. Nothing on the out-of-domain answers, on the hash tree or on the
commitment ID. Nothing on any program: no file of a program is compared here. Nothing on soundness,
completeness or index privacy.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.CodingCells
import Johnson.Bind.Twin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.Column
open Prob Cb Cb.Ood Blocks Hiop OnBytes.Slice OnBytes.Flat Inst.Model VerifiableInference
open Iop hiding Shape
open Bind.Twin (Shape Table)

/-- The running committer's shape has the library's a, l, r and v, and the pads begin at cut: three
pads for each out-of-domain answer, at the end of a row's message. Of the shape's s no more is
asked, and of its sigma nothing. -/
structure Agree (sh : Shape) (S : Sz) (cut : ℕ) : Prop where
  a : sh.a = S.P.T.a
  l : sh.l = S.P.T.l
  r : sh.r = S.P.T.r
  v : sh.v = S.P.v
  cut : cut + 3 * sh.s = sh.l

/-- Words that are read in the field and written again come back: at a row number b that the table
has, if the list has a message's length and every word is below the prime. -/
def RowsBack (S : Sz) : Prop :=
  ∀ (msg : ℕ → List UInt64) (b : ℕ), b < 2 ^ S.P.v → (msg b).length = S.P.T.l →
    (∀ w ∈ msg b, Fmt.Fld.two.ok w = true) → rowWords S (honestMsgs S msg) b = msg b

/-- The same at any lists of words: entry j comes back as the residue of the list's member j, or of
0 where the list has none. -/
def RowsResidues (S : Sz) : Prop :=
  ∀ (msg : ℕ → List UInt64) (b : ℕ), b < 2 ^ S.P.v →
    rowWords S (honestMsgs S msg) b =
      (List.range S.P.T.l).map fun j => Bind.Twin.residue ((msg b).getD j 0)

/-- The running committer's table at a matrix of cells: the plain entries are the library's own
words at pads of 0; tails, pads and salts are raw values by address. -/
def tableOf (S : Sz) (Z : Sample GE S.En) (cut : ℕ) (N : MatrixNums)
    (M : Cells (S.toDecR Z cut) N) (tail pad : ℕ → ℕ → UInt64) (salt : ℕ → ByteArray) : Table :=
  ⟨cellEntry S Z cut N M (fun _ _ => 0), tail, pad, salt⟩

/-- The library's honest table at a matrix of cells, with the pads and the tails read in the field
off raw words: what the encoder of `codingCells` gives (`EncIsHonestTab`). -/
def honestAt (S : Sz) (Z : Sample GE S.En) (cut : ℕ) (N : MatrixNums)
    (M : Cells (S.toDecR Z cut) N) (tail pad : ℕ → ℕ → UInt64) : S.Pos → _root_.Run.PQ.SgX :=
  honestTab S
    (rowWords S (honestMsgs S (cellWords S Z cut N M fun b j => toF (pad b.val j.val))))
    (tailWords S fun b q => toF (tail b.val q.val))

/-- **The column.** At every position the library's honest table has the position's number and the
running committer's column: every row's symbol, in the order of the rows. -/
def ColumnAgrees (S : Sz) (Z : Sample GE S.En) (cut : ℕ) (N : MatrixNums) (sh : Shape) : Prop :=
  ∀ (M : Cells (S.toDecR Z cut) N) (tail pad : ℕ → ℕ → UInt64) (salt : ℕ → ByteArray) (x : S.Pos),
    honestAt S Z cut N M tail pad x =
      (x.val, Bind.Twin.columnOf sh (Bind.Twin.laid sh (tableOf S Z cut N M tail pad salt)) x.val)

/-- The encoder of the object over `codingCells` is the honest table at the words of the matrix, the
pads laid in, and the tails' words: at all three protocols and all their honest provers. -/
def EncIsHonestTab (S : Sz) (Z : Sample GE S.En) (cut : ℕ) (N : MatrixNums) : Prop :=
  ∀ (X : Type) (pp : ScalesAndPolicy) (req : X → Instance ppref)
    (F : Files (DecR.configurationOfStoredTable (claimsLedgerOnAt (S.toDecR Z cut) N pp req)
      (relationsAndEncodingOfClaims _ (codingCells S Z cut N pp req)))) (P : F.Provers)
    (M : Cells (S.toDecR Z cut) N) (r : (F.withProvers P).EncodingRandomness),
    (F.withProvers P).encodeIndex M r =
      honestTab S (rowWords S (honestMsgs S (cellWords S Z cut N M r.1))) (tailWords S r.2)

/-- **The digits.** At a matrix whose cells are the casts of the integers mat, the library's word at
(row b, entry e), pads of 0, is the least residue of the integer at
(e / 2^kLo, b 2^kLo + e % 2^kLo), or 0 where the matrix has no such cell. -/
def EntryAgrees (S : Sz) (Z : Sample GE S.En) (cut : ℕ) (N : MatrixNums) : Prop :=
  ∀ (M : Cells (S.toDecR Z cut) N) (mat : ℕ → ℕ → ℤ),
    (∀ y c, M y c = ((mat y.val c.val : ℤ) : GE)) → ∀ b e : ℕ,
    cellEntry S Z cut N M (fun _ _ => 0) b e =
      if e / 2 ^ N.kLo < N.rows ∧ b * 2 ^ N.kLo + e % 2 ^ N.kLo < 2 ^ (N.kLo + S.P.v) then
        UInt64.ofNat (mat (e / 2 ^ N.kLo) (b * 2 ^ N.kLo + e % 2 ^ N.kLo) % (Code.pGold : ℤ)).toNat
      else 0

end Bind.Column

end
