-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/PolysAt.lean: the coefficients of the polynomials of a committed table's
rows, for an honest prover: out of a row's tail and message in the field (`rowTailF`, `rowMsgF`,
Johnson/Bind/ForProver/Rows.lean), typed as the library's link reads them. Three definitions and two
equations that hold by these definitions' text.

Why. The library's link between two committed tables speaks of a table's rows as functions from a
row (a vertex of the cube) and a coefficient's number to the extension field
(`OnBytes.Slice.honestPolys`, OnBytes/Slice/Honest.lean). This folder has a row's tail and message
by plain numbers, in the base field. Whoever holds the one against the other needs a term of the
link's type that is made of this folder's rows. Two inputs are spoken of below: the goals' (a matrix
of cells, pads and tails on finite ranges: what the library's typed encoder takes) and the frame's
(functions of two plain numbers: what the frame for an honest prover hands out).

Main definitions (namespace `Bind.ForProver`).
   `rowCoefF sh entry ρ b k`: coefficient number k of the polynomial of the table's row b: below r
      the tail's entry k, from r on the message's entry k - r. By plain numbers, in the base field.
   `polysAt S sh entry ρ`: the same at the link's types at the sizes S: by the vertex, read as its
      number (`Sz.rowNo`), and the coefficient's number below S's r + l; cast into the extension
      field.
   `qOf S cut ρ`: A DEFINITION OF THE TIE BETWEEN TWO INPUTS, in a section of its own: the frame's
      coins for a committed table, cut down to the addresses that the library's typed encoder reads
      at the sizes S: pads by row and entry below l - cut, tails by row and entry below r.
   `rowCoefF_tail`, `rowCoefF_msg`: the two branches of `rowCoefF`. They unfold the definition and
      say nothing else.
Limits. DEFINITIONS: nothing is held against another text here. `polysAt` takes the sizes S and the
shape sh apart: the branch is taken at sh's r, the type is S's; where the two numbers differ the
term is still typed and is the text of no table's rows. That they agree is a premise
(`Bind.Column.Agree`) of the laws in Johnson/Bind/ForProver/Polys.lean. From sh's r + l on
`rowCoefF` is 0, by `rowMsgF`'s text. `qOf` forgets the coins' values outside the addresses named;
no law of this file says that a prover's coins are 0 or anything else there. THAT THE HONEST
PROVER'S INPUT AT THE PROTOCOL IS MADE BY `qOf` IS SAID BY NO FILE BENEATH THIS ONE: a law that is
stated at `qOf` holds at an input that is made of the frame's by this definition, and says so. The
maps of the other direction, from the goals' input to plain readers, are those of the library's
E2E/KeyReaders.lean; the laws at them hold at every input of the goals' type
(Johnson/Bind/ForProver/PolysReaders.lean). The plain entries are a letter: that they are an index's
is not said. No term of a type of polynomials is made. One committed table; which of the protocol's
tables it is, the first or a copy, is not said here. This file writes no honest prover. Nothing on
completeness, on index privacy, on soundness or on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.Rows
import Johnson.Flat.CodingCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.ForProver
open OnBytes.Slice (Sz GF GE)
open OnBytes.Flat (PadsOf)
open ProofFile.Honest (TableRand)
open Bind.Twin (Shape)

/-- **Coefficient number k of the polynomial of the table's row b**: the tail's entries, then the
message's. ρ is any pair of plain functions: at k < sh.r it reads `ρ.tail b k`, whatever range the
maker of ρ had in mind. Where ρ is made of a typed input by readers that give 0 outside its range
(Johnson/Bind/ForProver/PolysReaders.lean), and sh.r or the row b outruns that range, A 0 STANDS FOR
A TAIL. (Nothing here ties sh to sizes; the laws that do ask `Bind.Column.Agree`,
Johnson/Bind/ColumnDefs.lean.) -/
def rowCoefF (sh : Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (b k : ℕ) : GF :=
  if k < sh.r then rowTailF ρ b k else rowMsgF sh entry ρ b (k - sh.r)

/-- **The table of coefficients at the link's types**: by the vertex, read as its number, and the
coefficient's number; cast into the extension field. -/
def polysAt (S : Sz) (sh : Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) :
    S.ix.Row → S.Co → GE :=
  fun β k => algebraMap GF GE (rowCoefF sh entry ρ (Sz.rowNo β) k.val)

/-- Below r a coefficient is the tail's entry. By the definition's text. -/
theorem rowCoefF_tail (sh : Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (b q : ℕ)
    (hq : q < sh.r) : rowCoefF sh entry ρ b q = rowTailF ρ b q :=
  if_pos hq

/-- Coefficient number r + e is the message's entry e. By the definition's text. -/
theorem rowCoefF_msg (sh : Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (b e : ℕ) :
    rowCoefF sh entry ρ b (sh.r + e) = rowMsgF sh entry ρ b e := by
  unfold rowCoefF
  rw [if_neg (Nat.not_lt.2 (Nat.le_add_right _ _)), Nat.add_sub_cancel_left]

/-! ## A definition of the tie between two inputs -/

section Tie

/-- **A DEFINITION OF THE TIE; THAT THE HONEST PROVER'S INPUT AT THE PROTOCOL IS SO MADE IS SAID BY
NO FILE BENEATH THIS ONE.** The frame's coins for a committed table (functions of two plain
numbers), cut down to the addresses that the library's typed encoder reads: the coins of the goals'
input, made of the frame's. MANY TO ONE: it drops every value outside the typed addresses. So a
statement over the typed coins says nothing of the values that are dropped, and no statement of this
file goes through it. The other map of this direction is `cellsOfF`
(Johnson/Bind/ForProver/CellsInField.lean), on the matrix. -/
def qOf (S : Sz) (cut : ℕ) (ρ : TableRand) :
    PadsOf S cut × (Fin (2 ^ S.P.v) → Fin S.P.T.r → GF) :=
  (fun b j => ρ.pad b.val j.val, fun b q => ρ.tail b.val q.val)

end Tie

end Bind.ForProver

end

#print axioms Bind.ForProver.rowCoefF_tail
#print axioms Bind.ForProver.rowCoefF_msg
#print axioms Bind.ForProver.rowCoefF
#print axioms Bind.ForProver.polysAt
#print axioms Bind.ForProver.qOf
