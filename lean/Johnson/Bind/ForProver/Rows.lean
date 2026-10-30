-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/Rows.lean: the rows of one committed table, for an honest prover: from the
index's matrix and that table's pads and encoding randomness, both typed in the field, to the table
that the stand-in committer on byte strings (`Bind.Twin.commitW`, Johnson/Bind/Twin.lean) encodes.
Definitions with code; no theorem.

Why. The frame for an honest prover in Lean (Johnson/Desc/ProofFile/Honest/) reads the index as a
matrix in the field, by the matrix's row and column (`ProofFile.Honest.Weights`), and a committed table's
pads and encoding randomness as pads and tails in the field (`ProofFile.Honest.TableRand`). The stand-in
committer takes a table of words, by the table's row and the place in that row. This file lays the
one into the other, so that the encoded index of that frame and the committer's are one text.

Main definitions (namespace `Bind.ForProver`).
   `entryAtF kLo rows v w b e`: the packing: entry e of the table's row b is the word of the
      matrix's entry at (e / 2^kLo, b 2^kLo + e % 2^kLo); 0 where the matrix has no such cell.
   `tableOfRand entry ρ`: the committer's table: these plain entries, ρ's tails and pads written as
      words below p. Its salts are empty strings: the encoder and the OOD answers read no salt.
   `rowMsgF sh entry ρ b e`, `rowTailF ρ b q`: a row's message and tail in the field, by the table's
      row and the place: for whoever writes a fold of the table's rows.
   `rowsFit sh kLo rows`: a test with code: a message has room for its pads (3 s ≤ l), and all rows
      of the matrix have room before the pads (rows 2^kLo ≤ l - 3 s).
Limits. Where `rowsFit` fails, rows of the matrix lie in no row of the table: `entryAtF` and
`tableOfRand` say nothing of it; a caller asks the test. Nothing is held against another text here.
The packing is held against that of the honest side of the linear claim's shared rounds (the shared
chain) (`entriesOf_eq`, Johnson/Bind/ForProver/K14Rows.lean), against the plain entries at given
weights (`entryOf_eq`, Johnson/Bind/ForProver/AtWeights.lean) and against the library's cells
(`wordsTable_eq`, Johnson/Bind/ForProver/LawsSizes.lean); at the full size's shape also against the
library's decoder, which gives the index's matrix back (`column_decodes_at`,
Johnson/Bind/ForProver/JoinsSizes.lean); `rowMsgF` and `rowTailF` against the committer's lists in
Johnson/Bind/ForProver/Laws.lean. No #guard or #eval line of this folder runs this file's
definitions. One committed table; which of the protocol's tables it is, the first or a copy, is not
said here. This file writes no honest prover. Nothing on completeness, on index privacy or on any
program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.Twin
import OnBytes.Slice.Field
import Johnson.Desc.ProofFile.Honest.ForKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes.Slice (toF ofF)
open ProofFile.Honest (TableRand Weights)
open Bind.Twin (Shape Table)

/-- **The packing.** Entry e of the table's row b: the word below p of the matrix's entry at the row
e / 2^kLo and the column b 2^kLo + e % 2^kLo; 0 where the matrix, of the given number of rows and
2^(kLo + v) columns, has no such cell. -/
def entryAtF (kLo rows v : ℕ) (w : ℕ → ℕ → Cb.Gl.F) (b e : ℕ) : UInt64 :=
  if e / 2 ^ kLo < rows ∧ b * 2 ^ kLo + e % 2 ^ kLo < 2 ^ (kLo + v) then
    ofF (w (e / 2 ^ kLo) (b * 2 ^ kLo + e % 2 ^ kLo))
  else 0

/-- The committer's table at given plain entries and the coins ρ, written as words below p. The
salts are empty strings: the encoder and the OOD answers read no salt, but a run of the stand-in
committer does (`Bind.Twin.leafAtW`, Johnson/Bind/Twin.lean, fills a salt up with zero bytes): a
root, a name or a commitment ID of this table would stand at salts of zero bytes. -/
def tableOfRand (entry : ℕ → ℕ → UInt64) (ρ : TableRand) : Table :=
  ⟨entry, fun b q => ofF (ρ.tail b q), fun b j => ofF (ρ.pad b j), fun _ => ByteArray.empty⟩

/-- Entry e of the message of the table's row b, in the field: a plain entry below l - 3 s, then the
pads up to l, 0 beyond. -/
def rowMsgF (sh : Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (b e : ℕ) : Cb.Gl.F :=
  if e < sh.plain then toF (entry b e) else if e < sh.l then ρ.pad b (e - sh.plain) else 0

/-- Entry q of the tail of the table's row b, in the field. -/
def rowTailF (ρ : TableRand) (b q : ℕ) : Cb.Gl.F := ρ.tail b q

/-- **A test with code**: a message has room for its pads, and a matrix of the given number of rows,
2^kLo columns of it in a row of the table, has room before the pads. -/
def rowsFit (sh : Shape) (kLo rows : ℕ) : Bool :=
  decide (3 * sh.s ≤ sh.l) && decide (rows * 2 ^ kLo ≤ sh.plain)

end Bind.ForProver

#print axioms Bind.ForProver.entryAtF
#print axioms Bind.ForProver.tableOfRand
#print axioms Bind.ForProver.rowMsgF
#print axioms Bind.ForProver.rowTailF
#print axioms Bind.ForProver.rowsFit
