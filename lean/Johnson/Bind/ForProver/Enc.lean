-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/Enc.lean: the encoded index's column at a position, for an honest prover: the
column of the stand-in committer on byte strings (`Bind.Twin.columnOf`, the encoder of
`Bind.Twin.commitW`, Johnson/Bind/Twin.lean), read in the field. Definitions with code; no theorem.

Main definitions (namespace `Bind.ForProver`).
   `encAt sh entry ρ x`: general in the shape: at a position x below 2^a the committer's column at
      the table `tableOfRand entry ρ` (Johnson/Bind/ForProver/Rows.lean), each word read in the
      field; nothing from 2^a on.
   `shapeOfIndex`, `linOf`, `shapeOf`: the committer's shape off the public part (`ProofFile.Pub`,
      Johnson/Desc/ProofFile/Pub.lean): the six numbers of the planner's shape of the committed
      table, on the road Z.p.chains.made.sized.proof.batch.shape, by which the own parameters of the
      linear claim's shared rounds (the shared chain) are made (`Desc.K14.p14Of`,
      Johnson/Desc/K14/Blocks.lean). Depth, width and salt are held by place against the library's
      own field names: `declared_shape` (Johnson/Bind/ForProver/Declared.lean).
   `entryOfPub Z w`: the plain entries off a public part: the packing of the index w.
   `encW Z w rc item x`: the index as a matrix in the field (`ProofFile.Honest.Weights`): `encAt` at the
      shape off Z, the packing of w and the coins of the item 0 (it reads rc 0). It gives nothing at
      every item but 0, from 2^a on, and at every position where the test `rowsFit` fails.
   `enc Z i rc item x`: the index as `Cm.Idx`: `encW` at the casts of the matrix's integers.
      `encW` at the reader `OnBytes.HonestTrace.entryOf i` is `encIdx`; that this is `enc`:
      `encIdx_eq_enc`, Johnson/Bind/ForProver/AtIndex.lean.
Limits. `encAt` lays all rows' lists anew at every call: it is the form of which theorems speak, not
a form for a program at a large shape. `rowsFit` asks for room alone. It is not the
verifier's test on the shape (`OnBytes.Params.LinShape.ok`): `encW` gives columns at shapes that
this test rejects, among them l + r > 2^a, where the encoded table does not fix the rows. That test
admits 32 < a ≤ 60 (`OnBytes.Code.ok`, OnBytes/Iop/Ground.lean); there positions of the stand-in
committer share points (Johnson/Bind/Twin.lean) and `encW` is not the format's code: whoever needs
that asks a ≤ 32 besides (at files in scope: `a_inScope`, Johnson/Bind/ForProver/ShapeInScope.lean).
`enc` means something at the full size's shape alone: `Cm.Idx` is typed at the reference sizes, and
at a public part of another size `enc` encodes a cut or a padding of such a matrix. Where the maker
of the public part returns, in the goals' scope `rowsFit` passes and the shape is the full size's
(`rowsFit_inScope`, `shapeOf_inScope`, Johnson/Bind/ForProver/ShapeInScope.lean); at other files no
theorem here says the first (by reading, `made_parts`, `sized_tests`, `linOk_ok`, `rowsFit_of_ok`
give it); that it returns the side library proves at the library's written copies of the two stored
sets, in scope (AtFullSide/E2E/StartAtWrittenFiles.lean), and Johnson/Second/Seam/SeatFacts.lean
evaluates at its written copies of the small stored example's files, which are out of scope; this
file, which has no theorem, says of no files that it returns. One committed table; which of the
protocol's tables it is, the first or a copy, is not said here. WHICH ITEM. READ, NOT PROVED: a
statement's items are numbered file by file. At the link the item 0 holds the first table and the
item 1 the copy (`OnBytes.linkStepsVerify`, OnBytes/Iop/Link.lean); in a proof file's shared chain
the item 0 holds its one table (`Desc.K14.p14Of`, Johnson/Desc/K14/Blocks.lean), which in the
library's typed schemes that are cited here is a copy (`allY`, Johnson/Prover/All/Defs.lean;
`proveAt`, Johnson/WholeKey/Defs.lean). `encW` reads rc 0 and answers at the item 0 alone, and so do
`oodSh` and its key (Johnson/Bind/ForProver/Ood.lean): in that numbering they are a session's text.
Over coins by item in the link's numbering they would give the first table's columns and OOD sample,
and nothing for the copy. That the shared chain of the description that `ProofFile.onlineDescription` returns holds
the eight blocks of `p14Of` at the planner's chains and the list `beforePointOf N`, each under one
wrapper (`retype`), is the library's `Desc.K14.Law.k14_sits` (Johnson/Desc/K14/Law/K14Sits.lean),
under the premise that these blocks are made; this file, which has no theorem, does not use it. This
file writes no honest prover. Nothing on completeness, on index privacy or on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.Rows
import Johnson.Desc.ProofFile.Pub
import Cm.RelBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes.Slice (toF ofF)
open ProofFile.Honest (TableRand Weights)
open Bind.Twin (Shape Table)

/-- **The encoded index's column at the position x**, general in the shape: the column of the
committer on bytes, read in the field; nothing from 2^a on. At every shape it gives a column at
every position below 2^a; at sh.r = 0 no tail is laid. -/
def encAt (sh : Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (x : ℕ) :
    Option (List Cb.Gl.F) :=
  if x < 2 ^ sh.a then
    some ((Bind.Twin.columnOf sh (Bind.Twin.laid sh (tableOfRand entry ρ)) x).map toF)
  else none

/-- The committer's shape of the verifier's shape of a committed table: the same six numbers. -/
def shapeOfIndex (s : OnBytes.Params.IndexShape) : Shape :=
  ⟨s.code.logN, s.code.ell, s.code.r, s.v, s.answers, s.saltBytes⟩

/-- The planner's shape of the proof file's batch, off the public part. -/
def linOf (Z : ProofFile.Pub) : OnBytes.Params.LinShape := Z.p.chains.made.sized.proof.batch.shape

/-- The committer's shape, off the public part. -/
def shapeOf (Z : ProofFile.Pub) : Shape := shapeOfIndex (linOf Z).fold.index

/-- **The encoded index's column, the index as a matrix in the field**: by the statement's item and
the position. Nothing at every item but 0, from 2^a on, and where `rowsFit` fails. Items are
numbered file by file: this is the item 0 of a side that holds one committed table; over coins by
item in a link's numbering it speaks of the link's first table and gives nothing for the second (the
head's Limits, "Which item"). -/
def encW (Z : ProofFile.Pub) (w : Weights) (rc : ℕ → TableRand) (item x : ℕ) : Option (List Cb.Gl.F) :=
  if item = 0 ∧ rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows = true then
    encAt (shapeOf Z) (entryAtF (linOf Z).kLo (linOf Z).matrixRows (shapeOf Z).v w.entry) (rc 0) x
  else none

/-- The plain entries off a public part: the packing of the index, as `encW` lays it. -/
def entryOfPub (Z : ProofFile.Pub) (w : Weights) : ℕ → ℕ → UInt64 :=
  entryAtF (linOf Z).kLo (linOf Z).matrixRows (shapeOf Z).v w.entry

/-- **The encoded index's column, the index as a well-formed matrix of digits.** -/
def enc (Z : ProofFile.Pub) (i : Cm.Idx) : (ℕ → TableRand) → ℕ → ℕ → Option (List Cb.Gl.F) :=
  encW Z ⟨fun y c => ((i.mat y c : ℤ) : Cb.Gl.F)⟩

end Bind.ForProver

#print axioms Bind.ForProver.encAt
#print axioms Bind.ForProver.shapeOfIndex
#print axioms Bind.ForProver.linOf
#print axioms Bind.ForProver.shapeOf
#print axioms Bind.ForProver.encW
#print axioms Bind.ForProver.entryOfPub
#print axioms Bind.ForProver.enc
