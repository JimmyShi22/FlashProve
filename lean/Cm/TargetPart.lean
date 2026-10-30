-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetPart.lean: the constraint system of the integer model, cut into 25 segments. It is a
partition over a configuration (Cb/Part/LdPartDef.lean: `LdPartD`), over p =
2^64 - 2^32 + 1.

Definitions. That the partition has its laws (`LdPartD.Props`) is not proved in this library.
A partition (`LdPartD`) holds a model's conditions cut into segments; its laws are `LdPartD.Props`.
What is put together: the relation pair at the field's own prime in a configuration
(Cm/TargetPLangs.lean: `targetCfP`); the 25 segments over Gl.F, Gl.E with the one equivalence
(Cm/TargetSegModel.lean: `segM`, `model_admit`, `model_force`); the dictionary between cells and
integer matrices, the shapes, what each segment reads, the kept rows (Cm/SegLayout.lean:
field-free); "no coefficient before the last segment reads the reply" (Cm/TargetSegNoReply.lean);
gluing (Cb/Req/ReqGlue.lean).

Main names:
  `TargetRoom`: Cf₀: any data of a configuration over Gl.F, Gl.E (its model is thrown away); klo: of
    the 18 column variables of the index matrix the last klo name a place inside a row of the
    encoded index, the first Cf₀.v the row; lay: where entry (row y of the matrix, place inside a
    row) stands in the layout of a row of the encoded index; pl: the placing of the index's entries.
  `TargetRoom.Fits`: sum: Cf₀.v + klo = 18; law: the placing is by column blocks: the entry (y, c)
    of an index stands in the row named by the leading Cf₀.v bits of c, at the layout's place lay
    (y, the last klo bits of c): as `matB` (Cb/Part/LdPartDef.lean) reads it.
  `targetPart R s : LdPartD (R.cf s)`: h := 3,076,096; n := 25; seg k := (segM s k).glued: one
    family of identities, one family of keys for each table; form: r < e; the request without the
    reply: (prompt, r, e); matI i := i's matrix modulo p; B := 129, D := 2^17 (the larger bound, 2 D
    in the clause force: 2^18).











Why: pl is a field with a law (`TargetRoom.Fits`: law), not computed, so that the partition can
stand over the very term of a configuration that is given with its own placing.
How the format is crossed: the segments' statements stand at `Cm.Seg.TS.fmtRef` (a placeholder code;
the split 11 + 7). A partition's format is (the configuration's code, h, Cf₀.v, klo). Conditions and
well-formedness read of a format the number of rows and the sum of the two numbers of column
variables alone: Cb/Part/LdPartIdxFmt.lean.

How this stands to a write-up of ours (lean/CREDITS.md; by reading, on these statements):
towards; the letters are the write-up's, number for number: rows and columns of the index
matrix (its reference split:
11 + 7, one value of R.Fits), the placing by column blocks, 25 segments, the honest bound 129, the
digit range 2^17, the larger bound 2^18, at most 7,200 columns; (prompt, r, e) is its request, the
reply one token, r < e (with e at most the number of tokens by type) its test of the form.

Limits: declared differences and what is owed (the same reading) (by a reading).
  (1) Shapes. Here one matrix a segment with 2^19 | 2^18 | 2^19 rows in the three kinds (slots of
    65,536 rows; a segment's own cells only: an earlier matrix that it reads is read at the earlier
    segment's number); the write-up's figures for rows are smaller (no padding to a power of
    two)
    and count the earlier matrices that a segment reads too: the two counts are not of the same
    thing. Lean's columns: 5,990 | 7,200 | 4,816 (Cm/SegLayout.lean).
    Held against a print of the write-up, by
    reading:
    the two counts of rows differ as said here: own and borrowed
    matrices without padding there; own only, in slots, padded, here. Of the columns the first two
    agree; the head's does not: there the head's large matrix is about half as wide: Lean's has
    Inst/Model/Head/Index.lean's shape, with room for an array that the plain head does not have,
    and about half of it is zero. It enters every count of the range check.
  (2) One matrix with slots, where the write-up has a tuple of matrices (rows = bits ×
      parts),
    laid along the diagonal, each in a message of its own. With it: the kept rows are sets of rows
    (slots), not whole matrices.
  (3) A true crossing: behind an odd segment k the kept rows are a slot of segment k - 1: rows
    written two segments before their next reader cross every attention segment. So a builder's
    shortcut "every kept matrix stands in every later body" costs at 12 segments here.
  (4) admit and force are two consequences of the write-up's one equivalence, each with its
    bound, and they speak of the list of conditions. That the list admits and forces the greedy
    reply is another theorem: Cm/TargetPRel.lean (forces, trace_iff: lawful tables).
  (5) The cell atoms: Cb/Req/ReqSpec.lean allows any affine form at each vertex; the
      write-up's
    cell map is one matrix with row bits and column bits as variables and fixed coefficients on
    parts. Whether every atom of the 25 glued segments has that form is shown nowhere: owed.
  (6) Not in Props, and used by the write-up's theorem: the degree bound; the packing; which 13
    segments read the index.


  (7) Gluing adds selector variables and raises degrees (no atom is added to a term:
    `Spec.degLe_glue`, Cb/Req/ReqNumsGlue.lean; but every member is then summed at the largest of
    the members' degrees): the numbers of variables of the glued segments, by size of table, and how
    many families of keys they have: Cm/TargetPartNumKeys.lean; the numbers of inner sums are stated
    nowhere.




This file does not say that R with `R.Fits` exist.
This file
does not say which list of conditions this is, and what of it has been held, by reading, against the
write-up: the heads of Cm/TargetPRel.lean, Cm/TargetSegAll.lean. At an unlawful table admit
may hold for want of a witness. Nothing on protocols.
The notions follow the worked example named in lean/CREDITS.md; the text is this library's.
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cm.TargetSegModel
import Cm.TargetSegNoReply
import Cm.TargetPLangs
import Cb.Part.LdPartCf
import Cb.Req.ReqGlue
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm

open Inst.Model Inst.Model.All Iop Prob Hiop Cb Cm.Seg
open Inst.Model.Layout (kRef hRef)

/-- The code's side with room for the index matrix: the fields. -/
structure TargetRoom : Type 1 where
  Cf₀ : LdCf Gl.F Gl.E
  klo : ℕ
  lay : Fin hRef × (Fin klo → Bool) → Cf₀.Lay
  pl  : TargetEnt → Cf₀.Row × Cf₀.Lay

namespace TargetRoom
variable (R : TargetRoom)

/-- What is asked of the fields. -/
structure Fits : Prop where
  sum : R.Cf₀.v + R.klo = kRef
  law : ∀ q : TargetEnt, R.pl q =
    (Alg.bits R.Cf₀.v (q.2.val / 2 ^ R.klo), R.lay (q.1, Alg.bits R.klo (q.2.val % 2 ^ R.klo)))

/-- The configuration. -/
@[reducible] def cf (s : Scales) : LdCf Gl.F Gl.E := targetCfP R.Cf₀ R.pl Gl.p s

end TargetRoom

/-- The partition of the model. -/
def targetPart (R : TargetRoom) (s : Scales) : LdPartD (R.cf s) where
  h := hRef
  klo := R.klo
  lay := R.lay
  n := nSeg
  seg := fun k => (TS.segM s k).glued
  form := fun x : Instance ppref => x.r < x.e
  Xr := (Fin ppref.T → Fin ppref.V) × Fin (ppref.T + 1) × Fin (ppref.T + 1)
  req := fun x : Instance ppref => (x.prompt, x.rF, x.eF)
  matI := fun i : Idx => TP.castW Gl.p i.mat
  toMat := toMat Hd.plain
  ofMat := ofMat Hd.plain
  kept := kept
  B := 129
  D := 2 ^ 17

end Cm
