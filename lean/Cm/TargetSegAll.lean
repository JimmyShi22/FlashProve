-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegAll.lean: the model's conditions modulo p = 2^64 - 2^32 + 1, cut into 25 segments: what
is asked of the segments, and the one equivalence.

In standard terms: the model's system of constraints modulo p is split into 25 parts (segments),
each with its own matrix of cells, lookups and zero identities. Stated: for any 25 segments with
`SegsOK`, the whole system holds if and only if every segment's constraints hold.
Definitions and statements (`Cm.Seg.TS.Spec.cond_iff`, `Spec.equiv_of`, `Spec.equiv_to`); the
proofs are in Cm/TargetSegAllProofs.lean; the segments themselves: Cm/TargetSegModel.lean. This
file stands over the fields of Cb/Gl/GlField.lean
(`Gl.F` the integers modulo p, `Gl.E` its cubic extension), for the relation
pair of Cm/TargetPRel.lean at that p.
What a segment is: Cb/Req/ReqSpec.lean's `SegSpec`: the shape of its matrix of cells; families of
identities; families of keys with their tables; a family is a sum of terms, a term a table of
public coefficients (a function of the instance and of the vertex) times a product of atoms of
three kinds: affine in cells | linear in the index (at every point a tensor form) | the sum over
further variables of a sum of terms over atoms of the first two kinds. `S.Holds Φ x W A`: every
identity is 0 at every vertex, every key is an entry of its table.

Main names:
  `fmtRef`: the shape of the index matrix for the tensor forms: 3,076,096 rows, 2^(11 + 7) columns.
    Its field "code" is a placeholder (a toy code): a format of Cb/Gen/Tensor.lean holds a code,
    and nothing in the files Cm/TargetSeg*.lean reads it (by a search of the texts): forms, atoms
    and conditions read the number of rows and of column variables alone. The split 11 + 7 is not
    read by them either.
  `FFAt`, `AttAt`, `HeadAt`: the clauses of `Cm.TP.Cond Gl.p` that belong to one segment: keys and
    identities of the first segment of group g (all of the group's four layers but the attention
    weights (attention itself, from queries, keys and values to its output o:
    Cm/TargetSegAtt.lean): normalisations, projections, router, hidden units; in group 0 the
    embedding), of its second segment (the attention weights), of the plain head with the scaled
    table, and with the head the identity "y = 0 if e < 1,024".
  `SegsOK s seg`: what is asked of 25 segments: the shapes of the dictionary (Cm/SegLayout.lean);
    well formed; they read places that the dictionary says they read; and the assembly, twice for
    each segment: its conditions hold at the matrices of a trace T (resp. at integer matrices M),
    at the image of an integer index matrix W, if and only if the segment's clauses hold at T
    (resp. at the trace of M). No bound on cells occurs.
  `Spec.equiv_of`, `Spec.equiv_to`: the one equivalence, for all segments with `SegsOK`, every
    table s (lawful or not: `Scales.Lawful`, Cm/Rel2.lean), every request x, every integer index
    matrix W and all integer matrices M of cells (all traces T), without a bound: all conditions
    modulo p hold at (W, the trace of M) ⇔ for all 25 segments the segment's conditions hold at (x,
    W, M). An assembly: `SegsOK` holds the equivalence segment by segment, `cond_iff` splits the
    conditions, these two put them together. All content lies in "25 segments with `SegsOK` exist"
    (Cm/TargetSegModel.lean: `Cm.Seg.TS.Spec.segs_ok`); without that value the two statements could
    range over nothing.

How this renders a write-up of ours (lean/CREDITS.md). There a model supplies one partition
of its conditions into segments and one equivalence: whatever request, reply, index and cells are,
index and cells
meet the constraints if and only if for all segments the zero predicate of its summands and the
lookup predicate of its keys hold. `equiv_of` is that sentence. As there: the identity on y is an
identity of the last segment (a term without atoms, whose coefficient reads the request), so a
zerocheck checks it and nothing of it is left to a test (this is so of the model's own last
segment: `idY`, `segHeadY`, Cm/TargetSegHeadY.lean; for any 25 segments with `SegsOK` this file
says of y only that the last one's conditions are `HeadAt`, which has the clause on y); index and
cells are integer matrices, read by their residues; a segment has several summands and key maps
(gluing them is the model's matter: Cb/Req/ReqGlue.lean, generic). (r < e is no condition: it is
the form of a request, a clause of both relations here, a check of the verifier there.)

Limits: declared differences. (1) A cell atom is, at each vertex, an arbitrary affine form in any
places of this or of earlier segments (Cb/Req/ReqSpec.lean: `CForm`). The write-up's cell
map is the extension of a constant and a fixed public combination over the parts of one matrix, row
bits
and column bits being variables: that structure makes a claim at a point a partial evaluation
(weights on rows, a point on columns): one pair (matrix, point) in the list of reads. So a builder
of a request gets no list of reads from these data: the model's forms have to be shown to have that
structure, or the reads' weights given otherwise. (2) One matrix of 2^rowsLog rows a segment, where
the write-up has a tuple of matrices with parts, laid block-diagonally and filled up to the
packing factor: it moves the range check's count and the packing; it has not been compared with
Cm/SegLayout.lean. (3) That the verifier can evaluate the coefficients fast is not rendered.
This file does not say that segments with `SegsOK` exist (Cm/TargetSegModel.lean). Nothing on
protocols, on the top record that a request's builder will take, on kept rows (which earlier
matrices this or a later segment still reads: Cm/SegLayout.lean: `kept`, `reads`). Owed
to a builder beside the equivalence: the degree bound and the numbers of variables, atoms and sums;
that the coefficients of the segments before the last do not read the reply y (by type a coefficient
reads the whole instance); that the index atoms are tensor forms at the column split of the encoded
index (the split is not read here; the test for linear constraints reads it). This file does not say
which list of conditions this is: the head of Cm/TargetPRel.lean.
Of the model's own segments `segM s k` (Cm/TargetSegModel.lean), and of these alone, other files
state a part of what is owed. Before gluing, `segM_nums` (Cm/TargetPartNumSeg.lean) has upper
bounds on atoms in a term, a family's variables (`Fam.v`), families and tables; it has nothing on
the numbers of sums, nor on the further variables of the sum atoms.

`Spec.no_reply` (Cm/TargetSegNoReply.lean): for
k < 24 all coefficient tables of `segM s k` are the same at two requests with the same prompt; that
file's head says that the other half of what the reply's round needs is owed.
This file does not say that the glued segments are well formed at the partition's own format
(`LdPartD.fmt`, Cb/Part/LdPartDef.lean).

Terms: lean/GLOSSARY.md.
The notions follow the worked example named in lean/CREDITS.md; the text is this library's.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cm.TargetPRel
import Cm.SegLayoutPlain
import Cb.Req.ReqSpec
import Cb.GlVal.GlToyBase

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS

open Cb Inst.Model
open Inst.Model.Layout (kRef hRef)

/-- the shape of the index matrix; the code is a placeholder that nothing in the files
Cm/TargetSeg*.lean reads (by a search of the texts) -/
def fmtRef : IdxFmt Gl.F := ⟨Gl.C8, hRef, 11, 7⟩

end Cm.Seg.TS

namespace Cm.Seg.TS
open Cb Inst.Model Inst.Model.All
open Inst.Model.Layout (kRef hRef)

/-! ## The clauses of one segment -/

/-- keys and identities of the first segment of group g -/
def FFAt (s : Scales) (g : ℕ) (W : Mat) (x : Instance ppref) (T : Trace) : Prop :=
  (∀ k, (TP.segFF Gl.p s.kap s.nf g).key
      (tokOf x.prompt) (TP.castW Gl.p W) (fun c => T.vFF g c.val) k ∈
    (TP.segFF Gl.p s.kap s.nf g).table k) ∧
  ∀ j, (TP.segFF Gl.p s.kap s.nf g).idn
      (tokOf x.prompt) (TP.castW Gl.p W) (fun c => T.vFF g c.val) j = 0

/-- keys and identities of the second segment of group g: the attention weights -/
def AttAt (s : Scales) (g : ℕ) (T : Trace) : Prop :=
  (∀ (c : Fin 4) (X : ℕ), X < (DAK s.kap g).used c →
    AttSeg.keyVec (scl := SFK s.kap s.nf g) (DAK s.kap g) tbRef
        (AttSeg.castT (T.vAtt g) : AttSeg.Raw → Gl.F) c X ∈
      AttSeg.lutSet (AttSeg.lut (scl := SFK s.kap s.nf g) (DAK s.kap g) tbRef c)) ∧
  ∀ j : AttSeg.Idn, j.Valid (DAK s.kap g) →
    AttSeg.idnVal (DAK s.kap g) (AttSeg.castT (T.vAtt g) : AttSeg.Raw → Gl.F) j = 0

/-- keys and identities of the plain head with the scaled table, and the identity on y -/
def HeadAt (s : Scales) (W : Mat) (x : Instance ppref) (T : Trace) : Prop :=
  (∀ f a i, a < Plain.len f → i < Head.nT →
    Head.InLut (Plain.TP.tableOf f)
      (Plain.TP.key s.nf (T.vHead.cast Gl.F) (TP.castH Gl.p W) (reqOf x) f a i)) ∧
  (∀ i < Head.nT, ∀ k < 17, Plain.idn s.nf (T.vHead.cast Gl.F) i k = 0) ∧
  (x.e < ppref.T → ((x.y.val : ℕ) : ZMod Gl.p) = 0)

/-- integer matrices in Gl.E -/
abbrev cM (M : ℕ → ℕ → ℕ → ℤ) : ℕ → ℕ → ℕ → Gl.E := fun a r c => ((M a r c : ℤ) : Gl.E)

/-- What is asked of the 25 segments. -/
structure SegsOK (s : Scales) (seg : ℕ → SegSpec (Instance ppref) Gl.F Gl.E) : Prop where
  rows   : ∀ k < nSeg, (seg k).rowsLog = rowsLog k
  cols   : ∀ k < nSeg, (seg k).cols = cols k
  wf     : ∀ k < nSeg, (seg k).WF fmtRef
  places : ∀ k < nSeg, ∀ q ∈ (seg k).places, q ∈ reads Hd.plain k
  ffTo   : ∀ g < nGr, ∀ (x : Instance ppref) (T : Trace) (W : Mat),
    (seg (2 * g)).Holds fmtRef x (TP.castW Gl.p W) (cM (toMat Hd.plain T)) ↔ FFAt s g W x T
  ffOf   : ∀ g < nGr, ∀ (x : Instance ppref) (M : ℕ → ℕ → ℕ → ℤ) (W : Mat),
    (seg (2 * g)).Holds fmtRef x (TP.castW Gl.p W) (cM M) ↔ FFAt s g W x (ofMat Hd.plain M)
  attTo  : ∀ g < nGr, ∀ (x : Instance ppref) (T : Trace) (W : Mat),
    (seg (2 * g + 1)).Holds fmtRef x (TP.castW Gl.p W) (cM (toMat Hd.plain T)) ↔ AttAt s g T
  attOf  : ∀ g < nGr, ∀ (x : Instance ppref) (M : ℕ → ℕ → ℕ → ℤ) (W : Mat),
    (seg (2 * g + 1)).Holds fmtRef x (TP.castW Gl.p W) (cM M) ↔ AttAt s g (ofMat Hd.plain M)
  headTo : ∀ (x : Instance ppref) (T : Trace) (W : Mat),
    (seg 24).Holds fmtRef x (TP.castW Gl.p W) (cM (toMat Hd.plain T)) ↔ HeadAt s W x T
  headOf : ∀ (x : Instance ppref) (M : ℕ → ℕ → ℕ → ℤ) (W : Mat),
    (seg 24).Holds fmtRef x (TP.castW Gl.p W) (cM M) ↔ HeadAt s W x (ofMat Hd.plain M)

end Cm.Seg.TS

namespace Cm.Seg.TS.Spec
open Cb Inst.Model Inst.Model.All

/-- the conditions modulo p are the clauses of the 25 segments -/
def cond_iff : Prop :=
  ∀ (s : Scales) (W : Mat) (x : Instance ppref) (T : Trace),
    TP.Cond Gl.p s W x T ↔ (∀ g < nGr, FFAt s g W x T) ∧ (∀ g < nGr, AttAt s g T) ∧ HeadAt s W x T

/-- The one equivalence, for all segments with `SegsOK s seg`, at integer matrices of cells. -/
def equiv_of : Prop :=
  ∀ (s : Scales) (seg : ℕ → SegSpec (Instance ppref) Gl.F Gl.E), SegsOK s seg →
    ∀ (W : Mat) (x : Instance ppref) (M : ℕ → ℕ → ℕ → ℤ),
      TP.Cond Gl.p s W x (ofMat Hd.plain M) ↔
      ∀ k < nSeg, (seg k).Holds fmtRef x (TP.castW Gl.p W) (cM M)

/-- The same at the matrices of a trace. -/
def equiv_to : Prop :=
  ∀ (s : Scales) (seg : ℕ → SegSpec (Instance ppref) Gl.F Gl.E), SegsOK s seg →
    ∀ (W : Mat) (x : Instance ppref) (T : Trace),
      TP.Cond Gl.p s W x T ↔
      ∀ k < nSeg, (seg k).Holds fmtRef x (TP.castW Gl.p W) (cM (toMat Hd.plain T))

end Cm.Seg.TS.Spec
