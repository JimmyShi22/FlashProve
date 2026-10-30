-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartDef.lean: a partition of a model's conditions into segments, over a
configuration `LdCf` (Cb/Obj/LdObjectConf.lean): the data and the laws.

In standard terms: an arithmetisation of the model's pair of relations. Each segment has a matrix of
integer cells, identities that must vanish at every vertex, and keys that must lie in tables
(`SegSpec.Holds`). Definitions only. It is what the builder of a request (Cb/Part/LdPart*.lean)
takes from a model.


Main names:
  `LdPartD Cf`: the data.
    h, klo: the index matrix has h rows and 2^(Cf.v + klo) columns (Cf.v column variables name a
      row of the encoded index, klo a place inside it).
    lay: where entry (y, place inside a row) is in the layout of a row of the encoded index.
    n segments, seg k : `SegSpec` (Cb/Req/ReqSpec.lean: shape of its matrix of cells; families of
      identities; families of keys with tables).
    form: the form of a request (a test of the instance). req: the instance without the reply.
    matI: the matrix of an index.
    toMat, ofMat: the dictionary between the model's cells and integer matrices (segment, row,
      column).
    kept k: the rows (segment, row) that are handed on after segment k.
    B, D: the bound on honest cells, the window: the relaxed bound is 2 D.
  `P.InShape`, `P.Below`, `P.Cond x W A`: a place lies in its segment's matrix; all entries in the
    shapes are below a bound in absolute value; all segments' conditions hold.
  `P.matB a`: the matrix that is read off the body of a message of the encoded index: entry (y, c)
    is in the row named by the leading Cf.v bits of c, at the layout's place lay (y, the klo last
    bits of c).
  `Term.SameAt`, `Atom.SameAt`, `Fam.SameAt`, `SegSpec.SameAt` x x': all coefficient tables, also
    under inner sums, are the same at two instances.
  `P.Props p`: the laws.
    pos: there is a segment. formY: a witness's request has the form.
    admit: a witness of the relation gives matrices below B in absolute value that meet all
      segments' conditions at the index's matrix. force: a request of the form, matrices below 2 D
      in absolute value that meet all segments' conditions at the matrix of the index i: a witness
      of the relaxed relation (`Cf.Rno`) for i. (Two consequences of the one equivalence of a
      write-up of ours (lean/CREDITS.md), which has no bound and goes both ways at all
      cells: what completeness and knowledge soundness use of it; weaker as a duty)
    ofMat_congr: ofMat reads inside the shapes. wf: well formed. reads, keeps, keptIn, keptStep:
      see the fields below.
    reply: the coefficient tables of all segments but the last are the same at two instances with
      the same request.
    idx: the matrix read off a body that holds the index i is i's.
    char: the characteristic. one_le, le_D: 1 ≤ B ≤ D. small: 4 D < p.

Limits:
In this record "form" is a
predicate, and nothing else of the instance is tested outside the segments (the identity on the
reply is the last segment's); cells are read back by the range check's unpacking; the matrix
is read off by the layout (`matB`), so that a quantity is described
once.
What the write-up uses of a partition and this record lacks (by reading, not machine-checked). The
degree bound (with the numbers). The form of a cell map, from which the list of reads comes: here
the builder takes readings as further data (Cb/Part/LdPartRead.lean: every cell atom all of whose
places lie in the shapes (`P.InShape`) has one). Which segments read the index: computable from the
atoms; a definition, no law. Whole matrices are kept there, rows here. The packing factor: "small :
4 D < p" is the unpacking's condition at packing factor 1 only; at factor P with radix ϱ it is
Cb/Ld/LdRngAlg.lean's `Uniq`, asked with the public parameters. "lay" is not asked injective (the
clause idx then binds the index set).
Four small departures more, and one thing to know (against the write-up, by reading, not
machine-checked; all are widenings or ways of writing). (a) There a segment has a tuple of
matrices, read as one with the members along the diagonal, padded; here one matrix of 2^rowsLog
rows: toMat, ofMat are free letters, so this is a way of writing. (b) A cell atom here is, at each
vertex, any affine form in any places of any segment up to its own, with coefficients in E that may
change with the vertex; there a cell map reads one matrix, with public integers that do not depend
on the vertex: here much wider. (c) kept may hold more than is read later. (d) The words admit,
force: there they are properties of the conditions against the model's greedy reply, the second is
stated over the integers, and a lemma with a bound on the conditions' size shows that conditions
which hold modulo the field's size hold over the integers; here they are the two implications
between a pair of relations and the conditions: where the pair is the model's own, force contains
that lemma (no wrap-around). To know: the law idx is an equation of functions on all of ℕ × ℕ, and
`matB` is 0 outside h rows and 2^(v + klo) columns: so idx also asks that matI i vanishes there, for
every index i that a body holds.
This file gives no instance of the records that it defines. That a partition with these laws exists
is not shown here. Elsewhere:
the model's partition: Cm/TargetPart.lean:
`targetPart`. (The integer model is that of Cm/TargetSegModel.lean, which has admit, force, wf,
reads, reply (reply: Cm/TargetSegNoReply.lean) as statements (proofs: Cm/TargetSegModelProofs.lean,
Cm/TargetSegNoReplyProofs.lean) and needs a configuration whose encoded index has room for its
matrix).
This file says nothing on degrees. This file gives no value of any parameter of the protocol. It
does not say that the honest trace's matrices before the last segment do not depend on the reply. It
says nothing on protocols.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Req.ReqSpec
import Cb.Obj.LdObjectConf

set_option autoImplicit false

namespace Cb

open Blocks Finset

/-! ## The same coefficient tables at two instances -/

section Same
variable {X F E : Type}

def Term.SameAt (t : Term X E) (x x' : X) : Prop := ∀ b, t.coef x b = t.coef x' b

def Atom.SameAt (a : Atom X E) (x x' : X) : Prop :=
  match a with
  | .base _ => True
  | .sum _ P => ∀ t ∈ P.terms, t.SameAt x x'

def Fam.SameAt (f : Fam X E) (x x' : X) : Prop :=
  (∀ t ∈ f.terms, t.SameAt x x') ∧ ∀ j < f.na, (f.atom j).SameAt x x'

/-- all coefficient tables of the segment are the same at x and x' -/
def SegSpec.SameAt (S : SegSpec X F E) (x x' : X) : Prop :=
  (∀ f ∈ S.idn, f.SameAt x x') ∧ ∀ k ∈ S.keys, k.1.SameAt x x'

end Same

/-- A partition over the target's configuration: the data. -/
structure LdPartD {F E : Type} [Field F] [Field E] [Algebra F E] (Cf : LdCf F E) where
  h     : ℕ
  klo   : ℕ
  lay   : Fin h × (Fin klo → Bool) → Cf.Lay
  n     : ℕ
  seg   : ℕ → SegSpec Cf.Xm F E
  form  : Cf.Xm → Prop
  Xr    : Type
  req   : Cf.Xm → Xr
  matI  : Cf.I → ℕ → ℕ → F
  toMat : Cf.Cells → ℕ → ℕ → ℕ → ℤ
  ofMat : (ℕ → ℕ → ℕ → ℤ) → Cf.Cells
  kept  : ℕ → Finset (ℕ × ℕ)
  B     : ℤ
  D     : ℤ

namespace LdPartD
variable {F E : Type} [Field F] [Field E] [Algebra F E] {Cf : LdCf F E} (P : LdPartD Cf)

/-- the format for the tensor forms -/
def fmt : IdxFmt F := ⟨Cf.C₀, P.h, Cf.v, P.klo⟩

def InShape (q : Place) : Prop :=
  q.1 < P.n ∧ q.2.1 < 2 ^ (P.seg q.1).rowsLog ∧ q.2.2 < (P.seg q.1).cols

def Below (B : ℤ) (M : ℕ → ℕ → ℕ → ℤ) : Prop := ∀ q : Place, P.InShape q → |M q.1 q.2.1 q.2.2| < B

/-- integer matrices, read in E -/
def castM (M : ℕ → ℕ → ℕ → ℤ) : ℕ → ℕ → ℕ → E := fun s r c => (M s r c : E)

/-- All segments' conditions hold. -/
def Cond (x : Cf.Xm) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) : Prop :=
  ∀ s < P.n, (P.seg s).Holds P.fmt x W A

/-- the matrix that is read off the body of a message of the encoded index; 0 outside h rows and
2^(v + klo) columns -/
def matB (a : (Fin Cf.v → Bool) × Cf.J₀ → F) : ℕ → ℕ → F := fun y c =>
  if hy : y < P.h then
    (if c < 2 ^ (Cf.v + P.klo) then
        a (Alg.bits Cf.v (c / 2 ^ P.klo), Cf.lay (P.lay (⟨y, hy⟩, Alg.bits P.klo (c % 2 ^ P.klo))))
      else 0)
  else 0

/-- The laws of a partition; p is the characteristic. -/
structure Props (p : ℕ) : Prop where
  pos    : 0 < P.n
  formY  : ∀ i x c, Cf.Ryes i x c → P.form x
  admit  : ∀ i x c,
    Cf.Ryes i x c → P.Below P.B (P.toMat c) ∧ P.Cond x (P.matI i) (castM (E := E) (P.toMat c))
  force  : ∀ i x M,
    P.form x → P.Below (2 * P.D) M → P.Cond x (P.matI i) (castM (E := E) M) → Cf.Rno i x (P.ofMat M)
  ofMat_congr : ∀ M M',
    (∀ q : Place, P.InShape q → M q.1 q.2.1 q.2.2 = M' q.1 q.2.1 q.2.2) → P.ofMat M = P.ofMat M'
  wf     : ∀ s < P.n, (P.seg s).WF P.fmt
  reads  : ∀ s < P.n, ∀ q ∈ (P.seg s).places, q.1 ≤ s ∧ P.InShape q
  keeps  : ∀ s < P.n, ∀ q ∈ (P.seg s).places, ∀ k, q.1 ≤ k → k < s → (q.1, q.2.1) ∈ P.kept k
  keptIn : ∀ k, ∀ q ∈ P.kept k, q.1 ≤ k ∧ q.1 < P.n ∧ q.2 < 2 ^ (P.seg q.1).rowsLog
  keptStep : ∀ k, ∀ q ∈ P.kept (k + 1), q.1 = k + 1 ∨ q ∈ P.kept k
  reply  : ∀ k, k + 1 < P.n → ∀ x x', P.req x = P.req x' → (P.seg k).SameAt x x'
  idx    : ∀ a i, Cf.heldB a = some i → P.matB a = P.matI i
  char   : CharP F p
  one_le : 1 ≤ P.B
  le_D   : P.B ≤ P.D
  small  : 4 * P.D < p

end LdPartD

end Cb
