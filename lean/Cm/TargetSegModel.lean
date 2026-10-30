-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegModel.lean: the 25 segments of the integer model over p = 2^64 - 2^32 + 1, as a
definition; the one equivalence at it, with no hypothesis left (Cm/TargetSegAll.lean's `SegsOK`
holds at it: `Spec.segs_ok`); "admit" and "force", in the sense of Cb/Req/ReqSpec.lean, in terms of
the segments.

In standard terms: the 25 parts of the model's system of constraints are defined outright, and it
is stated that together they are equivalent to the whole system, and what that yields for the
relation and its relaxation.
One definition and statements (`Cm.Seg.TS.Spec.segs_ok` and the like); the proofs are in
Cm/TargetSegModelProofs.lean. It is the model's side of what a request's builder takes
(Cm/TargetPart.lean: `targetPart R s`: seg k := (segM s k).glued): the data of a partition (the
segments; the dictionary `toMat`, `ofMat`, the shapes, reads and kept rows of Cm/SegLayout.lean;
the bounds 129 and 2^18) at the field `Gl.F`, with the equivalence
proved.

Main names:
  `segM s k`: segment k of the model at the table s of scales, over `Gl.F`, `Gl.E`
    (Cb/Req/ReqSpec.lean: `SegSpec`): for even k < 24 the first segment of group k / 2
    (Cm/TargetSegFFAll.lean: all of the group's four layers but the attention weights (attention
    itself, from queries, keys and values to its output o: Cm/TargetSegAtt.lean); 34 families of
    keys, among them the seven that have a matrix product with weights: queries and keys with the
    rotation, values, output projection, gate, up and down projections with the routed experts,
    router); for odd k the second (Cm/TargetSegAtt.lean: the attention weights); for k = 24 the
    plain head with the scaled table and the identity on y (Cm/TargetSegHeadY.lean).
Stated for every table s of scales, lawful (`s.Lawful`, Cm/Rel2.lean) or not, with no hypothesis on
it, but for `Spec.model_true`:
  `Spec.segs_ok`: `SegsOK s (segM s)` (Cm/TargetSegAll.lean): shapes, well formed, places, and the
    assembly of each segment, twice. The instance that shows that Cm/TargetSegAll.lean's statements
    do not range over nothing.
  `Spec.model_equiv`: for every request x, every integer index matrix W, all integer matrices M of
    cells: `Cm.TP.Cond Gl.p s W x` (the trace of M) ⇔ for all k < 25 the conditions of `segM s k`
    hold at (x, W, M); and the same at the matrices of a trace T.
  `Spec.model_admit`: a witness T of `Cm.TP.Ryes Gl.p s i x` gives: r < e; matrices below 129 at
    all places of the shapes; all 25 segments' conditions at the index's own matrix.
  `Spec.model_force`: r < e, integer matrices M below 2^18 at all places of the shapes, all 25
    segments' conditions at the matrix of the index i: the trace of M is a witness of
    `Cm.TP.Rno Gl.p s i x`. (These two are the equivalence with a bound put beside it: no content
    on the reply. What a write-up of ours (lean/CREDITS.md) calls "admit" and "force", a
    true request has cells below the strict bound that meet the constraints; cells below the larger
    bound that meet them force the reply, is in the next statement.)
  `Spec.model_true`: at a lawful table: r < e and such matrices below 2^18 exist exactly if the
    request is true (Cm/RelBase.lean: `TrueAt`); and a true request has such matrices below 129:
    those of the honest trace. (Through `Cm.TP.forces`, `Cm.TP.trace_iff`: nothing wraps around.)
    That true and false requests exist, and that the index matters: the facts of
    Cm/RelTrue.lean, Cm/RelTrueExp.lean on `TrueAt`'s language; a lawful table: `lawful_sRef`.

Most uses of weights are in keys: a rounding's low key has the matrix product as a sum atom over
(index atom × cell atoms): 36 index atoms among the keys of each first segment, 2 in the head, none
in the second segments (a count in a file that is not in this repository): 13 segments read the
index, as in the write-up by a reading.

Limits: this file has no top record over a configuration: it lies in Cm/TargetPart.lean
(`targetPart R s`); "the matrix that is read off a message
which holds the index i is the image of i's matrix" is the index's side and is not stated here.
This file says nothing on protocols. This file does not say the declared
differences and what else a builder is owed: the head of Cm/TargetSegAll.lean. This file does not
say which list of conditions this is: the head of Cm/TargetPRel.lean. The numbers (variables,
atoms, sums, tensor rows, gluing) are not here; over this field, before gluing, by its head:
Cm/TargetPartNumSeg.lean (atoms in a term, variables, numbers of families, sizes of tables, the
shape of each `segM s k`).
After gluing, by its head, Cm/TargetPartNumKeys.lean has upper bounds
on the variables of the glued families and numbers of families;
it says nothing on the numbers of sum atoms or of index atoms.
Terms: lean/GLOSSARY.md.
The notions follow the worked example named in lean/CREDITS.md; the text is this library's.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cm.TargetSegAttOK
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Inst.Model Inst.Model.All

/-- Segment k of the model. -/
def segM (s : Scales) : ℕ → SegSpec XI Cb.Gl.F Cb.Gl.E := segOf s (attM s)

namespace Spec

/-- The 25 segments meet `SegsOK`. -/
def segs_ok : Prop := ∀ s : Scales, SegsOK s (segM s)

/-- The one equivalence at the model. -/
def model_equiv : Prop :=
  ∀ (s : Scales) (W : Mat) (x : Instance ppref),
    (∀ M : ℕ → ℕ → ℕ → ℤ,
      TP.Cond Cb.Gl.p s W x (ofMat Hd.plain M) ↔
      ∀ k < nSeg, (segM s k).Holds fmtRef x (TP.castW Cb.Gl.p W) (cM M)) ∧
    (∀ T : Trace,
      TP.Cond Cb.Gl.p s W x T ↔
      ∀ k < nSeg, (segM s k).Holds fmtRef x (TP.castW Cb.Gl.p W) (cM (toMat Hd.plain T)))

/-- a witness of the relation gives small matrices that meet all segments' conditions -/
def model_admit : Prop :=
  ∀ (s : Scales) (i : Idx) (x : Instance ppref) (T : Trace), TP.Ryes Cb.Gl.p s i x T →
    x.r < x.e ∧
    (∀ q : Cb.Place, InShape q → |toMat Hd.plain T q.1 q.2.1 q.2.2| < 129) ∧
    ∀ k < nSeg, (segM s k).Holds fmtRef x (TP.castW Cb.Gl.p i.mat) (cM (toMat Hd.plain T))

/-- if r < e, matrices below the relaxed bound that meet all segments' conditions give a witness of
the relaxed relation -/
def model_force : Prop :=
  ∀ (s : Scales) (i : Idx) (x : Instance ppref) (M : ℕ → ℕ → ℕ → ℤ), x.r < x.e →
    (∀ q : Cb.Place, InShape q → |M q.1 q.2.1 q.2.2| < 2 ^ 18) →
    (∀ k < nSeg, (segM s k).Holds fmtRef x (TP.castW Cb.Gl.p i.mat) (cM M)) →
    TP.Rno Cb.Gl.p s i x (ofMat Hd.plain M)

/-- at a lawful table, if r < e: the segments' conditions at small matrices say that the request is
true -/
def model_true : Prop :=
  ∀ s : Scales, s.Lawful →
    ∀ (i : Idx) (x : Instance ppref),
      ((x.r < x.e ∧
          ∃ M : ℕ → ℕ → ℕ → ℤ,
            (∀ q : Cb.Place, InShape q → |M q.1 q.2.1 q.2.2| < 2 ^ 18) ∧
            ∀ k < nSeg, (segM s k).Holds fmtRef x (TP.castW Cb.Gl.p i.mat) (cM M)) ↔
        TrueAt s.kap s.nf i x) ∧
      (TrueAt s.kap s.nf i x →
        (∀ q : Cb.Place, InShape q → |toMat Hd.plain (trace2 s i x) q.1 q.2.1 q.2.2| < 129) ∧
        ∀ k < nSeg,
          (segM s k).Holds fmtRef x (TP.castW Cb.Gl.p i.mat) (cM (toMat Hd.plain (trace2 s i x))))

end Spec

end Cm.Seg.TS
