-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/LayersPartsAside.lean: what is set aside at the written values
inside a layers' link, the layers' parts: of the lookup's record its calls and rows; of the lookup's
record as heard its calls; of the own record the lookup's calls and rows as heard, tV.rowU, the p
and rowU of tT, KT, and the entries of K.Alin, K.Blin and K.rowS. Plain definitions and laws by
cases; nothing is evaluated.

Why. The inner written values of a layers' link (shapes written out as Lean terms) are whole but
for these parts, after the pattern of SetAside (Johnson/AtFull/Shape/JoinMany.lean). The slots of
the three long forms and the rows of the lookup's record as heard stay in the value, because the
light batching's step reads them (objectsG the rows, the covered runs the slots).

  OwnRecordParts, ownRecordPartsOf, noOwnRecordParts, ownRecordWithParts   the own record's parts:
                          their type, reading them, none, and putting them back.
  lookupRecordWithParts, lookupRecordWithCalls   putting parts back into a lookup's record.
  LayersPartsData, layersPartsOf, noLayersParts   the layers' parts of a whole shape.
  chainWithLayersParts, shapeWithLayersParts   putting them where a record stands.
  **lessLayersParts**     the shape less the parts.
  **shape_eq_lessParts_withParts**   a shape is what it is less the parts, with its own parts put
                          back.
  lessLayersParts_own     under lessLayersParts the own record is ownRecordLessParts of it.

Limits. Definitions and equations alone: that no member opens a part is not said here. What any of
this costs Lean's kernel is not measured here. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.OwnRecordClosedForm
import Johnson.AtFull.Shape.FrameForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.LayersPartsAside
open OnBytes OnBytes.Model
open Johnson.AtFull.Shape
open OnBytes.Desc.First.K4.Rt (ownRecordLessParts lookupRecordLessParts normsLessParts
    stackLessParts emptyForm bareSumcheckShape)
open VerifiableInference.Desc.First.Shape

/-- Of own: the lookup's calls and rows as heard, tV.rowU, the p and rowU of tT, KT, and the entries
of K.Alin, K.Blin and K.rowS. -/
abbrev OwnRecordParts : Type :=
  Array Call × List AffSh × AffSh × Option (PscSh × AffSh) × AffSh × List EntSh × List EntSh ×
    List EntSh

/-- Reads the own record's parts. -/
def ownRecordPartsOf (o : OwnSh) : OwnRecordParts :=
  (o.H.fo.shape.calls, o.H.fo.rows, o.H.tV.rowU, o.H.tT.map fun t => (t.p, t.rowU), o.H.KT,
    o.K.Alin.ents, o.K.Blin.ents, o.K.rowS.ents)

/-- The empty parts of an own record. -/
def noOwnRecordParts : OwnRecordParts := (#[], [], emptyForm, none, emptyForm, [], [], [])

/-- own with the parts put in; the three forms keep their slots. -/
def ownRecordWithParts (o : OwnSh) (q : OwnRecordParts) : OwnSh :=
  { o with
    H := { o.H with
      fo := { o.H.fo with shape := { o.H.fo.shape with calls := q.1 }, rows := q.2.1 }
      tV := { o.H.tV with rowU := q.2.2.1 }
      tT := o.H.tT.map fun t =>
        { t with p := (q.2.2.2.1.map (·.1)).getD bareSumcheckShape, rowU :=
            (q.2.2.2.1.map (·.2)).getD emptyForm }
      KT := q.2.2.2.2.1 }
    K := { o.K with
      Alin := AffSh.mk q.2.2.2.2.2.1 o.K.Alin.slots
      Blin := AffSh.mk q.2.2.2.2.2.2.1 o.K.Blin.slots
      rowS := AffSh.mk q.2.2.2.2.2.2.2 o.K.rowS.slots } }

/-- The own record less its parts is the own record with the empty parts put in. -/
theorem ownRecordLessParts_isNoParts (o : OwnSh) : ownRecordLessParts o =
    ownRecordWithParts o noOwnRecordParts := rfl

/-- An own record is what stays of it with its own parts put back. -/
theorem ownRecordWithParts_self (o : OwnSh) : ownRecordWithParts (ownRecordLessParts o)
    (ownRecordPartsOf o) = o := by
  obtain ⟨g, iU3, K3, tab, zk, H, K, hd, hd2, sVE, wo⟩ := o
  obtain ⟨fo, PV, ZE, tkh, ztF, sW, gp, wpl, sPv, omV, tV, tT, KT⟩ := H
  cases tT with
  | none => rfl
  | some t => rfl

/-- A lookup's record with the calls and rows q put in. -/
def lookupRecordWithParts (h : HeardAll) (q : Array Call × List AffSh) : HeardAll :=
  { h with shape := { h.shape with calls := q.1 }, rows := q.2 }

/-- A lookup's record with the calls q put in. -/
def lookupRecordWithCalls (h : HeardAll) (q : Array Call) : HeardAll :=
  { h with shape := { h.shape with calls := q } }

/-- **The parts**: of look: calls and rows; of lookHeard: calls; of own: OwnRecordParts. -/
abbrev LayersPartsData : Type := Option (Array Call × List AffSh) × Option (Array Call) × Option
    OwnRecordParts

/-- Reads the layers' parts of a whole shape. -/
def layersPartsOf (x : ShA) : LayersPartsData :=
  (x.1.look.map fun h => (h.shape.calls, h.rows), x.1.lookHeard.map fun h => h.shape.calls,
    x.1.own.map ownRecordPartsOf)

/-- No parts handed in. -/
def noLayersParts : LayersPartsData := (none, none, none)

/-- The chain's shape with the parts put where a record stands; where none are handed in, the empty
ones. -/
def chainWithLayersParts : ChainSh → LayersPartsData → ChainSh
  | (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18), p =>
    (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
      a13.map fun h => lookupRecordWithParts h (p.1.getD (#[], [])), a14.map fun h =>
          lookupRecordWithCalls h (p.2.1.getD #[]),
      a15.map fun o => ownRecordWithParts o (p.2.2.getD noOwnRecordParts), a16, a17, a18)

/-- The whole shape with the parts put in. -/
def shapeWithLayersParts (x : ShA) (p : LayersPartsData) : ShA := (chainWithLayersParts x.1 p, x.2)

/-- **The shape less the parts.** -/
def lessLayersParts (x : ShA) : ShA := shapeWithLayersParts x noLayersParts

/-- **A shape is what it is less the parts, with its own parts put back.** -/
theorem shape_eq_lessParts_withParts {x c : ShA} (h : lessLayersParts x = c) : x =
    shapeWithLayersParts c (layersPartsOf x) := by
  subst h
  obtain ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩,
    F⟩ := x
  cases a15 with
  | none => cases a13 <;> cases a14 <;> rfl
  | some o =>
    obtain ⟨g, iU3, K3, tab, zk, H, K, hd, hd2, sVE, wo⟩ := o
    obtain ⟨fo, PV, ZE, tkh, ztF, sW, gp, wpl, sPv, omV, tV, tT, KT⟩ := H
    cases tT <;> cases a13 <;> cases a14 <;> rfl

/-- lessLayersParts leaves ownRecordLessParts of the own record. -/
theorem lessLayersParts_own (x : ShA) : (lessLayersParts x).1.own =
    x.1.own.map ownRecordLessParts := by
  obtain ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩,
    F⟩ := x
  rfl

end Johnson.AtFull.Shape.LayersPartsAside

#print axioms Johnson.AtFull.Shape.LayersPartsAside.OwnRecordParts
#print axioms Johnson.AtFull.Shape.LayersPartsAside.ownRecordPartsOf
#print axioms Johnson.AtFull.Shape.LayersPartsAside.noOwnRecordParts
#print axioms Johnson.AtFull.Shape.LayersPartsAside.ownRecordWithParts
#print axioms Johnson.AtFull.Shape.LayersPartsAside.ownRecordLessParts_isNoParts
#print axioms Johnson.AtFull.Shape.LayersPartsAside.ownRecordWithParts_self
#print axioms Johnson.AtFull.Shape.LayersPartsAside.lookupRecordWithParts
#print axioms Johnson.AtFull.Shape.LayersPartsAside.lookupRecordWithCalls
#print axioms Johnson.AtFull.Shape.LayersPartsAside.LayersPartsData
#print axioms Johnson.AtFull.Shape.LayersPartsAside.layersPartsOf
#print axioms Johnson.AtFull.Shape.LayersPartsAside.noLayersParts
#print axioms Johnson.AtFull.Shape.LayersPartsAside.chainWithLayersParts
#print axioms Johnson.AtFull.Shape.LayersPartsAside.shapeWithLayersParts
#print axioms Johnson.AtFull.Shape.LayersPartsAside.lessLayersParts
#print axioms Johnson.AtFull.Shape.LayersPartsAside.shape_eq_lessParts_withParts
#print axioms Johnson.AtFull.Shape.LayersPartsAside.lessLayersParts_own
