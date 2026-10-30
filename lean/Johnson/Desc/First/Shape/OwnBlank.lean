-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/OwnBlank.lean: FOR EACH SHAPE OF Johnson/Desc/First/Shape/Own.lean A RECORD
OF THAT SHAPE WITH ITS FIELD ELEMENTS 0 (ALL BUT ONE: see the Limits), and the law that its shape is
the shape it was made of. Definitions and small laws. Nothing is evaluated.

What it is for. A function of a record whose result's shape hangs on the record's shape alone can be
written on shapes by running it at the blank record.

  pscSh_blank, heardAll_blank   two of the three laws that Johnson/Desc/First/Shape/Tail.lean's
                  blanks lacked (the third, on TailSh.blank, is not here).
  LevelSh.blank, TscSh.blank, NormsSh.blank, StackSh.blank, RecSh.blank, MergeSh.blank, each with
                  its
  law levelSh_blank, tscSh_blank, normsSh_blank, stackSh_blank, recSh_blank, mergeSh_blank.
  **OwnSh.blank a y sc funs**, **ownSh_blank**   what the layers' own rounds leave. The layout, the
                  table of scales and the list of tables are no part of the shape: they are handed
                  in.

Limits. Definitions. A blank record is no record that a run leaves. NOT EVERY ELEMENT IS 0: the
sealed HeardAll.blank (Tail.lean) leaves the lookup's theta, alpha, a and leavesA to their defaults,
and a's default is 1 (Forest.Heard, OnBytes/Model/Look.lean): so (NormsSh.blank H).fo.a and
(OwnSh.blank a y sc funs).H.fo.a are 1. The laws speak of shapes alone. Nothing on soundness,
completeness or hiding.
-/
import Johnson.Desc.First.Shape.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model

theorem pscSh_blank (p : PscSh) : pscSh p.blank = p := by
  obtain ⟨a, b, c, d, e, f, g⟩ := p
  simp [pscSh, PscSh.blank, PscSh.mk, PscSh.rowMade, PscSh.started, PscSh.degrees,
    PscSh.challenges, PscSh.first, PscSh.start, PscSh.ended, affSh_blank, Function.comp_def]

theorem heardAll_blank (h : HeardAll) : heardAll h.blank = h := by
  cases h
  simp [heardAll, HeardAll.blank, affSh_blank, pscSh_blank, Function.comp_def]

/-- A layer of a product tree of this shape; every element 0. -/
def LevelSh.blank (l : LevelSh) : Level :=
  { r := Array.replicate l.r zeroE, sL := l.sL, sR := l.sR, tau := zeroE, row := l.row.blank }

theorem levelSh_blank (l : LevelSh) : levelSh l.blank = l := by
  cases l
  simp [levelSh, LevelSh.blank, affSh_blank]

/-- A token sumcheck of this shape; every element 0. -/
def TscSh.blank (o : TscSh) : Tsc :=
  { sCl := o.sCl, sEnd := o.sEnd, r := Array.replicate o.r zeroE, p := o.p.blank
    rowU := o.rowU.blank }

theorem tscSh_blank (o : TscSh) : tscSh o.blank = o := by
  cases o
  simp [tscSh, TscSh.blank, affSh_blank, pscSh_blank]

/-- The norms and the two token sumchecks of this shape; every element 0 but fo.a, which is 1 (see
the head's Limits). -/
def NormsSh.blank (H : NormsSh) : Layer.Heard :=
  { fo := H.fo.blank, PV := Array.replicate H.PV zeroE, ZE := Array.replicate H.ZE zeroE
    tkh := Array.replicate H.tkh zeroE, ztF := Array.replicate H.ztF zeroE, sW := H.sW
    gp := Array.replicate H.gp zeroE, wpl := H.wpl.blank, sPv := H.sPv
    omV := Array.replicate H.omV zeroE, tV := H.tV.blank, tT := H.tT.map TscSh.blank
    KT := H.KT.blank }

theorem normsSh_blank (H : NormsSh) : normsSh H.blank = H := by
  cases H
  simp [normsSh, NormsSh.blank, affSh_blank, heardAll_blank, levelSh_blank, tscSh_blank,
    Function.comp_def]

/-- The batched sumcheck's record of this shape; every element 0. -/
def StackSh.blank (K : StackSh) : Layer.HeardStack :=
  { rs := Array.replicate K.rs zeroE, sA0 := K.sA0, sH1 := K.sH1, sB0 := K.sB0, sV := K.sV
    fin := { Alin := K.Alin.blank, Blin := K.Blin.blank, As := zeroE, Bs := zeroE, wD := K.wD }
    rowS := K.rowS.blank }

theorem stackSh_blank (K : StackSh) : stackSh K.blank = K := by
  cases K
  simp [stackSh, StackSh.blank, affSh_blank]

/-- What is left of a weight claim, of this shape; every element 0. -/
def RecSh.blank (c : RecSh) : WsRecClaim :=
  { ui := c.ui, ka := zeroE
    f := c.f.map fun x =>
      { HV := Array.replicate x.1 zeroE, pl := Array.replicate x.2.1 zeroE
        AV := Array.replicate x.2.2 zeroE } }

theorem recSh_blank (c : RecSh) : recSh c.blank = c := by
  cases c
  simp [recSh, RecSh.blank, Function.comp_def]

/-- The merge's record of this shape; every element 0. -/
def MergeSh.blank (w : MergeSh) : WsForkOut :=
  { fvp := zeroE, beta := zeroE, rm := Array.replicate w.rm zeroE, p := w.p.blank, sFv := w.sFv
    recs := w.recs.map RecSh.blank }

theorem mergeSh_blank (w : MergeSh) : mergeSh w.blank = w := by
  cases w
  simp [mergeSh, MergeSh.blank, pscSh_blank, recSh_blank, Function.comp_def]

/-- **What the layers' own rounds leave, of this shape; every element 0 but H.fo.a, which is 1**
(see the head's Limits). y, sc: the plan's layout and table of scales; funs: the list of tables. -/
def OwnSh.blank (a : OwnSh) (y : Layer.Lay) (sc : Layer.Scales) (funs : List FunSh) : Layer.Own :=
  { v := { y := y, sc := sc, g := a.g, iU3 := a.iU3, K3 := a.K3
           tab := a.tab.map fun x => { name := x.1, first := x.2.1, len := x.2.2 }
           zk := (a.zk.map fun n => Array.replicate n zeroE).toArray }
    H := a.H.blank, K := a.K.blank, hd := a.hd.blank, hd2 := a.hd2.map LevelSh.blank
    sVE := a.sVE, wo := a.wo.blank, funs := (funs.map FunSh.blank).toArray }

theorem ownSh_blank (a : OwnSh) (y : Layer.Lay) (sc : Layer.Scales) (funs : List FunSh) :
    ownSh (a.blank y sc funs) = a := by
  cases a
  simp [ownSh, OwnSh.blank, normsSh_blank, stackSh_blank, levelSh_blank, mergeSh_blank,
    Function.comp_def]

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.pscSh_blank
#print axioms VerifiableInference.Desc.First.Shape.heardAll_blank
#print axioms VerifiableInference.Desc.First.Shape.levelSh_blank
#print axioms VerifiableInference.Desc.First.Shape.tscSh_blank
#print axioms VerifiableInference.Desc.First.Shape.normsSh_blank
#print axioms VerifiableInference.Desc.First.Shape.stackSh_blank
#print axioms VerifiableInference.Desc.First.Shape.recSh_blank
#print axioms VerifiableInference.Desc.First.Shape.mergeSh_blank
#print axioms VerifiableInference.Desc.First.Shape.ownSh_blank
#print axioms VerifiableInference.Desc.First.Shape.LevelSh.blank
#print axioms VerifiableInference.Desc.First.Shape.TscSh.blank
#print axioms VerifiableInference.Desc.First.Shape.NormsSh.blank
#print axioms VerifiableInference.Desc.First.Shape.StackSh.blank
#print axioms VerifiableInference.Desc.First.Shape.RecSh.blank
#print axioms VerifiableInference.Desc.First.Shape.MergeSh.blank
#print axioms VerifiableInference.Desc.First.Shape.OwnSh.blank
