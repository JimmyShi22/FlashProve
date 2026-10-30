-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/Own.lean: THE SHAPE OF WHAT THE LAYERS' OWN ROUNDS (K4) LEAVE: the record
Own (OnBytes/Model/Layer.lean) without its field elements: sizes in the place of arrays of elements,
slots as numbers, forms and sumchecks by their shapes (Johnson/Desc/First/Shape/Parts.lean), the
lookup's record and the tables by theirs (Johnson/Desc/First/Shape/Tail.lean). Definitions, and two
small laws. Nothing is evaluated.

THE FIELDS' TYPES. No field holds a field element.
  LevelSh   r : Nat (the number of challenges) · sL sR : Nat (slots) · row : AffSh. The point on the
            line (tau) is an element: out.
  TscSh     sCl sEnd : Nat (slots) · r : Nat · p : PscSh · rowU : AffSh.
  NormsSh   (of Layer.Heard) fo : HeardAll · PV ZE tkh ztF gp omV : Nat (sizes) · sW sPv : Nat
            (slots) · wpl : LevelSh · tV : TscSh · tT : Option TscSh · KT : AffSh.
  StackSh   (of Layer.HeardStack) rs : Nat · sA0 sH1 sB0 sV : Nat (slots) · Alin Blin : AffSh ·
            wD : Nat · rowS : AffSh. The two sides' values (As, Bs) are elements: out.
  RecSh     (of WsRecClaim) ui : Nat · f : List (Nat × Nat × Nat) (each factor's three sizes). The
            scalar ka is an element: out.
  MergeSh   (of WsForkOut) rm : Nat · p : PscSh · sFv : Nat (a slot) · recs : List RecSh. The shown
            value and its mask's factor are elements: out.
  OwnSh     g iU3 K3 : Nat · tab : List (String × Nat × Nat) (each family's name, first entry and
            number of entries) · zk : List Nat (sizes) · H : NormsSh · K : StackSh · hd : LevelSh ·
            hd2 : Option LevelSh · sVE : Nat (a slot) · wo : MergeSh.
  OUT, SINCE THE CHAIN's SHAPE SEES IT BY A COMPONENT OF ITS OWN: the list of tables (funs).
  OUT OF THE ENVIRONMENT: the layout (y) and the scales (sc): public data of the plan, which a step
  on the shape takes as a parameter.

  levelSh, tscSh, normsSh, stackSh, recSh, mergeSh, ownSh   the makers.
  OwnSh.skel      what a later listing's return hangs on, by the library's own record
                  (Johnson/Road/K4/Total/Returns.lean, Skel): the tables' places; the columns of the
                  array of the reads; "the second token sumcheck is there"; three sizes; the
                  lookup's shape. The library's record holds the layout too (EnvSkel.y): here that
                  is left to a parameter, as said above.
  ownSh_sFv, ownSh_skel   two readers.

Limits. Definitions. WIDE: every field of Own that is no element has its place, but for the three
named above as OUT (funs, y, sc), whether or not a later test reads it: the runs of claims behind
the hearing build their forms on these slots, and the forms' shapes are what the adding of the
claims tests. No update is here: this file does not say what the hearing lays as a function of the
plan and the next slot. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.Tail
import OnBytes.Model.Layer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model

/-- A layer of a product tree. -/
structure LevelSh where
  r : Nat
  sL : Nat
  sR : Nat
  row : AffSh

def levelSh (L : Level) : LevelSh := { r := L.r.size, sL := L.sL, sR := L.sR, row := affSh L.row }

/-- A token sumcheck. -/
structure TscSh where
  sCl : Nat
  sEnd : Nat
  r : Nat
  p : PscSh
  rowU : AffSh

def tscSh (o : Tsc) : TscSh :=
  { sCl := o.sCl, sEnd := o.sEnd, r := o.r.size, p := pscSh o.p, rowU := affSh o.rowU }

/-- The norms and the two token sumchecks. -/
structure NormsSh where
  fo : HeardAll
  PV : Nat
  ZE : Nat
  tkh : Nat
  ztF : Nat
  sW : Nat
  gp : Nat
  wpl : LevelSh
  sPv : Nat
  omV : Nat
  tV : TscSh
  tT : Option TscSh
  KT : AffSh

def normsSh (H : Layer.Heard) : NormsSh :=
  { fo := heardAll H.fo, PV := H.PV.size, ZE := H.ZE.size, tkh := H.tkh.size, ztF := H.ztF.size,
    sW := H.sW, gp := H.gp.size, wpl := levelSh H.wpl, sPv := H.sPv, omV := H.omV.size,
    tV := tscSh H.tV, tT := H.tT.map tscSh, KT := affSh H.KT }

/-- The batched sumcheck. -/
structure StackSh where
  rs : Nat
  sA0 : Nat
  sH1 : Nat
  sB0 : Nat
  sV : Nat
  Alin : AffSh
  Blin : AffSh
  wD : Nat
  rowS : AffSh

def stackSh (K : Layer.HeardStack) : StackSh :=
  { rs := K.rs.size, sA0 := K.sA0, sH1 := K.sH1, sB0 := K.sB0, sV := K.sV,
    Alin := affSh K.fin.Alin, Blin := affSh K.fin.Blin, wD := K.fin.wD, rowS := affSh K.rowS }

/-- What is left of a weight claim. -/
structure RecSh where
  ui : Nat
  f : List (Nat × Nat × Nat)

def recSh (c : WsRecClaim) : RecSh :=
  { ui := c.ui, f := c.f.map fun x => (x.HV.size, x.pl.size, x.AV.size) }

/-- The merge of the weight claims. -/
structure MergeSh where
  rm : Nat
  p : PscSh
  sFv : Nat
  recs : List RecSh

def mergeSh (w : WsForkOut) : MergeSh :=
  { rm := w.rm.size, p := pscSh w.p, sFv := w.sFv, recs := w.recs.map recSh }

/-- **What the layers' own rounds leave.** -/
structure OwnSh where
  g : Nat
  iU3 : Nat
  K3 : Nat
  tab : List (String × Nat × Nat)
  zk : List Nat
  H : NormsSh
  K : StackSh
  hd : LevelSh
  hd2 : Option LevelSh
  sVE : Nat
  wo : MergeSh

def ownSh (o : Layer.Own) : OwnSh :=
  { g := o.v.g, iU3 := o.v.iU3, K3 := o.v.K3, tab := o.v.tab.map fun x => (x.name, x.first, x.len),
    zk := o.v.zk.toList.map (·.size), H := normsSh o.H, K := stackSh o.K, hd := levelSh o.hd,
    hd2 := o.hd2.map levelSh, sVE := o.sVE, wo := mergeSh o.wo }

/-- What a later listing's return hangs on: the tables' places; the columns of the array of the
reads; the second token sumcheck is there; three sizes; the lookup's shape. -/
def OwnSh.skel (a : OwnSh) :
    List (String × Nat × Nat) × Nat × Bool × Nat × Nat × Option Nat × Forest.Shape :=
  (a.tab, a.K3, a.H.tT.isSome, a.H.wpl.r, a.hd.r, a.hd2.map (·.r), a.H.fo.shape)

theorem ownSh_sFv (o : Layer.Own) : (ownSh o).wo.sFv = o.wo.sFv := rfl

theorem ownSh_skel (o : Layer.Own) :
    (ownSh o).skel = (o.v.tab.map fun x => (x.name, x.first, x.len), o.v.K3, o.H.tT.isSome,
      o.H.wpl.r.size, o.hd.r.size, o.hd2.map (·.r.size), o.H.fo.shape) := by
  unfold OwnSh.skel ownSh normsSh levelSh
  simp [Option.map_map, Function.comp_def, heardAll]

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.ownSh_sFv
#print axioms VerifiableInference.Desc.First.Shape.ownSh_skel
