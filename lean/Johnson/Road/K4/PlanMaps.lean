-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/PlanMaps.lean: MAPS FROM THE ROUNDS THAT K4's BLOCK DECLARES TO THE TYPED ROUNDS OF
THE VALUE's CHAIN, AS DATA, AND THAT THEY ARE AS ASKED, for a sub-proof that is not the first.
Definitions and short theorems: an assembly of pieces that are proved elsewhere.

  `Plan4.Meets Q p hS pc`: the premises, as one record: those of `dimIs_layerNumbers`
    (PlanSizes.lean) at the place p's public record and plan and at the value's sizes Q.D; the
    value's number of rounds of the merge is the committed matrix's layout's; the group is not the
    first.
  `dsLater p`: the list of written rounds that K4's block declares at p in such a group, in the
    data of Johnson/Road/K4/DsTailR.lean (`rdOf`, `tailR`, `numsOf`).
    `k4Ds_dsLater`: `k4Ds p` is that list.
  `Plan4.chM`: the data of OnBytes/Desc/First/P1/ChMaps.lean for the value's chain over that list,
    at the program's own record of sizes `Verify.layerNumbers p.P p.hp p.g` (`ownAtM`).
  `Plan4.mapsK4`: the maps against the shape of the chain's reduction. `Plan4.mapsK4_ok`: they are
    as asked (`Maps.OK`).
  `Plan4.maps_plan`: at any list ds with `k4Ds p = some ds`: ds is `dsLater p`, and the maps carried
    to ds (`Maps.castD`, OnBytes/Flat/KindsRow.lean) are as asked.

The numberings N of the end values are a letter.

Limits. WHAT `Maps.OK` SAYS IS LITTLE: at each written round that is read, the map from its drawn
values to the typed round's challenge is one-to-one, and its positions have at most 64 bits
(OnBytes/Flat/CarrySMaps.lean). HOW MANY ELEMENTS A ROUND SENDS IS ASKED NOWHERE: a sent list is
read with 0 beyond its end. So of the fourteen equations on sizes only those on numbers of rounds
and of drawn coordinates bear on it. Nothing on which written scalar means what: that rests wholly
on the image of a transcript against what K4's text has heard, which is not treated here; nothing
on the counts, or on any law. It speaks of the rounds that the block
declares, not of a made plan's entries. The value's other letters are tied to no plan. That
`Meets` holds at a run's place is a premise (Johnson/Road/K4/PlanPublic.lean pays four of its
eight fields at the public part's record).
-/
import Johnson.Road.K4.PlanTail
import Johnson.Road.K4.DsTailLens
import OnBytes.Flat.KindsRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open OnBytes.Model.Layer (layout readsOf lamSOf nclOf)
open Inst.Model (Scl)
open OnBytes.Desc.First.K4 (covers Par k4Ds rdOf pointRd)
open OnBytes.Desc.First.P1 (ChM TailNums ownAtM ownAtMaps_ok)

variable [scl : Scl] {M X : Type}

/-- The premises, as one record. -/
structure Plan4.Meets (Q : Plan4 Cb.Gl.E M X) (p : Par) (hS : Layer.Shape)
    (pc : List (List String)) : Prop where
  hy : layout hS pc = .ok p.P.y
  hc : covers p.P = true
  hrd : readsOf p.P.y = .ok p.P.rd
  Z : Sized hS Q.D
  hl : p.hp.lamS = lamSOf p.P.y
  hn : p.hp.NCL = nclOf p.P.y p.g
  wk : Q.kW = p.P.wsLay.lk
  hg : (p.g == 0) = false

/-- The written rounds that K4's block declares at a place of a group that is not the first. -/
def dsLater (p : Par) : List RDT :=
  [rdOf (pointRd .zero p.P.y.h.lt)] ++ (tailR (numsOf p.P p.hp p.g)).all

variable {Q : Plan4 Cb.Gl.E M X} {p : Par} {hS : Layer.Shape} {pc : List (List String)}

namespace Plan4.Meets
variable (A : Q.Meets p hS pc)
include A

/-- The library's sizes are the program's own record's. -/
theorem dimIs : OnBytes.Tie.Pv.Lay.At.DimIs Q.D (Verify.layerNumbers p.P p.hp p.g) :=
  dimIs_layerNumbers A.hy A.hc A.hrd A.Z A.hl A.hn

/-- What the data of K4's declared rounds meet at the value's chain. -/
theorem written :
    OnBytes.Desc.First.P1.DrawsPt Q.full.own.toOwn.gT (rdOf (pointRd .zero p.P.y.h.lt)) ∧
      OnBytes.Desc.First.P1.TailDs Q.full.own.toOwn.tail (tailR (numsOf p.P p.hp p.g)) ∧
      OnBytes.Desc.First.P1.TailLens (tailR (numsOf p.P p.hp p.g))
        (Verify.layerNumbers p.P p.hp p.g) :=
  own_at Q.full.own.toOwn
    ⟨(Fo.readsOf_mu A.hrd).1, (Fo.readsOf_mu A.hrd).2.1, (Fo.readsOf_mu A.hrd).2.2⟩
    (lensTie_numbers p) A.dimIs.lt (Q.tailIs_plan A.hy A.hc A.hrd A.Z A.hl A.hn A.wk A.hg)

/-- K4's declared rounds are that list. -/
theorem k4Ds_dsLater : k4Ds p = some (dsLater p) := k4Ds_later A.hg

end Plan4.Meets

/-- **The data for the value's chain over K4's declared rounds.** -/
noncomputable def Plan4.chM (A : Q.Meets p hS pc) (N : TailNums Q.full.own.toOwn.tail) :
    ChM Q.full.own.toOwn.ch (dsLater p) :=
  ownAtM Q.full (Verify.layerNumbers p.P p.hp p.g) A.dimIs A.wk A.hg
    (rdOf (pointRd .zero p.P.y.h.lt)) A.written.2.2 N

/-- **The maps.** -/
noncomputable def Plan4.mapsK4 (A : Q.Meets p hS pc) (N : TailNums Q.full.own.toOwn.tail)
    (Ex : Iop.ExtSpec) : Maps (dsLater p) (Q.full.own.toOwn.ch.R Ex).shape :=
  (Plan4.chM A N).mapsR Ex

/-- **They are as asked** (`Maps.OK`: see the head's limits for how little that is), under
`Meets`. -/
theorem Plan4.mapsK4_ok (A : Q.Meets p hS pc) (N : TailNums Q.full.own.toOwn.tail)
    (Ex : Iop.ExtSpec) : (Plan4.mapsK4 A N Ex).OK :=
  ownAtMaps_ok Ex Q.full _ A.dimIs A.wk A.hg A.written.2.2 N A.written.1 A.written.2.1

/-- **At any list that K4's block declares at p**, under `Meets`: it is `dsLater p`, and the maps
carried to it are as asked. -/
theorem Plan4.maps_plan (A : Q.Meets p hS pc) (N : TailNums Q.full.own.toOwn.tail)
    (Ex : Iop.ExtSpec) {ds : List RDT} (hds : k4Ds p = some ds) :
    ∃ e : ds = dsLater p, ((Plan4.mapsK4 A N Ex).castD e).OK :=
  ⟨Option.some.inj (hds.symm.trans A.k4Ds_dsLater), Maps.ok_castD _ (Plan4.mapsK4_ok A N Ex)⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4.mapsK4_ok
#print axioms OnBytes.Road.K4.Plan4.maps_plan
