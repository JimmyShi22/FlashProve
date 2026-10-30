-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/PlanMapsFirst.lean: MAPS FROM THE ROUNDS THAT K4's BLOCK DECLARES TO THE TYPED
ROUNDS OF THE VALUE's CHAIN, AS DATA, AND THAT THEY ARE AS ASKED, FOR THE FIRST SUB-PROOF (g = 0):
the twin of Johnson/Road/K4/PlanMaps.lean. Definitions and short theorems: an assembly
of pieces that are proved elsewhere.

  `Plan4F.MeetsF Q p hS pc`: the premises, as one record: those of `Plan4.Meets`, but that the group
    IS the first, and two more: the value's ls is the place's; its gB is the place's lPd - ls.
  `dsFirst p`: the list of written rounds that K4's block declares at p in the first group: the
    token point's round, two further points' rounds, then the sixteen pieces of the tail
    (Johnson/Road/K4/DsTailR.lean: `rdOf`, `tailR`, `numsOf`). `k4Ds_dsFirst`: `k4Ds p` is that
    list.
  `Plan4F.chMF`: the data of OnBytes/Desc/First/P1/ChMaps.lean for the first value's chain
    (`chFF Q.fullF`) over that list, at the program's own record of sizes
    `Verify.layerNumbers p.P p.hp p.g` (`ownFirstAtM`).
  `Plan4F.mapsK4F`: the maps against the shape of the chain's reduction. `Plan4F.mapsK4F_ok`: they
    are as asked (`Maps.OK`).
  `Plan4F.maps_planF`: at any list ds with `k4Ds p = some ds`: ds is `dsFirst p`, and the maps
    carried to ds are as asked.

The numberings N of the end values are a letter.

Limits. Those of PlanMaps.lean, here in short: WHAT `Maps.OK` SAYS IS LITTLE; how many elements a
round sends is asked nowhere; nothing on which written scalar means what; it speaks of the rounds
that the block declares, not of a made plan's entries; that `MeetsF` holds at a run's place is a
premise. Of the first group's seven letters: ls and gB are tied here; nb is then pinned by the
value's own hd (by reckoning: nb = d / S2; no theorem); tok and sE are tied to nothing.

-/
import Johnson.Road.K4.PlanMaps
import Johnson.Road.K4.CarriageFirst
import OnBytes.Desc.First.P1.OwnMapsAtFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open OnBytes.Model.Layer (layout readsOf lamSOf nclOf)
open Inst.Model (Scl)
open OnBytes.Desc.First.K4 (covers Par k4Ds rdOf pointRd)
open OnBytes.Desc.First.P1 (ChM TailNums ownFirstAtM ownFirstAtMaps_ok tailIsF_at)

variable [scl : Scl] {M X : Type}

/-- The premises, as one record. -/
structure Plan4F.MeetsF (Q : Plan4F Cb.Gl.E M X) (p : Par) (hS : Layer.Shape)
    (pc : List (List String)) : Prop where
  hy : layout hS pc = .ok p.P.y
  hc : covers p.P = true
  hrd : readsOf p.P.y = .ok p.P.rd
  Z : Sized hS Q.D
  hl : p.hp.lamS = lamSOf p.P.y
  hn : p.hp.NCL = nclOf p.P.y p.g
  wk : Q.kW = p.P.wsLay.lk
  hg : (p.g == 0) = true
  hls : Q.ls = p.P.y.ls
  hB : Q.gB = p.P.y.lPd - p.P.y.ls

/-- The written rounds that K4's block declares at a place of the first group. -/
def dsFirst (p : Par) : List RDT :=
  [rdOf (pointRd .zero p.P.y.h.lt)] ++
    ([rdOf (pointRd .zero (p.P.y.ls + p.P.y.h.lt))] ++
      ([rdOf (pointRd .zero (p.P.y.lPd - p.P.y.ls))] ++ (tailR (numsOf p.P p.hp p.g)).all))

variable {Q : Plan4F Cb.Gl.E M X} {p : Par} {hS : Layer.Shape} {pc : List (List String)}

namespace Plan4F.MeetsF
variable (A : Q.MeetsF p hS pc)
include A

/-- The library's sizes are the program's own record's. -/
theorem dimIs : OnBytes.Tie.Pv.Lay.At.DimIs Q.D (Verify.layerNumbers p.P p.hp p.g) :=
  dimIs_layerNumbers A.hy A.hc A.hrd A.Z A.hl A.hn

/-- The first value's chain, from the limbs' scalars on, has the numbers of that record. -/
theorem tailIs :
    OnBytes.Tie.Pv.Lay.TailIs Q.fullF.ownF.toOwn.tail (Verify.layerNumbers p.P p.hp p.g) :=
  tailIsF_at Q.fullF (Verify.layerNumbers p.P p.hp p.g) A.dimIs A.wk A.hg

/-- What `ownFirstAtM`'s data meet at the first value's chain. -/
theorem written :
    OnBytes.Desc.First.P1.DrawsPt Q.fullF.ownF.toOwn.gT (rdOf (pointRd .zero p.P.y.h.lt)) ∧
      OnBytes.Desc.First.P1.DrawsPt Q.fullF.ownF.toOwn.gA
        (rdOf (pointRd .zero (p.P.y.ls + p.P.y.h.lt))) ∧
      OnBytes.Desc.First.P1.DrawsPt Q.fullF.ownF.toOwn.gB
        (rdOf (pointRd .zero (p.P.y.lPd - p.P.y.ls))) ∧
      OnBytes.Desc.First.P1.TailDs Q.fullF.ownF.toOwn.tail (tailR (numsOf p.P p.hp p.g)) ∧
      OnBytes.Desc.First.P1.TailLens (tailR (numsOf p.P p.hp p.g))
        (Verify.layerNumbers p.P p.hp p.g) :=
  ownFirst_at Q.fullF.ownF.toOwn
    ⟨(Fo.readsOf_mu A.hrd).1, (Fo.readsOf_mu A.hrd).2.1, (Fo.readsOf_mu A.hrd).2.2⟩
    (lensTie_numbers p) A.dimIs.lt (congrArg₂ (· + ·) A.hls A.dimIs.lt) A.hB A.tailIs

/-- K4's declared rounds are that list. -/
theorem k4Ds_dsFirst : k4Ds p = some (dsFirst p) := k4Ds_first A.hg

end Plan4F.MeetsF

/-- **The data for the first value's chain over K4's declared rounds.** -/
noncomputable def Plan4F.chMF (A : Q.MeetsF p hS pc) (N : TailNums Q.fullF.ownF.toOwn.tail) :
    ChM (chFF Q.fullF) (dsFirst p) :=
  ownFirstAtM Q.fullF (Verify.layerNumbers p.P p.hp p.g) A.dimIs A.wk A.hg
    (rdOf (pointRd .zero p.P.y.h.lt)) (rdOf (pointRd .zero (p.P.y.ls + p.P.y.h.lt)))
    (rdOf (pointRd .zero (p.P.y.lPd - p.P.y.ls))) A.written.2.2.2.2 N

/-- **The maps.** -/
noncomputable def Plan4F.mapsK4F (A : Q.MeetsF p hS pc) (N : TailNums Q.fullF.ownF.toOwn.tail)
    (Ex : Iop.ExtSpec) : Maps (dsFirst p) ((chFF Q.fullF).R Ex).shape :=
  (Plan4F.chMF A N).mapsR Ex

/-- **They are as asked** (`Maps.OK`: see PlanMaps.lean's limits for how little that is), under
`MeetsF`. -/
theorem Plan4F.mapsK4F_ok (A : Q.MeetsF p hS pc) (N : TailNums Q.fullF.ownF.toOwn.tail)
    (Ex : Iop.ExtSpec) : (Plan4F.mapsK4F A N Ex).OK :=
  ownFirstAtMaps_ok Ex Q.fullF _ A.dimIs A.wk A.hg A.written.2.2.2.2 N A.written.1 A.written.2.1
    A.written.2.2.1 A.written.2.2.2.1

/-- **At any list that K4's block declares at p**, under `MeetsF`: it is `dsFirst p`, and the maps
carried to it are as asked. -/
theorem Plan4F.maps_planF (A : Q.MeetsF p hS pc) (N : TailNums Q.fullF.ownF.toOwn.tail)
    (Ex : Iop.ExtSpec) {ds : List RDT} (hds : k4Ds p = some ds) :
    ∃ e : ds = dsFirst p, ((Plan4F.mapsK4F A N Ex).castD e).OK :=
  ⟨Option.some.inj (hds.symm.trans A.k4Ds_dsFirst), Maps.ok_castD _ (Plan4F.mapsK4F_ok A N Ex)⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4F.mapsK4F_ok
#print axioms OnBytes.Road.K4.Plan4F.maps_planF
