-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/OwnMapsAt.lean: the maps of OwnMaps.lean AT THE LIBRARY'S VALUE of the chain
of a layers' sub-proof's own rounds (Cb/Pv/Lay/At/OwnW.lean: `FullPar.own`; a sub-proof that is not
the first). A definition, and that the maps are as asked.

OnBytes/Tie/Pv/Lay/At/Sizes.lean (`sizesV`, `nW_eq`) and OwnSizes.lean (`tailIs`) give
that the chain's numbers at the value are those of the planner's record of sizes x, if the
library's sizes are (`DimIs`). So the seven ties of OwnMaps.lean are paid.

  `tailIs_at`: `TailIs` of the value's tail.
  `ownAtM`: the data of ChMaps.lean for `P.own.toOwn.ch`.
  `ownAtMaps_ok`: the maps against the shape of that chain's reduction are as asked.

The chain is the one of which Cb/Pv/Lay/At/OwnW.lean's `own_knowAt` speaks.

Limits. Those of OwnMaps.lean and of the called files. Premises: `DimIs P.D x`; the merge's rounds
are the planner's; x is not the first group's; the lengths of the written stretches (`TailLens`);
what the written rounds draw (`TailDs`); the numberings of the end values are letters. The
first sub-proof's value is not treated here.
-/
import OnBytes.Desc.First.P1.OwnMapsPlan
import OnBytes.Tie.Pv.Lay.At.Sizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.P1
open Iop Prob IOR Cb TWhole Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At Johnson.L5.Layers Johnson.L5.Door
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Params (LayerRounds)
open OnBytes.Tie.Pv.Lay (TailIs tailIs)
open OnBytes.Tie.Pv.Lay.At (DimIs sizesV nW_eq)
open Inst.Model (Scl)

variable [scl : Scl] {M X : Type}

/-- The numbers of the value's tail are the planner's record's. -/
theorem tailIs_at (P : FullPar GE M X) (x : LayerRounds) (h : DimIs P.D x) (wk : P.kW = x.lkW)
    (hf : x.firstGroup = false) : TailIs P.own.toOwn.tail x :=
  tailIs (sizesV P.toOwnPar P.wPart x h (nW_eq P x h) wk hf)

/-- **The data for the chain at the value.** -/
noncomputable def ownAtM (P : FullPar GE M X) (x : LayerRounds) (h : DimIs P.D x)
    (wk : P.kW = x.lkW) (hf : x.firstGroup = false) (dT : RDT) {R : TailR} (hl : TailLens R x)
    (N : TailNums P.own.toOwn.tail) : ChM P.own.toOwn.ch ([dT] ++ R.all) :=
  ownM P.own.toOwn dT (TailM.ofIs (tailIs_at P x h wk hf) hl N)

/-- **The maps at the value are as asked.** -/
theorem ownAtMaps_ok (Ex : ExtSpec) (P : FullPar GE M X) (x : LayerRounds) (h : DimIs P.D x)
    (wk : P.kW = x.lkW) (hf : x.firstGroup = false) {dT : RDT} {R : TailR} (hl : TailLens R x)
    (N : TailNums P.own.toOwn.tail) (hT : DrawsPt P.own.toOwn.gT dT)
    (H : TailDs P.own.toOwn.tail R) : ((ownAtM P x h wk hf dT hl N).mapsR Ex).OK :=
  ownMaps_ok Ex P.own.toOwn _ hT H

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.tailIs_at
#print axioms OnBytes.Desc.First.P1.ownAtMaps_ok
