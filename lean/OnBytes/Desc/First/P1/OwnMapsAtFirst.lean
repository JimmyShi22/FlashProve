-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/OwnMapsAtFirst.lean: the maps of OwnMaps.lean AT THE LIBRARY'S VALUE of the
chain of THE FIRST layers' sub-proof's own rounds (Cb/Pv/Lay/At/OwnFirstW.lean: `FullFPar.ownF`):
the twin of OwnMapsAt.lean. A definition, and that the maps are as asked.

OnBytes/Tie/Pv/Lay/At/Sizes.lean (`sizesVF`, `nW_eq`) and OwnSizes.lean (`tailIsF`) give
that the chain's numbers at the value, from the limbs' scalars on, are those of the planner's record
of sizes x, if the library's sizes are (`DimIs`). So the seven ties of OwnMaps.lean are paid.

  `tailIsF_at`: `TailIs` of the value's tail.
  `ownFirstAtM`: the data of ChMaps.lean for `P.ownF.toOwn.ch`: three points, then the tail.
  `ownFirstAtMaps_ok`: the maps against the shape of that chain's reduction are as asked.

Limits. Those of OwnMaps.lean and of the called files. Premises: `DimIs P.D x`; the merge's rounds
are the planner's; x is the first group's; the lengths of the written stretches (`TailLens`); what
the written rounds draw (three times `DrawsPt`; `TailDs`); the numberings of the end values are
letters.
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
open OnBytes.Tie.Pv.Lay (TailIs tailIsF)
open OnBytes.Tie.Pv.Lay.At (DimIs sizesVF nW_eq)
open Inst.Model (Scl)

variable [scl : Scl] {M X : Type}

/-- The numbers of the first value's tail are the planner's record's. -/
theorem tailIsF_at (P : FullFPar GE M X) (x : LayerRounds) (h : DimIs P.D x) (wk : P.kW = x.lkW)
    (hf : x.firstGroup = true) : TailIs P.ownF.toOwn.tail x :=
  tailIsF (sizesVF P.ofp P.wfPart x h (nW_eq P.toFullPar x h) wk hf)

/-- **The data for the first chain at the value.** -/
noncomputable def ownFirstAtM (P : FullFPar GE M X) (x : LayerRounds) (h : DimIs P.D x)
    (wk : P.kW = x.lkW) (hf : x.firstGroup = true) (dT dA dB : RDT) {R : TailR}
    (hl : TailLens R x) (N : TailNums P.ownF.toOwn.tail) :
    ChM P.ownF.toOwn.ch ([dT] ++ ([dA] ++ ([dB] ++ R.all))) :=
  ownFirstM P.ownF.toOwn dT dA dB (TailM.ofIs (tailIsF_at P x h wk hf) hl N)

/-- **The maps are as asked.** -/
theorem ownFirstAtMaps_ok (Ex : ExtSpec) (P : FullFPar GE M X) (x : LayerRounds)
    (h : DimIs P.D x) (wk : P.kW = x.lkW) (hf : x.firstGroup = true) {dT dA dB : RDT} {R : TailR}
    (hl : TailLens R x) (N : TailNums P.ownF.toOwn.tail) (hT : DrawsPt P.ownF.toOwn.gT dT)
    (hA : DrawsPt P.ownF.toOwn.gA dA) (hB : DrawsPt P.ownF.toOwn.gB dB)
    (H : TailDs P.ownF.toOwn.tail R) :
    ((ownFirstAtM P x h wk hf dT dA dB hl N).mapsR Ex).OK :=
  ownFirstMaps_ok Ex P.ownF.toOwn _ hT hA hB H

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.tailIsF_at
#print axioms OnBytes.Desc.First.P1.ownFirstAtMaps_ok
