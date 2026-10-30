-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/FinPart.lean: THE SHAPE OF THE FINISH's OWN FIELDS (FinOwn,
Johnson/Desc/First/State.lean:297): the last switch and the last proximity test of the first chain.
Definitions alone.

FIELD BY FIELD. `FinSh`: G : Option ReqGroup, answers, stages, L : GroupLayout, mask: AS THEY STAND
(numbers). fr : FrameSh (Calls.lean). row : GroupMk (Rows.lean): the batched row's make. sw, st :
`SwSh`: of what a code switch returned (Switched, OnBytes/Iop/Cs.lean:524): g, kept, others as they
stand; OF THE POSITIONS their range and how many were DRAWN. LEFT OUT: the positions themselves,
and how many of them differ: both hang on the draws. `swSh`, `finSh`, `finOf`: the readers.

Limits. Definitions alone: no law. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.Calls
import Johnson.Desc.First.Shape.Rows
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes VerifiableInference.Desc VerifiableInference.Desc.First

/-- What a code switch returned, without the positions' values. -/
structure SwSh where
  g : Nat
  kept : Array Nat
  others : Array Nat
  /-- the positions' range -/
  logN : Nat
  /-- how many positions were drawn -/
  draws : Nat

def swSh (w : Switched) : SwSh :=
  { g := w.g, kept := w.kept, others := w.others, logN := w.positions.logN
    draws := w.positions.draws.size }

/-- The shape of the finish's own fields. -/
structure FinSh where
  G : Option ReqGroup
  fr : FrameSh
  sw : SwSh
  answers : Option Nat
  stages : Option (Params.IoppStage × List Params.IoppStage)
  row : GroupMk
  L : GroupLayout
  mask : Option Nat
  st : SwSh

def finSh (a : FinOwn) : FinSh :=
  { G := a.G, fr := frameSh a.fr, sw := swSh a.sw, answers := a.answers, stages := a.stages
    row := groupMk a.row, L := a.L, mask := a.mask, st := swSh a.st }

def finOf : Here → Option FinSh
  | .fin a => some (finSh a)
  | _ => none

end VerifiableInference.Desc.First.Shape
