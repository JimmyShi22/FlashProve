-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/Chains.lean: the key file's three chains at the full size's written values, as
closed terms: the texts of the library's own routines (Key.firstChain; Key.sharedChain and
Key.thirdChain through Later.lean) at keyFull, recordSet, the written declared rounds and places'
numbers (KB8/Written.lean) and the tenants as told (Told.lean). Definitions alone.
Limits. That a key file's description has these chains at any public files is said in another file,
under named equations. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.Later
import Johnson.HB.LLHARD.KB4.Told
import Johnson.HB.LLHARD.KB8.Written

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open Lk6.AtPlan (keyFull)
open Johnson.KB8 (declKeyFull rangesNumsFull laterPlacesFull)

/-- The one-time chain's values that the first chain reads. -/
def oneFull : OneTime :=
  oneAt recordSet.samples keyFull.once.input keyFull.ranges.x keyFull.codes keyFull.once.shape

/-- The first chain. -/
def firstFull : Chain FirstState Claim :=
  firstChain oneFull declKeyFull.1 toldKeyFull.1 keyFull.set rangesNumsFull

/-- The shared chain, where its front says yes. -/
def sharedFull : Chain _root_.Desc.K14.St Claim := (sharedZ keyFull true laterPlacesFull).retype

/-- The third chain. -/
def thirdFull : Chain VerifiableInference.Desc.Third.S₃ Claim :=
  (thirdZ keyFull laterPlacesFull).retype

end Johnson.KB4
