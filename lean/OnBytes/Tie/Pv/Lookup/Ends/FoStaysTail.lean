-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysTail.lean.
Routines of OnBytes/Model/Tail.lean stay on the view: those that are named below.

One statement a routine: `DryS` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) or, for a routine of a
link, `DryL`: a run on a view that returns is still on the view. Where a routine takes routines or
blocks as arguments, the statement stands under the same of these. Each is proved by the tactic
`stays` (OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean) on the routine's own body; a routine that is
defined by recursion has a proof by induction.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysMerge
import OnBytes.Model.Tail

set_option autoImplicit false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Model OnBytes.Model.HTailF2

theorem stays_Model_HTailF2_drawMatrixF (tl : HTailF2)  :
    DryS (OnBytes.Model.HTailF2.drawMatrixF tl) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply stays_Model_HTailF2_drawMatrixF)

theorem stays_Model_HTailF2_fixedBeforeTheMatrixF (tl : HTailF2)  :
    DryL (OnBytes.Model.HTailF2.fixedBeforeTheMatrixF tl) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply stays_Model_HTailF2_fixedBeforeTheMatrixF)

theorem stays_Model_HTailF2_transcriptF (tl : HTailF2)  :
    DryL (OnBytes.Model.HTailF2.transcriptF tl) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply stays_Model_HTailF2_transcriptF)

theorem stays_Model_HTailF2_transcript (tl : HTailF2)  :
    DryL (OnBytes.Model.HTailF2.transcript tl) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply stays_Model_HTailF2_transcript)

theorem stays_Model_HTailF2_linJoin9 (tl : HTailF2)  :
    DryS (OnBytes.Model.HTailF2.linJoin9 tl) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_HTailF2_linJoin9)

theorem stays_Model_HTailF2_linBits9 (tl : HTailF2)  :
    DryS (OnBytes.Model.HTailF2.linBits9 tl) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_HTailF2_linBits9)

theorem stays_Model_HTailF2_linTie (tl : HTailF2) (mu : Nat)  :
    DryS (OnBytes.Model.HTailF2.linTie tl mu) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_HTailF2_linTie)

theorem stays_Model_HTailF2_linRead (tl : HTailF2) (Fn : HFun) (sg laid : Nat) (sums : E)  :
    DryS (OnBytes.Model.HTailF2.linRead tl Fn sg laid sums) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_HTailF2_linRead)

theorem stays_Model_HTailF2_weightsF (tl : HTailF2)  :
    DryS (OnBytes.Model.HTailF2.weightsF tl) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_HTailF2_weightsF)

theorem stays_Model_HTailF2_objectsF (tl : HTailF2) (funs : Array HFun)  :
    DryS (OnBytes.Model.HTailF2.objectsF tl funs) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_HTailF2_objectsF)

theorem stays_Model_HTailF2_selfTestF (tl : HTailF2) (nU : Array Nat)  :
    DryS (OnBytes.Model.HTailF2.selfTestF tl nU) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_HTailF2_selfTestF)

theorem stays_Model_HTailF2_selfTest (tl : HTailF2) (nU : Array Nat)  :
    DryS (OnBytes.Model.HTailF2.selfTest tl nU) := by stays

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply stays_Model_HTailF2_selfTest)

theorem stays_Model_HTailF2_tileSelfTestF (tl : HTailF2)  :
    DryS (OnBytes.Model.HTailF2.tileSelfTestF tl) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply stays_Model_HTailF2_tileSelfTestF)

theorem stays_Model_HTailF2_rkSelfTest (tl : HTailF2)  :
    DryS (OnBytes.Model.HTailF2.rkSelfTest tl) := by stays

macro_rules
  | `(tactic| stays_rule) =>
    `(tactic| with_reducible apply stays_Model_HTailF2_rkSelfTest)

end Fo
