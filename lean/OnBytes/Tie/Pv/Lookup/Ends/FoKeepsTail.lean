-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsTail.lean.
Routines of OnBytes/Model/Tail.lean that keep what lies under the filled slots.

One statement for each routine but those that are left out (see below): `Keeps`
(OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean) or, for a routine of a link, `KeepsL`
(OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLink.lean). Where a routine takes routines as arguments, the
statement has the premise that each of these has `Keeps`. Neither property says anything of a run in
which the routine refuses. Each statement is also given as a rule to the tactic `keeps`
(OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean).

Left out: coefficientsF and coefficients, which run after the last claim and write the virtual
rows' weights by a function on the whole state. No statement is made of them.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsMerge
import OnBytes.Model.Tail

set_option autoImplicit false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Model OnBytes.Model.HTailF2

theorem keeps_Model_HTailF2_drawMatrixF (tl : HTailF2)  :
    Keeps (OnBytes.Model.HTailF2.drawMatrixF tl) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply keeps_Model_HTailF2_drawMatrixF)

theorem keeps_Model_HTailF2_fixedBeforeTheMatrixF (tl : HTailF2)  :
    KeepsL (OnBytes.Model.HTailF2.fixedBeforeTheMatrixF tl) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply keeps_Model_HTailF2_fixedBeforeTheMatrixF)

theorem keeps_Model_HTailF2_transcriptF (tl : HTailF2)  :
    KeepsL (OnBytes.Model.HTailF2.transcriptF tl) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply keeps_Model_HTailF2_transcriptF)

theorem keeps_Model_HTailF2_transcript (tl : HTailF2)  :
    KeepsL (OnBytes.Model.HTailF2.transcript tl) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply keeps_Model_HTailF2_transcript)

theorem keeps_Model_HTailF2_linJoin9 (tl : HTailF2)  :
    Keeps (OnBytes.Model.HTailF2.linJoin9 tl) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_HTailF2_linJoin9)

theorem keeps_Model_HTailF2_linBits9 (tl : HTailF2)  :
    Keeps (OnBytes.Model.HTailF2.linBits9 tl) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_HTailF2_linBits9)

theorem keeps_Model_HTailF2_linTie (tl : HTailF2) (mu : Nat)  :
    Keeps (OnBytes.Model.HTailF2.linTie tl mu) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_HTailF2_linTie)

theorem keeps_Model_HTailF2_linRead (tl : HTailF2) (Fn : HFun) (sg laid : Nat) (sums : E)  :
    Keeps (OnBytes.Model.HTailF2.linRead tl Fn sg laid sums) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_HTailF2_linRead)

theorem keeps_Model_HTailF2_weightsF (tl : HTailF2)  :
    Keeps (OnBytes.Model.HTailF2.weightsF tl) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_HTailF2_weightsF)

theorem keeps_Model_HTailF2_objectsF (tl : HTailF2) (funs : Array HFun)  :
    Keeps (OnBytes.Model.HTailF2.objectsF tl funs) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_HTailF2_objectsF)

theorem keeps_Model_HTailF2_selfTestF (tl : HTailF2) (nU : Array Nat)  :
    Keeps (OnBytes.Model.HTailF2.selfTestF tl nU) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_HTailF2_selfTestF)

theorem keeps_Model_HTailF2_selfTest (tl : HTailF2) (nU : Array Nat)  :
    Keeps (OnBytes.Model.HTailF2.selfTest tl nU) := by keeps

macro_rules | `(tactic| keeps_rule) => `(tactic| with_reducible apply keeps_Model_HTailF2_selfTest)

theorem keeps_Model_HTailF2_tileSelfTestF (tl : HTailF2)  :
    Keeps (OnBytes.Model.HTailF2.tileSelfTestF tl) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply keeps_Model_HTailF2_tileSelfTestF)

theorem keeps_Model_HTailF2_rkSelfTest (tl : HTailF2)  :
    Keeps (OnBytes.Model.HTailF2.rkSelfTest tl) := by keeps

macro_rules
  | `(tactic| keeps_rule) =>
    `(tactic| with_reducible apply keeps_Model_HTailF2_rkSelfTest)

end Fo
