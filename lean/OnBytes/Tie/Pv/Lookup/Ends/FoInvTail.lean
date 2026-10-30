-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvTail.lean.
The routines of OnBytes/Model/Tail.lean keep every property of the state that has `Prim`.

One statement a routine, but for those named under "Left out": `Inv I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean) or, for a
routine of a link, `InvL I`
(OnBytes/Tie/Pv/Lookup/Ends/FoInvLink.lean); where a routine takes routines as arguments, under the
same of these.

Left out: HTailF2.coefficientsF (OnBytes/Tie/Pv/Lookup/Ends/FoInvCoef.lean), HTailF2.coefficients
(OnBytes/Tie/Pv/Lookup/Ends/FoInvCoef.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvMerge
import OnBytes.Model.Tail

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Fo
open OnBytes.PscRun OnBytes OnBytes.Model OnBytes.Model.HTailF2

variable {I : OnBytes.Model.Fork → Prop} [Fo.Prim I]

theorem inv_Model_HTailF2_drawMatrixF (tl : HTailF2)  :
    Inv I (OnBytes.Model.HTailF2.drawMatrixF tl) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply inv_Model_HTailF2_drawMatrixF)

theorem inv_Model_HTailF2_fixedBeforeTheMatrixF (tl : HTailF2)  :
    InvL I (OnBytes.Model.HTailF2.fixedBeforeTheMatrixF tl) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply inv_Model_HTailF2_fixedBeforeTheMatrixF)

theorem inv_Model_HTailF2_transcriptF (tl : HTailF2)  :
    InvL I (OnBytes.Model.HTailF2.transcriptF tl) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply inv_Model_HTailF2_transcriptF)

theorem inv_Model_HTailF2_transcript (tl : HTailF2)  :
    InvL I (OnBytes.Model.HTailF2.transcript tl) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply inv_Model_HTailF2_transcript)

theorem inv_Model_HTailF2_linJoin9 (tl : HTailF2)  :
    Inv I (OnBytes.Model.HTailF2.linJoin9 tl) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_HTailF2_linJoin9)

theorem inv_Model_HTailF2_linBits9 (tl : HTailF2)  :
    Inv I (OnBytes.Model.HTailF2.linBits9 tl) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_HTailF2_linBits9)

theorem inv_Model_HTailF2_linTie (tl : HTailF2) (mu : Nat)  :
    Inv I (OnBytes.Model.HTailF2.linTie tl mu) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_HTailF2_linTie)

theorem inv_Model_HTailF2_linRead (tl : HTailF2) (Fn : HFun) (sg laid : Nat) (sums : E)  :
    Inv I (OnBytes.Model.HTailF2.linRead tl Fn sg laid sums) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_HTailF2_linRead)

theorem inv_Model_HTailF2_weightsF (tl : HTailF2)  :
    Inv I (OnBytes.Model.HTailF2.weightsF tl) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_HTailF2_weightsF)

theorem inv_Model_HTailF2_objectsF (tl : HTailF2) (funs : Array HFun)  :
    Inv I (OnBytes.Model.HTailF2.objectsF tl funs) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_HTailF2_objectsF)

theorem inv_Model_HTailF2_selfTestF (tl : HTailF2) (nU : Array Nat)  :
    Inv I (OnBytes.Model.HTailF2.selfTestF tl nU) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_HTailF2_selfTestF)

theorem inv_Model_HTailF2_selfTest (tl : HTailF2) (nU : Array Nat)  :
    Inv I (OnBytes.Model.HTailF2.selfTest tl nU) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible apply inv_Model_HTailF2_selfTest)

theorem inv_Model_HTailF2_tileSelfTestF (tl : HTailF2)  :
    Inv I (OnBytes.Model.HTailF2.tileSelfTestF tl) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply inv_Model_HTailF2_tileSelfTestF)

theorem inv_Model_HTailF2_rkSelfTest (tl : HTailF2)  :
    Inv I (OnBytes.Model.HTailF2.rkSelfTest tl) := by inv

macro_rules
  | `(tactic| inv_rule) =>
    `(tactic| with_reducible apply inv_Model_HTailF2_rkSelfTest)

end Fo
