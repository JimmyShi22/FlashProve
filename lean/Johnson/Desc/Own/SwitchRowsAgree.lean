-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/SwitchRowsAgree.lean: the five makers of
Johnson/Desc/Own/SwitchRows.lean agree with the hand-written program's (OnBytes/Iop/Cs.lean) at all
arguments. No block imports this file.

Statements and proofs. Each proof is `rfl`: the two texts are the same but for names.
Main names: `swFormOn_eq`, `swFrame_eq`, `swCarried_eq`, `swOldSamples_eq`, `swRows_eq`.
Why: a law that is proved of the hand-written program's maker holds of the description's by one
rewriting.
Limits: nothing on what the rows mean. Nothing on soundness.

-/
import Johnson.Desc.Own.SwitchRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

theorem swFormOn_eq (o : Nat) (row : Row) : swFormOn o row = switchFormOn o row := rfl

theorem swFrame_eq (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat)
    (anew : Array Nat) : swFrame S old T g anew = switchFrame S old T g anew := rfl

theorem swCarried_eq (W : SwitchFrame) (old : SingleRows) :
    swCarried W old = switchCarried W old := rfl

theorem swOldSamples_eq (S : Statement) (W : SwitchFrame) :
    swOldSamples S W = switchOldSamples S W := rfl

theorem swRows_eq (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat)
    (anew : Array Nat) (pos : Positions) (y : Array E) :
    swRows S old T g anew pos y = switchRows S old T g anew pos y := rfl

end VerifiableInference.Desc.Own

#print axioms VerifiableInference.Desc.Own.swFormOn_eq
#print axioms VerifiableInference.Desc.Own.swFrame_eq
#print axioms VerifiableInference.Desc.Own.swCarried_eq
#print axioms VerifiableInference.Desc.Own.swOldSamples_eq
#print axioms VerifiableInference.Desc.Own.swRows_eq
