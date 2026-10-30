-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerMembersOwed.lean: A DEFINITION, AND THREE STATEMENTS ON IT THAT ARE OWED
FOR K14's LAW, AS PROPOSITIONS BY def: NO PROOF HERE. The laws of the shared chain's blocks bear a
letter mem : from a message's number in the chain's statement to the member of the list that is that
message. At the list msSh (Johnson/Desc/Sound/SharedMembers.lean) the three members are memSh .oU,
.oOmega, .oSp (Johnson/Desc/Sound/SeamNumbersSh.lean), with the numbers numSh sU: 0, sU, sU + 1.

  memK            the letter mem, filled: 0, sU and sU + 1 to the three members; else none
  MemAtOwed       where o_u's sending has a message: memK at the three numbers
  MemNoOwed       oNoSh gives each of the three its number
  MemSitsOwed     who sits at a message's tenant has that message's number
What is not claimed. That they hold.
(They are proved in Johnson/Desc/K14/Law/LedgerMembers.lean: memAt, memNo, memSits.)
Nothing on soundness.

-/
import Johnson.Desc.Sound.SeamNumbersSh

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open Desc.K14.Law.Fence

/-- **The letter mem, filled**: from a message's number to the member. sU: how many messages o_u's
sending has. -/
def memK (S : LinShape) (rU rO rSp lo : ℕ) (layU layO : TreeLay) (sU : ℕ) : ℕ → Option Mem :=
  fun n =>
    if n = 0 then some (memSh S rU rO rSp lo layU layO .oU)
    else if n = sU then some (memSh S rU rO rSp lo layU layO .oOmega)
    else if n = sU + 1 then some (memSh S rU rO rSp lo layU layO .oSp)
    else none

/-- OWED: at the three numbers. (At sU = 0 the first two numbers are one: so the premise.) -/
def MemAtOwed : Prop :=
  ∀ (S : LinShape) (rU rO rSp lo : ℕ) (layU layO : TreeLay) (sU : ℕ), 0 < sU → ∀ m : Msg2,
    memK S rU rO rSp lo layU layO sU (numSh sU m) = some (memSh S rU rO rSp lo layU layO m)

/-- OWED: each of the three has its number. -/
def MemNoOwed : Prop :=
  ∀ (S : LinShape) (rU rO rSp lo : ℕ) (layU layO : TreeLay) (sU : ℕ) (m : Msg2),
    oNoSh sU (memSh S rU rO rSp lo layU layO m) = numSh sU m

/-- OWED: who sits at a message's tenant has that message's number. -/
def MemSitsOwed : Prop :=
  ∀ (S : LinShape) (rU rO rSp lo : ℕ) (layU layO : TreeLay) (codes : Codes)
    (sentU sentO : Array OracleNotice), layTrees codes sentU = some layU →
    layTrees codes sentO = some layO → 0 < sentU.size → 1 < sentO.size → ∀ (sU : ℕ) (m : Msg2),
    ∀ z ∈ msSh S rU rO rSp lo layU layO,
      SitsAt z (tenantSh lo layU layO m).1 (tenantSh lo layU layO m).2 → oNoSh sU z = numSh sU m

end Desc.K14.Law
