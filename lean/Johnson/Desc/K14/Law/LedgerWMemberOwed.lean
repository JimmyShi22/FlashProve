-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerWMemberOwed.lean: A TEST WITH CODE, AND ONE STATEMENT ON IT THAT IS OWED
FOR K14's LAW, AS A PROPOSITION BY def: NO PROOF HERE. The law of the shared chain's first block
("LIN point") bears a letter xW: the member of the first chain's list of sampled members that is W's
message. It asks three things of it: it is in the list; it sits at W's seat; its shape is the shape
that the plan gives W. No term for xW lies. Here: a test on the list, the seat and the shape, whose
yes gives such a member.

  wMemberB ms seat sh   the first member of ms that sits at the seat is there and has the shape sh
  WMemberOwed           its yes gives a member with the three
What is not claimed. That it holds. That the test says yes at a plan. Nothing on soundness.

-/
import Johnson.Desc.Sound.SharedMembers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes
open VerifiableInference.Desc.Sound

/-- **A TEST ON THE PLAN**: the first member of the list at the seat is there, with the shape sh. -/
def wMemberB (ms : List Mem) (seat : ℕ × ℕ) (sh : OracleShape) : Bool :=
  (ms.find? fun m => decide (m.1.seat m.2 = seat)).any fun m => decide ((m.1.l.get m.2).1 = sh)

/-- OWED: the test's yes gives the member that the law at "LIN point" asks. -/
def WMemberOwed : Prop :=
  ∀ (ms : List Mem) (seat : ℕ × ℕ) (sh : OracleShape), wMemberB ms seat sh = true →
    ∃ xW : Mem, xW ∈ ms ∧ SitsAt xW seat.1 seat.2 ∧ sh = (xW.1.l.get xW.2).1

end Desc.K14.Law
