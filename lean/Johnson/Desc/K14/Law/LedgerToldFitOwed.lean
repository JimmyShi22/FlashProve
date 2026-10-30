-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerToldFitOwed.lean: ONE CLOSED FACT ON THE SHARED CHAIN's PARAMETERS AT THE
TYPED VALUES, AS A PROPOSITION BY def: NO PROOF HERE. Another file brings
«the seats of o_u, o_omega and o_sp fit what the IOP as written in Lean tells» (SeatFits; the
ledger's premises hFU, hFO, and with them hSh2, hSh5) down to one test with code on the codes, the
shape and the two layouts: toldFitB (Johnson/Second/Seam/SeatOfTold.lean). This file asks that
test's accept at the values that the ledger's top has at the seat: the typed codes, the typed shape,
and the two layouts as the shared table's constant makes them.

  ToldFitOwed   at every x that realSized returns with codesFull2: toldFitB accepts
The road: as ten_real (Johnson/Goal/Numbers/K14PlanTen.lean): the Bool under realSized.any, decided by Lean's kernel.
Can it be met? realSized returns (k14_real). Whether the test accepts there: evaluated, by report, at the planner's own values alone; not at these.
(Decided at these values by the kernel: toldFit_any, Johnson/Second/Seam/ToldFitWritten.lean;
and map14_hTold, LedgerScopeTerms.lean.)
What is not claimed. Nothing on soundness.
-/
import Johnson.Second.Seam.SeatOfTold
import Johnson.HB.LLHARD.K01Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Johnson.G
open VerifiableInference.Desc.K1 (realSized)

/-- OWED: the test on what is told accepts at the typed values. -/
def ToldFitOwed : Prop :=
  ∀ x : LinSized, realSized = some (x, codesFull2) →
    Second.Seam.toldFitB codesFull2 x.shape
      ((layTrees codesFull2 ((withU x.shape).getD #[])).getD default)
      ((layTrees codesFull2 (withOmega x.shape)).getD default) = true

end Desc.K14.Law
