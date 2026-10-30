-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PlanOfLaid.lean: `WrittenAt Zp` AND `XNine` FROM THE HEAD's OWN FIELDS. Over the
entry tests' list of thirteen rows the laid value's tests hold two pins; `pins_of_laid`
(Johnson/Goal/Skeleton/PinsOfLaid.lean) draws their accepts out of `LaidAt`, in the goals' scope.
With `written_at_in_scope` (through Johnson/Road/K4/K4PlanInScope.lean) that gives
`WrittenAt Zp`: so the five equations are no condition of their own any more. Three theorems: calls.

  `laidPOf_of_laidAt`: `LaidAt` gives back "the value is laid" (the converse `laidPOf_of`).
  `writtenAt_of_laid`: in scope, from `LaidAt`: `WrittenAt Zp`.
  `xNine_of_head`: with publicOf's return, the public core and the head's test `laidThere`:
    `XNine Zp.p.X`.

Limits. K04_law IS NOT PROVED BY THIS. IT NEEDS THE TWO PINS AMONG THE VERIFIER's ENTRY TESTS (rows
9 and 10 of `LPFD.lawsAsk`, Johnson/Desc/Laid/ProofAsks.lean: fourteen rows in this tree): an
earlier list of eight rows held no such pin. That `LaidAt` can be met is shown by no
theorem. `laidThere` stays a named test of the head.
-/
import Johnson.Road.K4.K4PlanInScope
import Johnson.Road.K4.NineInScope
import Johnson.Goal.Skeleton.PinsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes.Model.Verify (publicOf)
open OnBytes.Maker (WholeD)
open P5J (F0T LaidAt TS)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}

/-- `LaidAt` gives back that the value is laid. -/
theorem laidPOf_of_laidAt (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    LPFD.Full.proofDataAndDecisionOfPublicFiles o Z.pol Z.lay Z.KL = .ok (D, r) := by
  rw [L.run]
  exact LPFD.Full.laidPOf_of L.value L.planOk L.data L.asks

/-- **In scope, where the value is laid, five parts of Zp are the written values.** -/
theorem writtenAt_of_laid (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) : WrittenAt Zp :=
  writtenAt_in_scope hZ L.pub (P5J.pins_of_laid hZ L).1 (laidPOf_of_laidAt L)

/-- **`XNine` from the head's own fields.** -/
theorem xNine_of_head {pol KL : ByteArray} {lay : Option ByteArray} (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) (h : publicOf pol KL lay = .ok Zp.p.X)
    (C : Hd.PublicCore Zp.p.X.P)
    (T : Meaning.laidThere Zp.p.X (Meaning.sizesOf Zp.p.X) Zp.first.layout = true) :
    XNine Zp.p.X :=
  xNine_of_laid h C (writtenAt_of_laid hZ L).layout T

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.laidPOf_of_laidAt
#print axioms OnBytes.Road.K4.writtenAt_of_laid
#print axioms OnBytes.Road.K4.xNine_of_head
