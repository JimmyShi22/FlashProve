-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ReadsTestsAtHead.lean: THE TWO CLOSED TESTS THAT STAND IN FRONT OF THE READING LAW AT THE FIRST CHAIN's BORDERS (the fields seat and below of ReadsTests, Johnson/P5J/ReadsOfHead.lean; the premises hseat and hbelow of Johnson/P5J/ReadsOwedAt.lean) ARE THEOREMS UNDER THE HEAD.
 THE ROAD (that of Johnson/P5J/StartAtHead.lean): where the verifier's value is laid the two pins accept: so the planner's sendings, the codes, and what the first chain's sub-protocols tell ARE THE WRITTEN ONES; at these each test is a closed Bool: by Lean's kernel, each with a twin that must fail.
  P5J.index_at_head   (At.N Zp cF).index = (1, 0): the index masks' seat.
  P5J.laid_at_head    At.laid? Zp = some LFull: laid_in_scope (Johnson/HB/LLHARD/PlanInScope.lean): called, not typed anew.
  P5T.seatFull (BY THE KERNEL)  the written list of seats has (1, 0) at the number msgNoOf toldCut (1, 0) · seatFull_control: A NEGATIVE TEST: one number higher: not that seat.
  P5T.belowFull (BY THE KERNEL) planBelowB LFull 358 toldCut = true · belowFull_control: A NEGATIVE TEST: every seat's tree one higher: it rejects. ("Nothing told" would be an empty bend: no seat below no tree.)
  **P5J.seat_at_head · P5J.below_at_head (h : AtMg OnBytes.secondHashFunction …): THE TWO FIELDS, TO THE LETTER.**
Limits. The head is a premise. At OnBytes.secondHashFunction. The full size alone. The written values rest on their files' own heads. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.StartAtHead
import Johnson.HB.LLHARD.PlanInScope
import Johnson.Desc.K13.Law.PlanTestsM3

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5T
open VerifiableInference.Desc.First (msgNoOf toldCut)
open VerifiableInference.Desc.K13.Law (LFull planBelowB)

set_option maxRecDepth 1000000 in
theorem seatFull : LFull.places[msgNoOf toldCut (1, 0)]? = some (1, 0) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one number higher. -/
theorem seatFull_control : LFull.places[msgNoOf toldCut (1, 0) + 1]? ≠ some (1, 0) := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem belowFull : planBelowB LFull 358 toldCut = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: every seat's tree one higher. -/
theorem belowFull_control :
    planBelowB { LFull with places := LFull.places.map fun p => (p.1 + 1, p.2) } 358 toldCut =
      false := by decide +kernel

end P5T

namespace P5J
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc.K13.Law (LFull planBelowB)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl}

/-- **The index masks' seat at the head.** -/
theorem index_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) : (At.N Zp cF).index = (1, 0) := by
  obtain ⟨c1, e2⟩ := written_at_head h
  show (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).index = _
  rw [P5T.planSeats_at]
  unfold P5T.planSeatsAt
  rw [c1, e2, P5T.index_of_startE _ _ _ P5T.startE_full]
  rfl

/-- **The list of seats at the head is the written one.** -/
theorem laid_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) : At.laid? Zp = some LFull :=
  VerifiableInference.Desc.K13.Law.laid_in_scope h.scope h.laid.pub (pins_of_laid h.scope h.laid).1

/-- **THE FIELD seat.** -/
theorem seat_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∀ L, At.laid? Zp = some L → L.places[(At.N Zp cF).indexNo]? = some (At.N Zp cF).index := by
  intro L hL
  obtain rfl : LFull = L := Option.some.inj ((laid_at_head h).symm.trans hL)
  rw [indexNo_at_head h, index_at_head h]
  exact P5T.seatFull

/-- **THE FIELD below.** -/
theorem below_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∀ L, At.laid? Zp = some L → planBelowB L At.ps.length (At.told cF) = true := by
  intro L hL
  obtain rfl : LFull = L := Option.some.inj ((laid_at_head h).symm.trans hL)
  have e : At.ps.length = 358 := by decide +kernel
  rw [told_at_head h, e]
  exact P5T.belowFull

end P5J

#print axioms P5T.seatFull
#print axioms P5T.seatFull_control
#print axioms P5T.belowFull
#print axioms P5T.belowFull_control
#print axioms P5J.index_at_head
#print axioms P5J.laid_at_head
#print axioms P5J.seat_at_head
#print axioms P5J.below_at_head
