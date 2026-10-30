-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5PlansFTrue.lean: kind K5 (an attention segment's own rounds): THE CLOSED TESTS ON THE SEATS AND ON THE SHAPES, IN THE FORM FOR THE KERNEL (K5PlansF.lean), SAY YES AT ALL TWELVE GROUPS: DECIDED BY LEAN's KERNEL.

Compiled with the whole library.

(Where this and lean/THEOREM.md differ, the page holds.)

Why. Two of the kind's named conditions on public data (seatsPlan · shapesPlan, for each of twelve groups), and a third through the first (sent), are asked by no test of the verifier. They have been carried to closed terms; here these are decided. "decide +kernel": the kernel evaluates the proposition's Decidable instance; the compiler's code is not trusted.

Main names:
  **`plansF_true`**: seatsAllF g and shapesAllF g at every g below 12, as one Bool.
  `seatsAllF_true`, `shapesAllF_true`: group by group.
  `plansF_bite`: a negative test: at the listed seats without their first, the test on the seats of group 0 says no.
Is it empty here? Sentences without a premise, and equations.
Limits. They speak of the written values.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5PlansF

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door

set_option maxRecDepth 100000 in
/-- **At all twelve groups: yes.** -/
theorem plansF_true : ((List.range 12).all fun g => seatsAllF g && shapesAllF g) = true := by decide +kernel

theorem seatsAllF_true {g : ℕ} (hg : g < 12) : seatsAllF g = true :=
  (Eq.mp (Bool.and_eq_true _ _) (List.all_eq_true.1 plansF_true g (List.mem_range.2 hg))).1

theorem shapesAllF_true {g : ℕ} (hg : g < 12) : shapesAllF g = true :=
  (Eq.mp (Bool.and_eq_true _ _) (List.all_eq_true.1 plansF_true g (List.mem_range.2 hg))).2

set_option maxRecDepth 100000 in
/-- A negative test: the listed seats without their first. -/
theorem plansF_bite : seatsAtF 0 { VerifiableInference.Desc.K13.Law.LFull with places := VerifiableInference.Desc.K13.Law.LFull.places.drop 1 } = false := by decide +kernel

end H2K5.Door

#print axioms H2K5.Door.plansF_true
#print axioms H2K5.Door.seatsAllF_true
#print axioms H2K5.Door.shapesAllF_true
#print axioms H2K5.Door.plansF_bite
