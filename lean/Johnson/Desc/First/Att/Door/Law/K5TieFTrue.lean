-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5TieFTrue.lean: kind K5 (an attention segment's own rounds): THE CLOSED TEST tie, IN THE FORM FOR THE KERNEL (K5TieF.lean), SAYS YES AT ALL TWELVE GROUPS: DECIDED BY LEAN's KERNEL.

Compiled with the whole library.

(Where this and lean/THEOREM.md differ, the page holds.)

Why. The kind's named condition tie (for each of twelve groups) is asked by no test of the verifier. It has been carried to a closed term; here that is decided. "decide +kernel": the kernel evaluates the proposition's Decidable instance; the compiler's code is not trusted. That the test is not idle (five matrices a group)
is viewW_five (K5TieNotIdle.lean [not in this library]).

Main names:
  **`tiesF_true`**: tieF g at every g below 12, as one Bool. `tieF_true`: group by group.
  `tieF_bite`: a negative test: at the inverse of the numbering one higher, the test of group 0 says no.
Is it empty here? Sentences without a premise, and equations.
Limits. They speak of the written values.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5TieF

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open VerifiableInference.Desc.First.Look (idxAt sigListCalls)

set_option maxRecDepth 100000 in
/-- **At all twelve groups: yes.** -/
theorem tiesF_true : ((List.range 12).all fun g => tieF g) = true := by decide +kernel

theorem tieF_true {g : ℕ} (hg : g < 12) : tieF g = true := List.all_eq_true.1 tiesF_true g (List.mem_range.2 hg)

set_option maxRecDepth 100000 in
/-- A negative test: the inverse of the numbering one higher. -/
theorem tieF_bite :
    linkRestBy (viewW 1) sentW (sigListCalls sentW (fun _ => 0) 1) (P5T.numOfPlan P5T.seatsAllFull)
      (fun n => idxAt sentW (P5T.numOfPlan P5T.seatsAllFull) 1 n + 1) 1 = false := by decide +kernel

end H2K5.Door

#print axioms H2K5.Door.tiesF_true
#print axioms H2K5.Door.tieF_true
#print axioms H2K5.Door.tieF_bite
