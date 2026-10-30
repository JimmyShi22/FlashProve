-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/ShapeFair.lean: A TEST WITH CODE ON A MASKED SUMCHECK's SHAPE:
WHAT SumExact.lean OF THIS FOLDER SPENDS OF THE LIBRARY's `shapeOk`
(Johnson/Desc/Part/MaskedSum4.lean), AND NO MORE. A definition, and statements with their proofs.
Main names:
  `shapeFair`: every variable has at least two coefficients; without ends there is a variable; with
    ends 1 ≤ dY. It has no clause on the number of end values and none on 65.
  `shapeFair_of_ok`: a shape that passes `shapeOk` passes it.
  `fair_vs_two`, `fair_all_two`, `fair_all_ne`: the three facts that are taken from it: on the
    shape's variables; on all variables, Y among them; that there is one, Y counted.

Limits. It is sufficient for SumExact.lean's statements. Its clause on a variable without ends is
needed (SumExactAt.lean). Its clause 1 ≤ dY, and 2 ≤ d at a variable that is summed at a point, are
not shown needed. That 2 ≤ d is needed at a plain variable is shown by no theorem here (at d = 1 the
part sends one scalar where `scalarsOf` counts none). WHERE THIS TEST ACCEPTS AND `shapeOk` REJECTS
(ends with no end value; d above 65) THE LIBRARY's OWN VERIFIER TEXT REJECTS THE CALL (`hear` asks
`shapeOk`): what the weaker test gives a caller is a premise with two clauses fewer to show. No
property of a protocol is stated.
-/
import Johnson.Desc.Part.MaskedSum4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (zeroE)
open VerifiableInference.Desc.Part.MaskedSum (Call Var shapeOk)

/-- **Every variable has at least two coefficients; without ends there is a variable; with ends
1 ≤ dY.** It is what the statements of SumExact.lean spend of the library's test on a shape. -/
def shapeFair (k : Call) : Bool :=
  (k.vs.all fun v => decide (2 ≤ v.d)) &&
    (match k.ends with
     | none => !k.vs.isEmpty
     | some e => decide (1 ≤ e.dY))

/-- A shape that passes the library's test passes this one. -/
theorem shapeFair_of_ok {k : Call} (h : shapeOk k = true) : shapeFair k = true := by
  obtain ⟨lead, vs, ends⟩ := k
  cases ends with
  | none =>
    simp only [shapeOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    simp only [shapeFair, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨fun v hv => (h.1 v hv).1, h.2⟩
  | some e =>
    simp only [shapeOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    simp only [shapeFair, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨fun v hv => (h.1 v hv).1, h.2.1⟩

/-- Every variable of the shape has at least two coefficients. -/
theorem fair_vs_two {k : Call} (h : shapeFair k = true) : ∀ v ∈ k.vs, 2 ≤ v.d := by
  simp only [shapeFair, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- Every variable, Y among them, has at least two coefficients. -/
theorem fair_all_two {k : Call} (h : shapeFair k = true) : ∀ v ∈ k.all, 2 ≤ v.d := by
  obtain ⟨lead, vs, ends⟩ := k
  cases ends with
  | none => exact fair_vs_two h
  | some e =>
    simp only [shapeFair, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    intro v hv
    have hm : v ∈ vs ++ [Var.point zeroE (e.dY + 1)] := hv
    rcases List.mem_append.1 hm with h1 | h1
    · exact h.1 v h1
    · rw [List.mem_singleton] at h1
      subst h1
      show 2 ≤ e.dY + 1
      have := h.2
      omega

/-- There is a variable, Y counted. -/
theorem fair_all_ne {k : Call} (h : shapeFair k = true) : k.all ≠ [] := by
  obtain ⟨lead, vs, ends⟩ := k
  cases ends with
  | none =>
    simp only [shapeFair, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
    exact h.2
  | some e =>
    show vs ++ [_] ≠ []
    simp

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.shapeFair
#print axioms ProofFile.Honest.SumLaw.shapeFair_of_ok
#print axioms ProofFile.Honest.SumLaw.fair_vs_two
#print axioms ProofFile.Honest.SumLaw.fair_all_two
#print axioms ProofFile.Honest.SumLaw.fair_all_ne
