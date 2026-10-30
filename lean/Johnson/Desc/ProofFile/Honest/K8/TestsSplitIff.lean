-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/TestsSplitIff.lean: THE SMALLNESS TEST: THE SPLITTING OF THE
VERIFIER's THREE TESTS BEHIND THE ADDING (Johnson/Desc/ProofFile/Honest/K8/TestsSplit.lean) THE
OTHER WAY ROUND: wherever `testsP` returns, the kind's share of them is silent and all the other
guards hold. So the splitting is an "if and only if": the share's seven tests and `K8Rest` are
together just the verifier's sixteen guards. By the library's own laws that hand each guard out
(`tests_ok`, Johnson/Desc/First/TailClaims/EquationsTests.lean; `self_all`, `rk_all`,
Johnson/Desc/First/TailClaims/EquationsSelf.lean). None of the library's goals.

  **`share_of_tests`**   testsP nU tl F = .ok Fc → k8First tl nU F = none ∧ k8Second tl F = none ∧
                   K8Rest nU tl F
  **`tests_iff`**   (∃ Fc, testsP nU tl F = .ok Fc) ↔ k8First tl nU F = none ∧ k8Second tl F = none
                   ∧ K8Rest nU tl F
Limits. On the verifier's text alone: nothing on whether an honest state meets either side.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.TestsSplit
import Johnson.Desc.First.TailClaims.EquationsTests
import Johnson.Desc.First.TailClaims.EquationsSelf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (tests_ok self_all rk_all)

/-- **Where the three tests return, the share is silent and the rest holds.** -/
theorem share_of_tests {nU : Array Nat} {tl : HTailF2} {F Fc : Fork}
    (h : testsP nU tl F = .ok Fc) :
    k8First tl nU F = none ∧ k8Second tl F = none ∧ K8Rest nU tl F := by
  obtain ⟨hs, hc, hk⟩ := tests_ok h
  obtain ⟨r1, a, r2, r3⟩ := self_all tl nU F hs
  simp only [Bool.and_eq_true] at a
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := a
  obtain ⟨g, jo, nbW, W, hg, hjo, hW, r4, r5, r6, b1, r7, c, r10, r11⟩ := rk_all tl Fc hk
  simp only [Bool.and_eq_true] at c
  obtain ⟨⟨r8, b2⟩, r9⟩ := c
  have hc' : coefficientsP tl F = .ok (coefBody tl g F) := by
    unfold coefficientsP
    rw [hg]
  obtain rfl : coefBody tl g F = Fc := Except.ok.inj (hc'.symm.trans hc)
  refine ⟨?_, ?_, r1, r2, r3, g, jo, nbW, W, hg, hjo, hW, r4, r5, r6, r7, r8, r9, r10, r11⟩
  · simp only [k8First, a1, a2, a3, a4, a5, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  · unfold k8Second
    rw [hc', hg, hjo, hW]
    simp only [b1, b2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- **The splitting, both ways.** -/
theorem tests_iff {nU : Array Nat} {tl : HTailF2} {F : Fork} :
    (∃ Fc, testsP nU tl F = .ok Fc) ↔
      k8First tl nU F = none ∧ k8Second tl F = none ∧ K8Rest nU tl F :=
  ⟨fun ⟨_, h⟩ => share_of_tests h, fun ⟨h1, h2, R⟩ => tests_of_share h1 h2 R⟩

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.share_of_tests
#print axioms ProofFile.Honest.K8.tests_iff
