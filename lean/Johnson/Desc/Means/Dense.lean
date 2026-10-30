-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Means/Dense.lean: THE VERIFIER's TESTS ON A TENSOR AND ON A FORM (`tensorInOrder`,
`formFits`, Johnson/Desc/Own/Shapes.lean) AGAINST `DenseTensor` | `DenseForm` | `DenseRow`
(OnBytes/Slice/BlkProxDense.lean): of a tensor and of a form each way, of a row from the tests. The
statements name no sub-protocol, no chain and no prover.

  `denseTensor_of_test`, `test_of_denseTensor`   a tensor that passes the test on a tensor is
      dense; a dense tensor of at most 63 variables passes it.
  `formFits_of_dense`   tensors of n variables, single entries below 2^n (`CFits n f`,
      Johnson/Desc/Means/Shape.lean, written out), dense, n at most 63: the form passes `formFits`.
  `denseForm_of_fits`   a form that passes the test is dense.
  `denseRow_of_tests`   a row whose terms pass the test on a tensor and whose whole coefficient
      vectors pass the test on a form is dense.

Limits. `formFits_of_dense` goes one way; back comes `DenseForm`, not the bound on n. That the test
on a tensor also gives "at most 63 variables" is not stated here. Kin: the tests' meanings as
sentences (`tensorInOrder_iff`, `formFits_iff`, Johnson/Desc/Own/ShapesMean.lean) and `formFits_of`
(Johnson/Desc/K10/Honest/RowFits.lean), which ends as `formFits_of_dense`
does, from `All Own.InOrder`; no theorem here ties the predicates. Nothing on completeness, on
soundness or on
what is hidden.

-/
import OnBytes.Slice.BlkProxDense
import Johnson.Desc.Own.Shapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means
open OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc.Own (tensorInOrder formFits)

/-- A tensor that passes the verifier's own test on a tensor is dense. -/
theorem denseTensor_of_test {v : Tensor} (h : tensorInOrder v = true) : DenseTensor v := by
  unfold tensorInOrder at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq, List.isEmpty_iff] at h
  obtain ⟨⟨⟨_, h2⟩, h3⟩, h4⟩ := h
  exact ⟨⟨h4, h3⟩, h2⟩

/-- And it gives the test, at a tensor of at most 63 variables. -/
theorem test_of_denseTensor {v : Tensor} (h : DenseTensor v) (hn : v.pairs.length ≤ 63) :
    tensorInOrder v = true := by
  unfold tensorInOrder
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq, List.isEmpty_iff]
  exact ⟨⟨⟨hn, h.2⟩, h.1.2⟩, h.1.1⟩

/-- **A dense form (`DenseForm`) whose tensors have n variables and whose single entries lie below
2^n passes the verifier's test on a form**, for n at most 63. -/
theorem formFits_of_dense {f : Form} {n : Nat}
    (hc : (∀ v ∈ f.tensors, v.vars = n) ∧ ∀ e ∈ f.entries, e.1 < 2 ^ n) (hd : DenseForm f)
    (hn : n ≤ 63) : formFits f n = true := by
  unfold formFits
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun v hv => ?_, fun e he => decide_eq_true (hc.2 e he)⟩
  have h1 : v.pairs.length = n := hc.1 v hv
  rw [Bool.and_eq_true]
  exact ⟨by simpa using h1, test_of_denseTensor (hd v hv) (by rw [h1]; exact hn)⟩

/-- A form that passes the verifier's test on a form is dense. -/
theorem denseForm_of_fits {f : Form} {n : Nat} (h : formFits f n = true) : DenseForm f := by
  unfold formFits at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  intro v hv
  have := h.1 v hv
  rw [Bool.and_eq_true] at this
  exact denseTensor_of_test this.2

/-- A row whose terms pass the test on a tensor and whose whole coefficient vectors pass the test on
a form is dense. -/
theorem denseRow_of_tests {r : OnBytes.Row}
    (h1 : ∀ t ∈ r.terms.toList, tensorInOrder t.v = true)
    (h2 : ∀ f ∈ r.forms.toList, ∃ n, formFits f.c n = true) : DenseRow r :=
  ⟨fun t ht => denseTensor_of_test (h1 t ht), fun f hf => by
    obtain ⟨n, hn⟩ := h2 f hf
    exact denseForm_of_fits hn⟩

end OnBytes.Means

#print axioms OnBytes.Means.denseTensor_of_test
#print axioms OnBytes.Means.test_of_denseTensor
#print axioms OnBytes.Means.formFits_of_dense
#print axioms OnBytes.Means.denseForm_of_fits
#print axioms OnBytes.Means.denseRow_of_tests
