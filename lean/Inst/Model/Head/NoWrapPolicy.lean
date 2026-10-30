-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/NoWrapPolicy.lean: the acceptance policy in the head segment: bytes, the counted
positions and the margin of a trace. From a trace that satisfies the field relation of the head to
the policy's three clauses: Policy/Rel/LedgerHeadNoWrap.lean.

(The relation on a request under a policy is in Inst/Model/ProgramR.lean. The margin of a counted
position contains a hidden number.)
  `b256_range`
      n bytes, read in base 256, give a number in [0, 256^n)
  `sum_rhoC`
      a sum over all positions with the mask of the counted positions is the sum over these
  `N.ex_eq`, `N.mg_marg`
      ex as a sum of its cells; at a covered position the margin of the trace is the margin of the
      relations

Notation:
  `AcceptancePolicy` (Inst/Model/ProgramR.lean): the three numbers of the acceptance policy: the clip (C), the
    bound on the mean cost (θ), the limit on the number of positions above the clip (cap).
Limits. This file does not say that the logits of the cells are the integer program's (that is
`lg_stream`, Policy/Rel/LedgerHeadNoWrap.lean). It says nothing on the protocol.
(Words of this library: lean/GLOSSARY.md.)
-/
import Inst.Model.Head.NoWrapN
import Inst.Model.Head.PolicyNoWrap
import Inst.Model.Head.PolicyRead

set_option autoImplicit false

namespace Inst.Model.Head

open Finset

/-- n bytes, read in base 256, give a number in [0, 256^n) -/
theorem b256_range (D : ℕ → ℤ) (a : ℕ) :
    ∀ n : ℕ, (∀ l < n, 0 ≤ D (a + l) ∧ D (a + l) < 256) →
      0 ≤ Ledger.b256 D a n ∧ Ledger.b256 D a n < 256 ^ n
  | 0, _ => by simp [Ledger.b256]
  | n + 1, hD => by
    have ih := b256_range D a n fun l hl => hD l (by omega)
    have d := hD n (by omega)
    have p : (0 : ℤ) < 256 ^ n := by positivity
    have m0 : 0 ≤ 256 ^ n * D (a + n) := mul_nonneg p.le d.1
    have m1 : 256 ^ n * D (a + n) ≤ 256 ^ n * 255 := mul_le_mul_of_nonneg_left (by omega) p.le
    rw [Ledger.b256_succ, pow_succ]
    constructor <;> linarith

/-- a sum over all positions with the mask of the counted positions is the sum over these -/
theorem sum_rhoC (pol : AcceptancePolicy) (x : Instance ppref) (f : ℕ → ℤ) :
    ∑ i ∈ range nT, (Req.of pol x).rhoC i * f i = ∑ i ∈ x.cnt, f i := by
  have hsub : x.cnt ⊆ range nT := fun i hi => by
    have h1 := Finset.mem_Ico.1 hi
    have h2 : ppref.T - 1 = 1023 := rfl
    rw [h2] at h1
    exact mem_range.2 (by unfold nT; omega)
  rw [← sum_subset hsub fun i _ hn => by rw [Req.rhoC_of, if_neg hn, zero_mul]]
  exact sum_congr rfl fun i hi => by rw [Req.rhoC_of, if_pos hi, one_mul]

namespace N

section
variable {t : Cells ℤ}

theorem ex_eq (v i : ℕ) :
    ex t v i =
      8421505 + (t.hf (fEx 0 v) i + 256 * t.hf (fEx 1 v) i + 65536 * t.hf (fEx 2 v) i) := by
  simp [ex, rd, sum_range_succ]

end

section
variable {H : Mat} {pol : AcceptancePolicy} {x : Instance ppref} {t : Cells ℤ}

/-- at a covered position the margin of the trace is the margin of the relations -/
theorem mg_marg {i : ℕ} (hr : x.r ≤ i) (he : i < x.e) (v : ℕ) :
    mg t H (Req.of pol x) v i = Policy.marg (fun i v => lg t H i v) x (hidOf t) i v := by
  have h1 : (Req.of pol x).rho i = 1 := by
    unfold Req.rho
    exact if_pos ⟨hr, he⟩
  have h2 : (Req.of pol x).rhoC i = Policy.rhoC x i := Req.rhoC_of pol x i
  unfold mg Policy.marg
  rw [h1, h2]
  show ((1 : ℤ) : ℤ) * (lg t H i (x.w i) - lg t H i v - if v < x.w i then 1 else 0) +
      ((Policy.rhoC x i : ℤ) : ℤ) * (hidC t i + 2 ^ 37 * hidB t i) = _
  simp only [hidOf]
  ring

end

end N

end Inst.Model.Head
