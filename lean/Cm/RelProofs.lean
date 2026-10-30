-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/RelProofs.lean: lemmas on Cm/Rel.lean.

Main names:
  `below_129_iff`: `Below 129` is `All.Small128` (cells at most 128).
  `modelR_iff_modelS`: at a policy of exact match "the program runs and the policy holds" is "the
    program runs and every covered token has gap 0", for any weights, with or without the request's
    form.

Limits: what the head of Cm/Rel.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cm.Rel

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm

open Inst.Model Inst.Model.All
open Inst.Model.Layout (kRef hRef)

/-! ## Bounds -/

theorem Below.mono {B B' : ℤ} (h : B ≤ B') {T : Trace} (b : Below B T) : Below B' T :=
  ⟨b.toBelowL.mono h,
    fun i hi φ hφ => lt_of_lt_of_le (b.hf i hi φ hφ) h,
    fun i hi φ hφ => lt_of_lt_of_le (b.hd i hi φ hφ) h,
    fun i hi φ hφ => lt_of_lt_of_le (b.hr i hi φ hφ) h⟩

theorem below_129_iff (T : Trace) : Below 129 T ↔ Small128 T :=
  ⟨fun b =>
      ⟨fun g hg c hc => Int.lt_add_one_iff.1 (b.ff g hg c hc),
        fun g hg c hc => Int.lt_add_one_iff.1 (b.att g hg c hc),
        fun i hi φ hφ => Int.lt_add_one_iff.1 (b.hf i hi φ hφ),
        fun i hi φ hφ => Int.lt_add_one_iff.1 (b.hd i hi φ hφ),
        fun i hi φ hφ => Int.lt_add_one_iff.1 (b.hr i hi φ hφ)⟩,
    fun s =>
      ⟨⟨fun g hg c hc => Int.lt_add_one_iff.2 (s.ff g hg c hc),
          fun g hg c hc => Int.lt_add_one_iff.2 (s.att g hg c hc)⟩,
        fun i hi φ hφ => Int.lt_add_one_iff.2 (s.hf i hi φ hφ),
        fun i hi φ hφ => Int.lt_add_one_iff.2 (s.hd i hi φ hφ),
        fun i hi φ hφ => Int.lt_add_one_iff.2 (s.hr i hi φ hφ)⟩⟩

/-! ## The policies of exact match -/

theorem modelR_iff_modelS {pol : AcceptancePolicy} (hE : ExactPol pol) (κ : ℕ → LayerScale) (nf : NormPar)
    (tbs : ℕ → Tables) (w : Weights) (x : Instance ppref) :
    ModelR ppref κ nf tbs pol w x ↔ ModelS ppref κ nf tbs w x := by
  have hT : 0 < ppref.T := by decide
  obtain ⟨hθ, hC, hc⟩ := hE
  constructor
  · rintro ⟨h1, h3⟩
    refine ⟨h1, fun t hr he => ?_⟩
    by_cases ht : t < min x.e (ppref.T - 1)
    · exact exact_match _ pol x hθ hc h3 t (Finset.mem_Ico.2 ⟨hr, ht⟩)
    · have hle := x.e_le
      have e1 : t = ppref.T - 1 := by
        rcases Nat.lt_or_ge t (ppref.T - 1) with h | h
        · exact absurd (lt_min he h) ht
        · omega
      have e2 : x.e = ppref.T := by omega
      rw [e1, x.w_last hT]
      exact h3.c (by omega) e2
  · rintro ⟨h1, h3⟩
    have hc8 : ∀ t ∈ x.cnt, costOf (lgK ppref κ nf tbs w x.prompt) x t = 2 ^ 8 := fun t ht => by
      have := Finset.mem_Ico.1 ht
      unfold costOf
      rw [h3 t this.1 (lt_of_lt_of_le this.2 (min_le_left _ _)), zero_add]
    have hC' : (2 : ℤ) ^ 8 ≤ (pol.C : ℤ) := by exact_mod_cast hC
    have hθ' : (pol.theta : ℤ) = 2 ^ 8 := by rw [hθ]; norm_num
    refine ⟨h1, ⟨?_, ?_, fun hre he => ?_⟩⟩
    · have hs : ∑ t ∈ x.cnt, min (costOf (lgK ppref κ nf tbs w x.prompt) x t) (pol.C : ℤ) =
          ∑ _t ∈ x.cnt, (2 : ℤ) ^ 8 :=
        Finset.sum_congr rfl fun t ht => by rw [hc8 t ht, min_eq_left hC']
      rw [hs, Finset.sum_const, x.card_cnt, nsmul_eq_mul, hθ']
      exact le_of_eq (mul_comm _ _)
    · have hf : (x.cnt.filter fun t => (pol.C : ℤ) < costOf (lgK ppref κ nf tbs w x.prompt) x t) =
          ∅ :=
        Finset.filter_false_of_mem fun t ht => by rw [hc8 t ht]; exact not_lt.2 hC'
      rw [hf]
      exact Nat.zero_le _
    · have := h3 (ppref.T - 1) (by omega) (by omega)
      rwa [x.w_last hT] at this

end Cm
