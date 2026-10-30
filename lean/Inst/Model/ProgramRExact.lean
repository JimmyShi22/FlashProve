-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/ProgramRExact.lean: for T > 0, at the policy of exact match the relation with a policy is
"every covered token is the least token of largest logit", also without `Head3` (the request is
well-formed).
Inst/Model/ProgramR.lean (which defines the terms) has `RinfS_iff_exact` (0 < T): `RinfS` ↔ `RinfR`
at `AcceptancePolicy.exact` = (2^8, 2^8, 0), both with `Head3`. `ModelS`, `ModelR`, `RinfS0`, `RinfR0` are these
relations without it; of the two with a policy, `ModelR` and `RinfR0`, the first is the one to which
`Spec.ledger_noWrap` and `Spec.ledger_honest` (Policy/Rel/LedgerRelLaws.lean) tie the model's
conditions. Here:
    `ModelS_iff_exact`    `ModelS` ↔ `ModelR` at `AcceptancePolicy.exact`, for all weights and every instance
                          (0 < T)
    `RinfS0_iff_exact`    the same for an index: `RinfS0` ↔ `RinfR0` at `AcceptancePolicy.exact`
    `polOK_iff_of_noCnt`, `ModelR_congr_noCnt`
                          a request without a counted position (r ≥ min(e, T − 1)): the policy says
                          only clause (c), so the relation is the same under every policy
    `cnt_nextOf`, `ModelR_nextOf`
                          so on "the next token after these T tokens" the relation with a policy is
                          "y is the next token" (`ModelIsK`), whatever the policy (0 < T)
Why it holds without `Head3`: e ≤ T is in the type of an instance, and clause (c) of the policy has
the premise r < e in its own text.
What it is for: the relation at settings pp (`RinfPP0 pp`, Inst/Model/Scales.lean) is at their own
policy; the reference settings' is `AcceptancePolicy.exact`. Through these lemmas what is proved of `ModelS` and
`RinfS0` carries over to settings with exact match, and what is proved on "the next token" to all
settings.
Notation: `x : Instance P`: a request: T tokens, the announced token y, and the two numbers r, e
(Inst/Model/Program.lean); the covered positions are r ≤ t < e, the counted positions (`x.cnt`) are
the covered ones below T − 1 (Inst/Model/ProgramR.lean, the head); `i : Index P`: the type of
indices: the well-formed weights; `κ : ℕ → LayerScale`: for each layer, the scales of one layer;
`tbs : ℕ → Tables`: for each layer, the five table functions that the program reads;
`nf : NormPar`: the final normalisation (Inst/Model/Program.lean).
-/
import Inst.Model.ProgramRPol

set_option autoImplicit false

namespace Inst.Model

theorem ModelS_iff_exact (P : Params) (hT : 0 < P.T) (κ : ℕ → LayerScale) (nf : NormPar)
    (tbs : ℕ → Tables) (w : Weights) (x : Instance P) :
    ModelS P κ nf tbs w x ↔ ModelR P κ nf tbs AcceptancePolicy.exact w x := by
  constructor
  · rintro ⟨h1, h3⟩
    have hc : ∀ t ∈ x.cnt, costOf (lgK P κ nf tbs w x.prompt) x t = 2 ^ 8 := fun t ht => by
      have := Finset.mem_Ico.1 ht
      unfold costOf
      rw [h3 t this.1 (lt_of_lt_of_le this.2 (min_le_left _ _)), zero_add]
    refine ⟨h1, ⟨?_, ?_, fun hre he => ?_⟩⟩
    · rw [Finset.sum_congr rfl fun t ht => by rw [hc t ht], Finset.sum_const,
        x.card_cnt, nsmul_eq_mul]
      show (x.NB : ℤ) * min (2 ^ 8) ((2 ^ 8 : ℕ) : ℤ) ≤ ((2 ^ 8 : ℕ) : ℤ) * x.NB
      push_cast
      rw [min_self, mul_comm]
    · have hf : (x.cnt.filter fun t =>
            ((AcceptancePolicy.exact.C : ℕ) : ℤ) < costOf (lgK P κ nf tbs w x.prompt) x t) = ∅ :=
        Finset.filter_false_of_mem fun t ht => by
          rw [hc t ht]
          show ¬ (((2 ^ 8 : ℕ) : ℤ) < 2 ^ 8)
          norm_num
      rw [hf]
      exact Nat.zero_le _
    · have := h3 (P.T - 1) (by omega) (by omega)
      rwa [x.w_last hT] at this
  · rintro ⟨h1, h3⟩
    refine ⟨h1, fun t hr he => ?_⟩
    by_cases ht : t < min x.e (P.T - 1)
    · exact exact_match _ AcceptancePolicy.exact x rfl (Or.inl rfl) h3 t (Finset.mem_Ico.2 ⟨hr, ht⟩)
    · have hle := x.e_le
      have e1 : t = P.T - 1 := by
        rcases Nat.lt_or_ge t (P.T - 1) with h | h
        · exact absurd (lt_min he h) ht
        · omega
      have e2 : x.e = P.T := by omega
      rw [e1, x.w_last hT]
      exact h3.c (by omega) e2

theorem RinfS0_iff_exact (P : Params) (hT : 0 < P.T) (κ : ℕ → LayerScale) (nf : NormPar)
    (tbs : ℕ → Tables) (i : Index P) (x : Instance P) :
    RinfS0 P κ nf tbs i x ↔ RinfR0 P κ nf tbs AcceptancePolicy.exact i x :=
  ModelS_iff_exact P hT κ nf tbs i.val x

/-- Without a counted position the policy says only clause (c). -/
theorem polOK_iff_of_noCnt {P : Params} (lg : ℕ → ℕ → ℤ) (pol : AcceptancePolicy)
    (x : Instance P) (h : x.cnt = ∅) :
    PolOK lg pol x ↔ (x.r < x.e → x.e = P.T → gapOf P.V (lg (P.T - 1)) x.y.val = 0) := by
  have hN : x.NB = 0 := by rw [← x.card_cnt, h]; rfl
  refine ⟨fun hp => hp.c, fun hc => ⟨?_, ?_, hc⟩⟩
  · rw [h, hN]; simp
  · rw [h]; simp

/-- so there the relation is the same under every policy -/
theorem ModelR_congr_noCnt (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables)
    (pol pol' : AcceptancePolicy) (w : Weights) (x : Instance P) (h : x.cnt = ∅) :
    ModelR P κ nf tbs pol w x ↔ ModelR P κ nf tbs pol' w x := by
  unfold ModelR
  rw [polOK_iff_of_noCnt _ pol x h, polOK_iff_of_noCnt _ pol' x h]

theorem cnt_nextOf {P : Params} (prompt : Fin P.T → Fin P.V) (y : Fin P.V) :
    (Instance.nextOf prompt y).cnt = ∅ :=
  Finset.Ico_eq_empty (not_lt.2 (min_le_right _ _))

/-- If 0 < T: on "the next token" the relation with a policy is "y is the next token", whatever the
policy. -/
theorem ModelR_nextOf (P : Params) (hT : 0 < P.T) (κ : ℕ → LayerScale) (nf : NormPar)
    (tbs : ℕ → Tables) (pol : AcceptancePolicy) (w : Weights) (prompt : Fin P.T → Fin P.V) (y : Fin P.V) :
    ModelR P κ nf tbs pol w (Instance.nextOf prompt y) ↔ ModelIsK P κ nf tbs w prompt y.val :=
  (ModelR_congr_noCnt P κ nf tbs pol AcceptancePolicy.exact w _ (cnt_nextOf prompt y)).trans
    ((ModelS_iff_exact P hT κ nf tbs w _).symm.trans (ModelS_nextOf P hT κ nf tbs w prompt y))

end Inst.Model
