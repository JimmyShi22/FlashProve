-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumHon.lean: proofs of `Spec.ld_sum_run` and `Spec.ld_sum_rounds` (Cb/Ld/LdSum.lean): what
the honest prover of the zero-knowledge sumcheck sends.
`Spec.ld_sum_rounds` (for 2 ≤ n): the honest prover's first scalar is the sum of U over the cube,
and its round polynomials are those of the summand U + ε (claim polynomial). `Spec.ld_sum_run`: what
the honest prover sends in a run is its closed form at the run's challenges.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).
Also: sums over a cube of h + g variables split (`sum_cube_add`, `sum_eqk_add`), and the kernel
`Alg.eqk` factors (`eqk_add`); the carried mask, read as a table on the whole cube
(`SumPar.sCl_tab`, `SumPar.sBl_tab`).
-/
import Cb.Ld.LdSumRun

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

section Cube
variable {E : Type} [Field E] {h g : ℕ}

theorem sum_cube_add {N : Type} [AddCommMonoid N] (f : (Fin h → Bool) → (Fin g → Bool) → N) :
    ∑ b : Fin (h + g) → Bool, f (fun i => b (Fin.castAdd g i)) (fun t => b (Fin.natAdd h t)) =
      ∑ b', ∑ b'', f b' b'' := by
  rw [← Fintype.sum_prod_type', ← (Fin.appendEquiv h g).sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Fin.appendEquiv]

theorem eqk_add (z : Fin (h + g) → E) (b : Fin (h + g) → Bool) :
    Alg.eqk z b =
      Alg.eqk (fun i => z (Fin.castAdd g i)) (fun i => b (Fin.castAdd g i)) *
        Alg.eqk (fun t => z (Fin.natAdd h t)) (fun t => b (Fin.natAdd h t)) := by
  simp [Alg.eqk, Fin.prod_univ_add]

theorem sum_eqk_add (z : Fin (h + g) → E) (F : (Fin h → Bool) → E) (G : (Fin g → Bool) → E) :
    ∑ b, Alg.eqk z b * (F (fun i => b (Fin.castAdd g i)) * G fun t => b (Fin.natAdd h t)) =
      (∑ b', Alg.eqk (fun i => z (Fin.castAdd g i)) b' * F b') *
        ∑ b'', Alg.eqk (fun t => z (Fin.natAdd h t)) b'' * G b'' := by
  rw [Finset.sum_mul_sum,
    ← sum_cube_add fun b' b'' =>
      Alg.eqk (fun i => z (Fin.castAdd g i)) b' * F b' *
        (Alg.eqk (fun t => z (Fin.natAdd h t)) b'' * G b'')]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [eqk_add]
  ring

theorem sum_all_true (w : (Fin g → Bool) → E) :
    ∑ b'', w b'' * ∏ t : Fin g, (if b'' t then (1 : E) else 0) = w fun _ => true := by
  rw [Finset.sum_eq_single fun _ => true]
  · simp
  · intro b _ hb
    obtain ⟨t, ht⟩ := Function.ne_iff.1 hb
    rw [Finset.prod_eq_zero (Finset.mem_univ t) (by simp at ht; simp [ht]), mul_zero]
  · simp

end Cube

namespace SumPar
variable {E P : Type} [Field E] [Fintype E] (Y : SumPar E P)

omit [Fintype E] in
/-- the claim polynomial of the two tables on the whole cube is the one of the protocol -/
theorem sCl_tab (x : Y.Xi) (m : Y.Cin.J → E) (γ : HPt Y.vars) :
    sCl Y.n Y.k (Y.tabL x) (Y.tabM m) γ =
      ∑ c, Y.sl.fix (x.2.1, sPt Y.n Y.k γ) c * foldV (sPt Y.n Y.k γ) (fun a => m (.inl a)) c +
        (∑ c, Y.slS.fix (x.2.2, Y.pre (sPt Y.n Y.k γ)) c *
            foldV (Y.pre (sPt Y.n Y.k γ)) (fun a => m (.inr a)) c) *
          Y.late (sPt Y.n Y.k γ) := by
  unfold sCl
  rw [Fintype.sum_sum_type, Finset.sum_mul]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun c _ => ?_) (Finset.sum_congr rfl fun c _ => ?_)
  · refine congrArg₂ (· * ·) (Finset.sum_congr rfl fun b _ => mul_comm _ _) rfl
  · have h1 := sum_eqk_add (sPt Y.n Y.k γ) (fun b' => Y.slS x.2.2 (b', c)) fun b'' =>
      ∏ t : Fin Y.g, if b'' t then (1 : E) else 0
    have h2 := sum_eqk_add (sPt Y.n Y.k γ) (fun b' => m (.inr (b', c))) fun _ => (1 : E)
    rw [sum_all_true] at h1
    simp only [mul_one, Alg.sum_eqk] at h2
    show (∑ b, Alg.eqk (sPt Y.n Y.k γ) b *
          (Y.slS x.2.2 (fun i => b (Fin.castAdd Y.g i), c) *
            ∏ t : Fin Y.g, if b (Fin.natAdd Y.h t) then (1 : E) else 0)) *
        (∑ b, Alg.eqk (sPt Y.n Y.k γ) b * m (.inr (fun i => b (Fin.castAdd Y.g i), c))) = _
    rw [h1, h2]
    have h3 : Alg.eqk (fun t => sPt Y.n Y.k γ (Fin.natAdd Y.h t)) (fun _ => true) =
        Y.late (sPt Y.n Y.k γ) := by
      simp [Alg.eqk, late]
    rw [h3]
    have h4 : ∑ b', Alg.eqk (fun i => sPt Y.n Y.k γ (Fin.castAdd Y.g i)) b' * Y.slS x.2.2 (b', c) =
        Y.slS.fix (x.2.2, Y.pre (sPt Y.n Y.k γ)) c :=
      Finset.sum_congr rfl fun b _ => mul_comm _ _
    rw [h4]
    show _ * _ * foldV (Y.pre (sPt Y.n Y.k γ)) (fun a => m (.inr a)) c = _
    ring

omit [Fintype E] in
/-- the pairing of the two tables is the value of the input form -/
theorem sBl_tab (x : Y.Xi) (m : Y.Cin.J → E) :
    sBl (Y.tabL x) (Y.tabM m) = ∑ j, Y.slIn x.2 j * m j := by
  unfold sBl
  simp only [Fintype.sum_sum_type, Finset.sum_add_distrib]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine congrArg₂ (· + ·) rfl ?_
  have h := sum_cube_add (h := Y.h) (g := Y.g) fun b' b'' =>
    ∑ c, Y.slS x.2.2 (b', c) * (∏ t : Fin Y.g, if b'' t then (1 : E) else 0) * m (.inr (b', c))
  refine h.trans (Finset.sum_congr rfl fun b' _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h5 := sum_all_true (g := Y.g) fun _ => Y.slS x.2.2 (b', c) * m (.inr (b', c))
  refine Eq.trans (Finset.sum_congr rfl fun b'' _ => ?_) h5
  ring

theorem honQ_causal (w : Y.Cin.N.Wit) (x : Y.Xi) (W : HIdx Y.vars → E) (ε : E) :
    SCausal Y.n Y.k (Y.honQ w x W ε) :=
  SCausal.add_mul Y.n Y.k ε (hTr_causal Y.n Y.k 0 W) (sTr_causal Y.n Y.k _ _)

theorem honQ_rounds (hn : 2 ≤ Y.n) (w : Y.Cin.N.Wit) (x : Y.Xi) (W : HIdx Y.vars → E)
    (ε : E) (γ : HPt Y.vars) :
    HRounds Y.vars (Y.summand w x W ε) (Y.honQ w x W ε γ) γ := by
  have h1 := hRounds_U Y.vars (sVars_ok Y.n (by omega) Y.k) (0 : E) W γ
  have h2 := sTr_rounds Y.n hn Y.k (Y.tabL x) (Y.tabM w.1) γ
  refine HRounds.congr Y.vars (fun z => ?_) (HRounds.add_smul Y.vars ε h1 h2)
  rw [sCl_tab, smul_zero, zero_add]
  rfl

/-- the sum of the summand -/
theorem summand_sum (hn : 2 ≤ Y.n) (w : Y.Cin.N.Wit) (x : Y.Xi) (W : HIdx Y.vars → E) (ε : E) :
    hSumAll Y.vars (Y.summand w x W ε) = hMu Y.vars W + (∑ j, Y.slIn x.2 j * w.1 j) * ε := by
  have e : Y.summand w x W ε =
      fun z =>
        (hPsi Y.vars z • (0 : E) + hU Y.vars W z) + ε • sCl Y.n Y.k (Y.tabL x) (Y.tabM w.1) z := by
    funext z
    rw [sCl_tab, smul_zero, zero_add]
    rfl
  rw [e, hSumAll_add_smul, hSumAll_U Y.vars (sVars_ok Y.n (by omega) Y.k), sCl_sum, sBl_tab,
    zero_add, smul_eq_mul, mul_comm]

end SumPar

theorem ld_sum_rounds (E P : Type) [Field E] [Fintype E] : Spec.ld_sum_rounds E P := by
  intro Y hn w x W ε γ
  refine ⟨?_, Y.honQ_rounds hn w x W ε γ⟩
  have h := hSumAll_U Y.vars (sVars_ok Y.n (by omega) Y.k) (0 : E) W
  simpa using h

theorem ld_sum_run (E P : Type) [Field E] [Fintype E] : Spec.ld_sum_run E P := by
  intro Y w x c ρ
  obtain ⟨i1, i2, i3⟩ := sStrat_run Y.val Y.n Y.k (Y.honQ w x c.1 (Y.val ρ.1))
    (Y.honEnd w x c (Y.val ρ.1)) (Y.honQ_causal w x c.1 _) ρ.2
  exact ⟨i1, rfl, Prod.ext rfl i2, i3⟩

end Cb
