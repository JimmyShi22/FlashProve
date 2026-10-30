-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdPscProofs.lean: proofs for Cb/Ld/LdPsc.lean, first part: round polynomials of any summand;
the honest prover's run; the rounds of the variables (the main step of knowledge soundness).
The other parts: Cb/Ld/LdPscProofsIor.lean (completeness, the whole block),
Cb/Ld/LdPscProofsOur.lean.

Main names:
  `psc_trOf`, `psc_cons`: round polynomials of a summand with degrees.
  `hev_roots_val`: a non-zero polynomial with n + 1 coefficients vanishes at no more than n
    challenges, if different challenges have different values (`hv`).
  `pDoomed`: the sumcheck argument, for any list of variables in which different challenges have
    different values, and any summand that has round polynomials: a false claimed sum stays false
    but for n_j challenges in round j.
  `psc_rounds`, `psc_run`: the honest prover.
  `psc_core_sound_at`: the main step for round 0 and the rounds of the variables, as stated in
    Cb/Ld/LdPsc.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdPsc
import Cb.Ld.LdSumRun
import Alg.Poly
import Prob.Bias

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

section Summand
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

theorem hev_fsum {n : ℕ} {S : Type} [Fintype S] (a : S → R) (c : S → Fin (n + 1) → M) (x : R) :
    hev (fun t => ∑ s, a s • c s t) x = ∑ s, a s • hev (c s) x := by
  simp only [hev, Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => smul_comm _ _ _

/-- a sum over later variables of polynomials in x is a polynomial in x -/
theorem psc_hSumAll_poly {n : ℕ} :
    ∀ (l : List (HVar R)) (g : R → HPt l → M),
      (∀ xs, ∃ c : Fin (n + 1) → M, ∀ x, g x xs = hev c x) →
      ∃ c : Fin (n + 1) → M, ∀ x, hSumAll l (g x) = hev c x := by
  intro l
  induction l with
  | nil => intro g h; exact h ()
  | cons v l ih =>
      intro g h
      have h' : ∀ s : v.S,
          ∃ c : Fin (n + 1) → M, ∀ x, hSumAll l (fun xs => g x (v.node s, xs)) = hev c x :=
        fun s => ih (fun x xs => g x (v.node s, xs)) fun xs => h (v.node s, xs)
      choose c hc using h'
      refine ⟨fun t => ∑ s, v.wt s • c s t, fun x => ?_⟩
      rw [hev_fsum]
      exact Finset.sum_congr rfl fun s _ => by rw [← hc s x]

theorem hCo_spec {n : ℕ} {g : R → M} (h : ∃ c : Fin (n + 1) → M, ∀ x, g x = hev c x) (x : R) :
    hev (hCo n g) x = g x := by
  unfold hCo
  rw [dif_pos h]
  exact (h.choose_spec x).symm

theorem psc_trOf : Spec.psc_trOf R M := by
  intro l
  induction l with
  | nil => intro _ _ _; trivial
  | cons v l ih =>
      intro f γ h
      exact ⟨fun x => hCo_spec (psc_hSumAll_poly l (fun x xs => f (x, xs)) h.1) x, ih _ _ (h.2 γ.1)⟩

theorem psc_cons : Spec.psc_cons R M := hRounds_cons

theorem psc_hU_zero (l : List (HVar R)) (γ : HPt l) : hU l (0 : HIdx l → M) γ = 0 := by
  rw [hide_form R M l 0 γ]
  simp

theorem psc_hMu_zero (l : List (HVar R)) : hMu l (0 : HIdx l → M) = 0 := by
  have h := hMu_add l (0 : HIdx l → M) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

/-- each round's part does not depend on later challenges -/
def HCausal : (l : List (HVar R)) → (HPt l → RIdx l → M) → Prop
  | [], _ => True
  | _ :: l, q =>
    (∀ γ γ' t, q γ (.inl t) = q γ' (.inl t)) ∧ ∀ x, HCausal l fun γ i => q (x, γ) (.inr i)

theorem hTr_hcausal : ∀ (l : List (HVar R)) (Λ : M) (W : HIdx l → M), HCausal l (hTr l Λ W) := by
  intro l
  induction l with
  | nil => intro _ _; trivial
  | cons v l ih =>
      intro Λ W
      exact ⟨fun _ _ _ => rfl,
        fun x =>
          ih (hev v.psi x • Λ + hev (Fin.cons 0 fun t => W (.inl t) : Fin (v.n + 1) → M) x)
            fun i => W (.inr i)⟩

theorem hTrOf_hcausal : ∀ (l : List (HVar R)) (f : HPt l → M), HCausal l (hTrOf l f) := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons v l ih => intro f; exact ⟨fun _ _ _ => rfl, fun x => ih fun xs => f (x, xs)⟩

theorem HCausal.add_smul :
    ∀ (l : List (HVar R)) {q q' : HPt l → RIdx l → M} (a : R),
      HCausal l q → HCausal l q' → HCausal l fun γ i => q γ i + a • q' γ i := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _; trivial
  | cons v l ih =>
      intro q q' a h h'
      exact ⟨fun γ γ' t => by
        show q γ (.inl t) + a • q' γ (.inl t) = q γ' (.inl t) + a • q' γ' (.inl t)
        rw [h.1 γ γ' t, h'.1 γ γ' t], fun x => ih a (h.2 x) (h'.2 x)⟩

end Summand

section Field
variable {E : Type} [Field E] [Fintype E]

theorem hev_roots {n : ℕ} (c : Fin (n + 1) → E) (hc : c ≠ 0) :
    cnt (fun x : E => hev c x = 0) ≤ n := by
  have h := Alg.count_powers_le c hc 0
  simp only [Nat.add_sub_cancel, Nat.add_zero] at h
  exact h

theorem hev_roots_val {n : ℕ} {Ch : Type} [Fintype Ch] (val : Ch → E) (hv : Function.Injective val)
    (c : Fin (n + 1) → E) (hc : c ≠ 0) :
    cnt (fun a : Ch => hev c (val a) = 0) ≤ n :=
  le_trans (cnt_comp_le val (w := 1)
      (fun _ => cnt_le_one fun _ _ ha hb => hv (ha.trans hb.symm)) fun x => hev c x = 0)
    (by rw [Nat.mul_one]; exact hev_roots c hc)

/-- The sumcheck argument. Different challenges have different values; g has round polynomials at
every point; the claimed sum σ is false. Then the prover has lost (`Doomed`), with the degrees as
errors, towards every goal that holds as soon as "if the checks pass, the last value is not g at the
challenges". -/
theorem pDoomed :
    ∀ (l : List (PFmt E)) (d : PDats l), (∀ f ∈ l, Function.Injective f.val) →
      ∀ (g : HPt (pVars l d) → E) (σ : E) (goal : Tr (pRounds l) → Prop),
        (∀ γ, ∃ q, HRounds (pVars l d) g q γ) → hSumAll (pVars l d) g ≠ σ →
        (∀ τ : Tr (pRounds l),
          (HCons (pVars l d) σ (pQ l d τ.plains) (pH l d (pG l τ.rho)) →
            hFin (pVars l d) σ (pQ l d τ.plains) (pH l d (pG l τ.rho)) ≠ g (pH l d (pG l τ.rho))) →
          goal τ) →
        Doomed (pRounds l) (pErr l) goal := by
  intro l
  induction l with
  | nil =>
      intro d _ g σ goal _ hne hgoal
      exact hgoal () fun _ e => hne e.symm
  | cons f l ih =>
      intro d hinj g σ goal hR hne hgoal
      show ∀ m : (pRound f).Msg,
        cnt (fun c : f.Ch => ¬ Doomed (pRounds l) (pErr l) fun τ => goal (m, c, τ)) ≤ f.n
      intro m
      obtain ⟨q0, hq0⟩ := hR (0, hZero (pVars l d.2))
      have hp : ∀ x : E, hev (fun t : Fin (f.n + 1) => q0 (.inl t)) x =
          hSumAll (pVars l d.2) fun xs => g (x, xs) := hq0.1
      by_cases hφ : (f.var d.1).phi m.2 = σ
      · have hqp : (fun t : Fin (f.n + 1) => m.2 t - q0 (.inl t)) ≠ 0 := by
          intro h0
          apply hne
          have e : m.2 = fun t : Fin (f.n + 1) => q0 (.inl t) :=
            funext fun t => sub_eq_zero.1 (congrFun h0 t)
          rw [← hφ, e]
          exact (congrArg (f.var d.1).sum (funext hp)).symm
        refine le_trans (cnt_mono fun c hc => ?_)
          (hev_roots_val f.val (hinj f List.mem_cons_self) _ hqp)
        by_contra hz
        apply hc
        refine ih d.2 (fun f' hf' => hinj f' (List.mem_cons_of_mem _ hf'))
          (fun xs => g (f.val c, xs)) (hev m.2 (f.val c)) _ ?_ ?_ ?_
        · intro γ'
          obtain ⟨q, hq⟩ := hR (f.val c, γ')
          exact ⟨fun i => q (.inr i), hq.2⟩
        · rw [← hp]
          intro e
          apply hz
          rw [hev_sub, e, sub_self]
        · intro τ hτ
          exact hgoal (m, c, τ) fun hC => hτ hC.2
      · rw [cnt_false fun c hc =>
            hc (Doomed.of_forall _ _ fun τ => hgoal (m, c, τ) fun hC => absurd hC.1 hφ)]
        exact Nat.zero_le _

omit [Fintype E] in
theorem pStrat_run {β : Type} :
    ∀ (l : List (PFmt E)) (d : PDats l)
        (q : HPt (pVars l d) → RIdx (pVars l d) → E) (res : PPt l → β),
      HCausal (pVars l d) q →
      ∀ ρ : Rho (pRounds l),
        pQ l d ((pStrat l d q res).run ρ).1.plains = q (pH l d (pG l ρ)) ∧
        ((pStrat l d q res).run ρ).1.rho = ρ ∧
        ((pStrat l d q res).run ρ).2 = res (pG l ρ) := by
  intro l
  induction l with
  | nil => intro d q res _ ρ; exact ⟨funext fun i => i.elim, rfl, rfl⟩
  | cons f l ih =>
      intro d q res hq ρ
      obtain ⟨i1, i2, i3⟩ :=
        ih d.2 (fun γ i => q (f.val ρ.1, γ) (.inr i)) (fun γ => res (f.val ρ.1, γ)) (hq.2 _) ρ.2
      refine ⟨funext fun i => ?_, ?_, i3⟩
      · cases i with
        | inl t => exact hq.1 _ _ t
        | inr i => exact congrFun i1 i
      · exact Prod.ext rfl i2

end Field

namespace PscPar
variable {E : Type} [Field E] (Y : PscPar E)

theorem whole_eq (st : Y.St) (m : Y.J → E) (ε : E) (X : HPt (Y.vars st)) :
    (hPsi (Y.vars st) X • (0 : E) + hU (Y.vars st) (Y.W st m) X) +
        ε • ((hPsi (Y.vars st) X • Y.inc st m + hU (Y.vars st) (0 : HIdx (Y.vars st) → E) X) +
            (1 : E) • Y.sum st m X) =
      Y.whole st m ε X := by
  rw [psc_hU_zero]
  simp only [smul_eq_mul, mul_zero, zero_add, add_zero, one_mul]
  rfl

theorem whole_rounds (hV : Y.VarsOK) (hD : Y.DegOK) (st : Y.St) (m : Y.J → E)
    (ε : E) (γ : HPt (Y.vars st)) :
    HRounds (Y.vars st) (Y.whole st m ε) (Y.honQ st m ε γ) γ := by
  have h := HRounds.add_smul (Y.vars st) ε (hRounds_U (Y.vars st) (hV st) (0 : E) (Y.W st m) γ)
    (HRounds.add_smul (Y.vars st) (1 : E)
      (hRounds_U (Y.vars st) (hV st) (Y.inc st m) (0 : HIdx (Y.vars st) → E) γ)
      (psc_trOf (Y.vars st) (Y.sum st m) γ (hD st m)))
  have e : (fun i =>
        hTr (Y.vars st) 0 (Y.W st m) γ i +
          ε • (hTr (Y.vars st) (Y.inc st m) 0 γ i + (1 : E) • hTrOf (Y.vars st) (Y.sum st m) γ i)) =
      Y.honQ st m ε γ :=
    funext fun i => by simp only [smul_eq_mul, one_mul]; rfl
  rw [e] at h
  exact HRounds.congr _ (Y.whole_eq st m ε) h

theorem whole_sum (hV : Y.VarsOK) (st : Y.St) (m : Y.J → E) (ε : E) :
    hSumAll (Y.vars st) (Y.whole st m ε) =
      hMu (Y.vars st) (Y.W st m) + ε * (hSumAll (Y.vars st) (Y.sum st m) + Y.inc st m) := by
  rw [← funext (Y.whole_eq st m ε), hSumAll_add_smul, hSumAll_add_smul, hSumAll_U _ (hV st),
    hSumAll_U _ (hV st), psc_hMu_zero]
  simp only [smul_eq_mul, one_mul, zero_add, add_zero]
  ring

theorem honQ_causal (st : Y.St) (m : Y.J → E) (ε : E) : HCausal (Y.vars st) (Y.honQ st m ε) := by
  have h := HCausal.add_smul (Y.vars st) ε (hTr_hcausal (Y.vars st) (0 : E) (Y.W st m))
    (HCausal.add_smul (Y.vars st) (1 : E)
      (hTr_hcausal (Y.vars st) (Y.inc st m) (0 : HIdx (Y.vars st) → E))
      (hTrOf_hcausal (Y.vars st) (Y.sum st m)))
  have e : (fun γ i =>
        hTr (Y.vars st) 0 (Y.W st m) γ i +
          ε • (hTr (Y.vars st) (Y.inc st m) 0 γ i + (1 : E) • hTrOf (Y.vars st) (Y.sum st m) γ i)) =
      Y.honQ st m ε :=
    funext fun γ => funext fun i => by simp only [smul_eq_mul, one_mul]; rfl
  rwa [e] at h

end PscPar

section Main
variable (E : Type) [Field E] [Fintype E]

omit [Fintype E] in
theorem psc_rounds : Spec.psc_rounds E := fun Y hV hD st m ε γ => by
  refine ⟨?_, Y.whole_rounds hV hD st m ε γ⟩
  have h := hSumAll_U (Y.vars st) (hV st) (0 : E) (Y.W st m)
  simpa only [smul_zero, zero_add] using h

theorem psc_run : Spec.psc_run E := by
  intro Y Ex Wt msg w x ρ
  obtain ⟨i1, i2, i3⟩ := pStrat_run Y.fmt (Y.dat x.2) (Y.honQ x.2 (msg w) ρ.1)
    (fun γ => (Y.honMid x.2 (msg w) ρ.1 γ, w)) (Y.honQ_causal x.2 (msg w) ρ.1) ρ.2
  exact ⟨rfl, i1, Prod.ext rfl i2, i3⟩

theorem psc_core_sound_at : Spec.psc_core_sound_at E := by
  intro Y Ex hV hD hI x m hx
  show ∀ m0 : (pRound0 E).Msg,
    cnt (fun ε : E =>
        ¬ Doomed (pRounds Y.fmt) (pErr Y.fmt) fun τ =>
          ∀ z, Y.outC x (m0, ε, τ) = some z → ¬ Y.MidHolds z m) ≤ 1
  intro m0
  refine le_trans
    (cnt_mono (Q := fun ε : E => hSumAll (Y.vars x.2) (Y.whole x.2 m ε) = m0.2 + ε * x.1)
      fun ε hε => ?_)
    (cnt_le_one fun ε ε' h h' => ?_)
  · by_contra hne
    apply hε
    refine pDoomed Y.fmt (Y.dat x.2) hI (Y.whole x.2 m ε) (m0.2 + ε * x.1) _
      (fun γ => ⟨_, Y.whole_rounds hV hD x.2 m ε γ⟩) hne ?_
    intro τ hτ z hz hM
    unfold PscPar.outC at hz
    split at hz
    · rename_i hC
      obtain rfl := Option.some.inj hz
      exact hτ hC hM.symm
    · exact absurd hz (by simp)
  · rw [Y.whole_sum hV] at h h'
    have hd : hSumAll (Y.vars x.2) (Y.sum x.2 m) + Y.inc x.2 m - x.1 ≠ 0 := sub_ne_zero.2 hx
    have h0 : (ε - ε') * (hSumAll (Y.vars x.2) (Y.sum x.2 m) + Y.inc x.2 m - x.1) = 0 := by
      linear_combination h - h'
    exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hd)

end Main
end Cb
