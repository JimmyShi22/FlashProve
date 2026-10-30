-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Prob/LawKit.lean: lemmas for showing, piece by piece, that two functions of uniform coins have the
same distribution.

No protocol occurs here. The types of uniform coins are finite and non-empty. The cases: the two
functions are determined in the same way by quantities with the same distribution
(`map_eq_of_factor`); two independent uniform coins are
sampled one after the other (`map_unif_prod`); the coins are renamed by a bijection
(`map_unif_reindex`, `map_unif_prod_congr`); the distribution over the second coin depends on the
first coin only through a function of it (`map_unif_bind_factor`).
-/
import Prob.Count

namespace Prob

variable {α α' β γ δ : Type}

theorem map_congr_support (p : PMF α) {f g : α → γ} (h : ∀ a ∈ p.support, f a = g a) :
    p.map f = p.map g := by
  show p.bind (PMF.pure ∘ f) = p.bind (PMF.pure ∘ g)
  refine PMF.ext fun y => ?_
  simp only [PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : p a = 0
  · rw [ha, zero_mul, zero_mul]
  · rw [Function.comp_apply, Function.comp_apply, h a ((PMF.mem_support_iff _ _).2 ha)]

/-- If f and f' are determined in the same way by g and g' (g a = g' a' → f a = f' a'), and g, g'
have the same distribution, then f, f' have the same distribution. -/
theorem map_eq_of_factor {f : α → γ} {f' : α' → γ} {g : α → δ} {g' : α' → δ} (p : PMF α)
    (p' : PMF α') (h : ∀ a a', g a = g' a' → f a = f' a') (hg : p.map g = p'.map g') :
    p.map f = p'.map f' := by
  classical
  obtain ⟨a₀', -⟩ := p'.support_nonempty
  let Ψ : δ → γ := fun d => if hd : ∃ a', g' a' = d then f' hd.choose else f' a₀'
  have h1 : ∀ a ∈ p.support, f a = Ψ (g a) := by
    intro a ha
    have hm : g a ∈ (p'.map g').support := by
      rw [← hg]
      exact (PMF.mem_support_map_iff _ _ _).2 ⟨a, ha, rfl⟩
    obtain ⟨a', -, ha'⟩ := (PMF.mem_support_map_iff _ _ _).1 hm
    have hd : ∃ a', g' a' = g a := ⟨a', ha'⟩
    show f a = if hd : ∃ a', g' a' = g a then f' hd.choose else f' a₀'
    rw [dif_pos hd]
    exact h a _ hd.choose_spec.symm
  have h2 : ∀ a' ∈ p'.support, f' a' = Ψ (g' a') := by
    intro a' ha'
    have hm : g' a' ∈ (p.map g).support := by
      rw [hg]
      exact (PMF.mem_support_map_iff _ _ _).2 ⟨a', ha', rfl⟩
    obtain ⟨a, -, ha⟩ := (PMF.mem_support_map_iff _ _ _).1 hm
    have hd : ∃ a'', g' a'' = g' a' := ⟨a', rfl⟩
    show f' a' = if hd : ∃ a'', g' a'' = g' a' then f' hd.choose else f' a₀'
    rw [dif_pos hd, ← h a a' ha, h a _ (ha.trans hd.choose_spec.symm)]
  rw [map_congr_support p h1, map_congr_support p' h2]
  have e1 : p.map (fun a => Ψ (g a)) = (p.map g).map Ψ := (PMF.map_comp g p Ψ).symm
  have e2 : p'.map (fun a => Ψ (g' a)) = (p'.map g').map Ψ := (PMF.map_comp g' p' Ψ).symm
  rw [e1, e2, hg]

variable [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]

/-- The distribution of a function of two independent uniform coins: sample the first coin, then the
second. -/
theorem map_unif_prod (f : α × β → γ) :
    (unif (α × β)).map f = (unif α).bind fun a => (unif β).map fun b => f (a, b) := by
  rw [unif_prod]
  unfold prod
  rw [PMF.map_bind]
  refine congrArg _ (funext fun a => ?_)
  rw [PMF.map_comp]
  rfl

/-- If a bijection e of the coins satisfies f a = f' (e a) for all a, then f and f' have the same
distribution under uniform coins. -/
theorem map_unif_reindex (e : α ≃ α) (f f' : α → γ) (h : ∀ a, f a = f' (e a)) :
    (unif α).map f = (unif α).map f' := by
  have hf : f = f' ∘ e := funext h
  rw [hf, ← PMF.map_comp, map_unif_equiv]

theorem bind_unif_reindex (e : α ≃ α) (k : α → PMF γ) :
    ((unif α).bind fun a => k (e a)) = (unif α).bind k := by
  have h : ((unif α).map e).bind k = (unif α).bind fun a => k (e a) := PMF.bind_map _ _ _
  rw [← h, map_unif_equiv]

/-- Both coins are uniform and independent. The first coin is renamed by a bijection. If for each
value of it the distributions over the second coin agree, then the distributions over both agree. -/
theorem map_unif_prod_congr (e : α ≃ α) (f f' : α × β → γ)
    (h : ∀ a, ((unif β).map fun b => f (a, b)) = (unif β).map fun b => f' (e a, b)) :
    (unif (α × β)).map f = (unif (α × β)).map f' := by
  rw [map_unif_prod, map_unif_prod, ← bind_unif_reindex e fun a => (unif β).map fun b => f' (a, b)]
  exact congrArg _ (funext h)

/-- For independent uniform coins: if for each value a of the first coin the distribution over the
second coin is K (hh a), so that it depends on the first coin only through hh, then the distribution
over both is the distribution of hh followed by the kernel K; so the first coin's type and hh enter
only through the distribution of hh. -/
theorem map_unif_bind_factor (f : α × β → γ) (hh : α → δ) (K : δ → PMF γ)
    (h : ∀ a, ((unif β).map fun b => f (a, b)) = K (hh a)) :
    (unif (α × β)).map f = ((unif α).map hh).bind K := by
  rw [map_unif_prod, PMF.bind_map]
  exact congrArg _ (funext h)

end Prob
