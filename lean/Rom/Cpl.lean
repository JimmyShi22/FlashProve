-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Cpl.lean: couplings of two discrete distributions within a relation. Helper lemmas; no protocol.

`Cpl R p q`: p and q have a coupling under which the two samples are always related by R. Rules for
pure, bind, a sample on one side only, a function of the sample; two consequences:

  `Cpl.map_eq`     If R makes g₁ of the first sample equal to g₂ of the second, then p.map g₁ =
                   q.map g₂.
  `Cpl.exists_left`
                   Every possible sample of q is related to a possible sample of p.
-/
import Prob.Count
import Rom.Forget

namespace Rom
open Prob

variable {α β γ δ ε : Type}

/-- p and q have a coupling under which the samples are related by R -/
def Cpl (R : α → β → Prop) (p : PMF α) (q : PMF β) : Prop :=
  ∃ c : PMF (α × β), c.map Prod.fst = p ∧ c.map Prod.snd = q ∧ ∀ x ∈ c.support, R x.1 x.2

namespace Cpl

theorem pure {R : α → β → Prop} {a : α} {b : β} (h : R a b) : Cpl R (PMF.pure a) (PMF.pure b) :=
  ⟨PMF.pure (a, b), PMF.pure_map _ _, PMF.pure_map _ _, fun x hx => by
    rw [PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact h⟩

theorem mono {R R' : α → β → Prop} {p : PMF α} {q : PMF β}
    (h : Cpl R p q) (hR : ∀ a b, R a b → R' a b) : Cpl R' p q := by
  obtain ⟨c, h1, h2, h3⟩ := h
  exact ⟨c, h1, h2, fun x hx => hR _ _ (h3 x hx)⟩

/-- any two distributions have a coupling -/
theorem top (p : PMF α) (q : PMF β) : Cpl (fun _ _ => True) p q :=
  ⟨Prob.prod p q, map_fst_prod p q, map_snd_prod p q, fun _ _ => trivial⟩

/-- the second sample is a function of the first -/
theorem map_right (p : PMF α) (φ : α → β) : Cpl (fun a b => b = φ a) p (p.map φ) :=
  ⟨p.map fun a => (a, φ a), by rw [PMF.map_comp]; exact PMF.map_id p, by rw [PMF.map_comp]; rfl, fun x hx => by
    obtain ⟨a, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
    rfl⟩

theorem diag (p : PMF α) : Cpl (fun a b => a = b) p p := by
  have h := map_right p id
  rw [PMF.map_id] at h
  exact h.mono fun a b hab => hab.symm

theorem bind {R : α → β → Prop} {R' : γ → δ → Prop} {p : PMF α} {q : PMF β} {f : α → PMF γ}
    {g : β → PMF δ} (h : Cpl R p q) (hfg : ∀ a b, R a b → Cpl R' (f a) (g b)) :
    Cpl R' (p.bind f) (q.bind g) := by
  classical
  obtain ⟨c, h1, h2, h3⟩ := h
  have hD : ∀ x : α × β, ∃ d : PMF (γ × δ),
      d.map Prod.fst = f x.1 ∧
      d.map Prod.snd = g x.2 ∧
      (R x.1 x.2 → ∀ y ∈ d.support, R' y.1 y.2) := by
    intro x
    by_cases hx : R x.1 x.2
    · obtain ⟨d, a, b, e⟩ := hfg _ _ hx
      exact ⟨d, a, b, fun _ => e⟩
    · exact ⟨Prob.prod (f x.1) (g x.2), map_fst_prod _ _, map_snd_prod _ _, fun h => absurd h hx⟩
  choose D hD1 hD2 hD3 using hD
  refine ⟨c.bind D, ?_, ?_, ?_⟩
  · rw [PMF.map_bind, ← h1, PMF.bind_map]
    exact congrArg _ (funext fun x => hD1 x)
  · rw [PMF.map_bind, ← h2, PMF.bind_map]
    exact congrArg _ (funext fun x => hD2 x)
  · intro y hy
    obtain ⟨x, hx, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
    exact hD3 x (h3 x hx) y hy

/-- If every f a is coupled with q within R', so is p.bind f. -/
theorem bind_left {R' : γ → δ → Prop} (p : PMF α) {f : α → PMF γ}
    {q : PMF δ} (h : ∀ a, Cpl R' (f a) q) : Cpl R' (p.bind f) q := by
  have h1 :=
    bind (R := fun _ _ => True) (g := fun _ : Unit => q) (top p (PMF.pure ())) fun a _ _ => h a
  rwa [PMF.pure_bind] at h1

theorem map {R : α → β → Prop} {R' : γ → δ → Prop} {p : PMF α} {q : PMF β} (f : α → γ) (g : β → δ)
    (h : Cpl R p q) (hfg : ∀ a b, R a b → R' (f a) (g b)) : Cpl R' (p.map f) (q.map g) :=
  bind h fun a b hab => pure (hfg a b hab)

/-- what holds of every possible sample of p may be added to the relation -/
theorem and_left {R : α → β → Prop} {p : PMF α} {q : PMF β} (h : Cpl R p q)
    {A : α → Prop} (hA : ∀ a ∈ p.support, A a) :
    Cpl (fun a b => R a b ∧ A a) p q := by
  obtain ⟨c, h1, h2, h3⟩ := h
  refine ⟨c, h1, h2, fun x hx => ⟨h3 x hx, hA _ ?_⟩⟩
  rw [← h1]
  exact (PMF.mem_support_map_iff _ _ _).2 ⟨x, hx, rfl⟩

theorem map_eq {p : PMF α} {q : PMF β} (g₁ : α → ε) (g₂ : β → ε)
    (h : Cpl (fun a b => g₁ a = g₂ b) p q) : p.map g₁ = q.map g₂ := by
  obtain ⟨c, h1, h2, h3⟩ := h
  rw [← h1, ← h2, PMF.map_comp, PMF.map_comp]
  exact bind_congr_support c fun x hx => congrArg PMF.pure (h3 x hx)

theorem exists_left {R : α → β → Prop} {p : PMF α} {q : PMF β} (h : Cpl R p q) :
    ∀ b ∈ q.support, ∃ a ∈ p.support, R a b := by
  obtain ⟨c, h1, h2, h3⟩ := h
  intro b hb
  rw [← h2] at hb
  obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hb
  exact ⟨x.1, by rw [← h1]; exact (PMF.mem_support_map_iff _ _ _).2 ⟨x, hx, rfl⟩, h3 x hx⟩

end Cpl

end Rom
