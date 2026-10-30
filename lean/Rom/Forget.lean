-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Forget.lean: proofs of `Spec.forget` and `Spec.forgetCall` (Rom/SpecForget.lean).

`forget`: two challengers reply by oracle algorithms over a shared, lazily sampled table
(`World.ofOComp`), and φ maps the private states of the first to those of the second. If for every
fixed family of oracles each reply of the first, with its new private state mapped by φ, has the
distribution of the second's reply, then every adversary has the same joint distribution of output
and (mapped) final private state against both, from every table. `forgetCall`: if calls that run an
oracle algorithm, discard its result, reply with a constant and keep the private state are replaced
by the constant, the adversary's output keeps its distribution.

(a) `Adv.Bounded.mono`, `Adv.TotalBound.succ`.
(b) The proof of `forget` and `forgetCall`: adversary and challenger are together one oracle
    algorithm (`Adv.prog`, `interact_ofOComp`). The output law of an oracle algorithm under lazy
    sampling, from any table, is determined by its laws for fixed families of oracles
    (`map_runLazy_congr`, from `PrFrom_eq_lazy` of Rom/EagerLazy.lean: eager = lazy).

Notation: `A.Bounded t N` (Rom/World.lean): at most t o queries to oracle o and at most N calls, on
every path; `A.TotalBound t N` (Rom/World.lean): at most t queries in all and at most N calls, on
every path.
-/
import Rom.SpecForget
import Rom.EagerLazy

open scoped ENNReal
open Prob

namespace Rom

variable {S : OSpec} {Out In α β γ : Type}

/-! ## Tools -/

/-- Two continuations that agree on the support give the same law. -/
theorem bind_congr_support (p : PMF α) {f g : α → PMF β} (h : ∀ a ∈ p.support, f a = g a) :
    p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a ((PMF.mem_support_iff p a).mpr ha)]

theorem Table.set_of_some {T : Table S} {o : S.ι} {q : S.Dom o} (h : T o q = none) (r : S.Rng o)
    {o' : S.ι} {q' : S.Dom o'} {r' : S.Rng o'} (h' : T o' q' = some r') :
    T.set o q r o' q' = some r' := by
  by_cases ho : o' = o
  · subst ho
    by_cases hq : q' = q
    · subst hq
      rw [h] at h'
      exact absurd h' (by simp)
    · simpa [Table.set, Function.update_of_ne hq] using h'
  · simpa [Table.set, Function.update_of_ne ho] using h'

/-- What an entry of T.set o q r says. -/
theorem Table.set_eq_some {T : Table S} {o : S.ι} {q : S.Dom o} {r : S.Rng o} {o' : S.ι}
    {q' : S.Dom o'} {r' : S.Rng o'} (h : T.set o q r o' q' = some r') :
    (∃ ho : o' = o, ho ▸ q' = q ∧ ho ▸ r' = r) ∨ T o' q' = some r' := by
  by_cases ho : o' = o
  · subst ho
    by_cases hq : q' = q
    · subst hq
      left
      refine ⟨rfl, rfl, ?_⟩
      simpa [Table.set] using h.symm
    · right
      simpa [Table.set, Function.update_of_ne hq] using h
  · right
    simpa [Table.set, Function.update_of_ne ho] using h

/-- A lazy run never changes an entry of the table. -/
theorem OComp.runLazy_keeps (c : OComp S α) :
    ∀ (T : Table S), ∀ x ∈ (c.runLazy T).support,
      ∀ (o : S.ι) (q : S.Dom o) (r : S.Rng o), T o q = some r → x.2 o q = some r := by
  induction c with
  | pure a =>
    intro T x hx o q r h
    simp only [OComp.runLazy, PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact h
  | query o₀ q₀ k ih =>
    intro T x hx o q r h
    simp only [OComp.runLazy] at hx
    cases h0 : T o₀ q₀ with
    | some r₀ =>
      rw [h0] at hx
      exact ih r₀ T x hx o q r h
    | none =>
      rw [h0] at hx
      obtain ⟨r₀, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
      exact ih r₀ _ x hx o q r (Table.set_of_some h0 r₀ h)
  | sample n k ih =>
    intro T x hx o q r h
    simp only [OComp.runLazy] at hx
    obtain ⟨r₀, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
    exact ih r₀ T x hx o q r h

/-! ## (a) Larger bounds -/


theorem Adv.Bounded.mono {A : Adv S Out In α} :
    ∀ {t t' : S.ι → ℕ} {N : ℕ}, A.Bounded t N → (∀ o, t o ≤ t' o) → A.Bounded t' N := by
  induction A with
  | halt a => intro t t' N _ _; trivial
  | sample n k ih => intro t t' N h ht r; exact ih r (h r) ht
  | query o q k ih =>
    intro t t' N h ht
    refine ⟨lt_of_lt_of_le h.1 (ht o), fun r => ih r (h.2 r) fun o' => ?_⟩
    by_cases ho : o' = o
    · subst ho
      simp only [Function.update_self]
      exact Nat.sub_le_sub_right (ht o') 1
    · simp only [Function.update_of_ne ho]
      exact ht o'
  | call m k ih =>
    intro t t' N h ht
    cases N with
    | zero => exact h
    | succ N => exact fun a => ih a (h a) ht

theorem Adv.TotalBound.succ {A : Adv S Out In α} :
    ∀ {t N : ℕ}, A.TotalBound t N → A.TotalBound (t + 1) N := by
  induction A with
  | halt a => intro t N _; trivial
  | sample n k ih => intro t N h r; exact ih r (h r)
  | query o q k ih =>
    intro t N h
    cases t with
    | zero => exact absurd h (by simp [Adv.TotalBound])
    | succ t => exact fun r => ih r (h r)
  | call m k ih =>
    intro t N h
    cases N with
    | zero => exact h
    | succ N => exact fun a => ih a (h a)



/-! ## (b) Forget -/

/-- The output law of an oracle algorithm under lazy sampling, from any table, is determined by its
laws for fixed families of oracles (h). -/
theorem map_runLazy_congr {α₁ α₂ : Type} {c₁ : OComp S α₁} {c₂ : OComp S α₂} (g₁ : α₁ → β)
    (g₂ : α₂ → β) (h : ∀ f, (c₁.runEager f).map g₁ = (c₂.runEager f).map g₂) (T : Table S) :
    (c₁.runLazy T).map (fun x => g₁ x.1) = (c₂.runLazy T).map (fun x => g₂ x.1) := by
  refine ext_of_pr fun E => ?_
  have key : ∀ {α' : Type} (c : OComp S α') (g : α' → β), pr ((c.runLazy T).map fun x => g x.1) E =
      ∫⁻ f, pr ((c.runEager (T.over f)).map g) E ∂(U S) := by
    intro α' c g
    have h1 : (c.runLazy T).map (fun x => g x.1) = ((c.runLazy T).map Prod.fst).map g := by
      rw [PMF.map_comp]
      rfl
    rw [h1, pr_map, ← PrFrom_eq_lazy]
    unfold PrFrom PrCoins
    simp only [pr_map]
  rw [key c₁ g₁, key c₂ g₂]
  simp only [h]

/-- An adversary and the replies of a challenger, as one oracle algorithm. It returns the output and
the final private state. -/
def Adv.prog {τ : Type} (step : τ → Out → OComp S (In × τ)) : Adv S Out In α → τ → OComp S (α × τ)
  | .halt a, t => .pure (a, t)
  | .sample n k, t => .sample n fun r => (k r).prog step t
  | .query o q k, t => .query o q fun r => (k r).prog step t
  | .call m k, t => (step t m).bind fun p => (k p.1).prog step p.2

/-- The interaction is the lazy run of that algorithm. -/
theorem interact_ofOComp {τ : Type} (step : τ → Out → OComp S (In × τ)) (A : Adv S Out In α) :
    ∀ (t : τ) (T : Table S), interact (World.ofOComp step) A (t, T) =
      ((A.prog step t).runLazy T).map fun x => (x.1.1, (x.1.2, x.2)) := by
  induction A with
  | halt a =>
    intro t T
    simp only [interact, Adv.prog, OComp.runLazy, PMF.pure_map]
    rfl
  | sample n k ih =>
    intro t T
    simp only [interact, Adv.prog, OComp.runLazy, PMF.map_bind, ih]
    rfl
  | query o q k ih =>
    intro t T
    simp only [interact, Adv.prog, OComp.runLazy, World.ofOComp, lazyAnswer]
    cases h : T o q with
    | some r =>
      simp only [PMF.pure_map, PMF.pure_bind]
      exact ih r t T
    | none =>
      simp only [PMF.map_comp, PMF.bind_map, PMF.map_bind]
      exact congrArg _ (funext fun r => ih r t _)
  | call m k ih =>
    intro t T
    simp only [interact, Adv.prog, World.ofOComp, OComp.runLazy_bind, PMF.bind_map, PMF.map_bind]
    exact congrArg _ (funext fun x => ih x.1.1 x.1.2 x.2)

theorem interact_ofOComp_map {τ δ : Type} (step : τ → Out → OComp S (In × τ)) (A : Adv S Out In α)
    (t : τ) (T : Table S) (g : α × (τ × Table S) → δ) :
    (interact (World.ofOComp step) A (t, T)).map g =
      ((A.prog step t).runLazy T).map fun x => g (x.1.1, (x.1.2, x.2)) := by
  rw [interact_ofOComp]
  exact PMF.map_comp _ _ _

/-- For fixed oracles, if each reply of the first, mapped by φ, has the distribution of the second's
(h), the two algorithms have the same law up to φ. -/
theorem prog_runEager {τ₁ τ₂ : Type} (step₁ : τ₁ → Out → OComp S (In × τ₁))
    (step₂ : τ₂ → Out → OComp S (In × τ₂)) (φ : τ₁ → τ₂)
    (h : ∀ t m f, ((step₁ t m).runEager f).map (Prod.map id φ) = (step₂ (φ t) m).runEager f)
    (f : Fam S) (A : Adv S Out In α) :
    ∀ t, ((A.prog step₁ t).runEager f).map (Prod.map id φ) = (A.prog step₂ (φ t)).runEager f := by
  induction A with
  | halt a => intro t; simp [Adv.prog, OComp.runEager, PMF.pure_map]
  | sample n k ih => intro t; simp only [Adv.prog, OComp.runEager, PMF.map_bind, ih]
  | query o q k ih => intro t; simp only [Adv.prog, OComp.runEager, ih]
  | call m k ih =>
    intro t
    simp only [Adv.prog, OComp.runEager_bind, PMF.map_bind, ih]
    rw [← h t m f, PMF.bind_map]
    rfl

theorem forget : Spec.forget := by
  intro S Out In α τ₁ τ₂ step₁ step₂ φ h A t T
  have h1 := map_runLazy_congr (c₁ := A.prog step₁ t) (c₂ := A.prog step₂ (φ t)) (Prod.map id φ) id
    (fun f => by rw [prog_runEager step₁ step₂ φ h f A t, PMF.map_id]) T
  exact ((interact_ofOComp_map step₁ A t T fun x => (x.1, φ x.2.1)).trans h1).trans
    (interact_ofOComp_map step₂ A (φ t) T fun x => (x.1, x.2.1)).symm

theorem forgetCall : Spec.forgetCall := by
  intro S Out In τ α step step' h A s T
  have h1 := forget S Out In α τ τ step step' id (fun t m f => by
    have e : (Prod.map id id : In × τ → In × τ) = id := by funext x; rfl
    rw [e, PMF.map_id]
    show (step t m).runEager f = (step' t m).runEager f
    rcases h t m with h0 | ⟨β, c, a, hs, hs'⟩
    · rw [h0]
    · rw [hs, hs', OComp.runEager_bind]
      simp [OComp.runEager]) A s T
  have h2 := congrArg (fun p => p.map Prod.fst) h1
  exact ((PMF.map_comp _ _ _).symm.trans h2).trans (PMF.map_comp _ _ _)

end Rom
