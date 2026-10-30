-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide2/Same.lean: TWO ORACLE ALGORITHMS WITH THE SAME RUN UNDER EVERY RULE FOR ANSWERING
QUERIES (Rom/Handle/Defs.lean), the outputs of the first mapped to those of the second. Two
definitions and their calculus. General in the family of oracles.

General definitions and lemmas. This file states no goal of the release.

  Eqv c c'        c and c' have the same run, under every rule and from every state.
  Eqv.late, .swap a draw before an algorithm, or after it; two draws in either order.
  Same ψ Q c c'   the run of c' is the run of c with each output a mapped to ψ a; and every output
                  of c, on every path, has the property Q (Post, Johnson/TokenSide/Tie.lean).
  Same.bind       SEQUENTIAL COMPOSITION: what follows need be the same only at outputs with Q.
  Same.ofTie      from a tie (Tie) whose output does not hang on the coins, and "all coins first"
                  (CoinsFirst, Rom/Handle/Coins.lean) for the family on its right.

Beside Tie: a tie compares an algorithm with a FAMILY in coins that are drawn first, and two ties
are composed over a product of their coins. Same compares two algorithms. So where each part of a
long program has coins of its own, each part is brought to this form by itself, and the parts are
then composed with no coins left to carry.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.Tie
import Prob.LensLaw

set_option autoImplicit false

noncomputable section

namespace Rom
open Prob
variable {S : OSpec} {α β γ α' β' : Type}

/-! ## The same run -/

/-- Two algorithms have the same run, under every rule for answering queries and from every state.
-/
def Eqv (c c' : OComp S α) : Prop :=
  ∀ (σ : Type) (h : Handler S σ) (s : σ), c.interp h s = c'.interp h s

namespace Eqv

theorem refl (c : OComp S α) : Eqv c c := fun _ _ _ => rfl

theorem of_eq {c c' : OComp S α} (e : c = c') : Eqv c c' := e ▸ refl c

theorem symm {c c' : OComp S α} (h : Eqv c c') : Eqv c' c := fun σ hd s => (h σ hd s).symm

theorem trans {c c' c'' : OComp S α} (h : Eqv c c') (h' : Eqv c' c'') : Eqv c c'' :=
  fun σ hd s => (h σ hd s).trans (h' σ hd s)

theorem bind {c c' : OComp S α} {g g' : α → OComp S β} (hc : Eqv c c')
    (hg : ∀ a, Eqv (g a) (g' a)) : Eqv (c.bind g) (c'.bind g') := by
  intro σ h s
  rw [OComp.interp_bind, OComp.interp_bind, hc σ h s]
  exact congrArg _ (funext fun p => hg p.1 σ h p.2)

theorem sample {n : ℕ} {k k' : Fin (n + 1) → OComp S α} (hk : ∀ r, Eqv (k r) (k' r)) :
    Eqv (.sample n k) (.sample n k') := by
  intro σ h s
  rw [OComp.interp_sample, OComp.interp_sample]
  exact congrArg _ (funext fun r => hk r σ h s)

/-- A draw before an algorithm, or after it. -/
theorem late (n : ℕ) (c : OComp S α) (g : Fin (n + 1) → α → OComp S β) :
    Eqv (.sample n fun r => c.bind (g r)) (c.bind fun a => .sample n fun r => g r a) :=
  fun _ h s => OComp.interp_sample_comm h n c g s

/-- Two draws, in either order. -/
theorem swap (n m : ℕ) (k : Fin (n + 1) → Fin (m + 1) → OComp S α) :
    Eqv (.sample n fun a => .sample m fun b => k a b)
      (.sample m fun b => .sample n fun a => k a b) := by
  intro σ h s
  simp only [OComp.interp_sample]
  exact PMF.bind_comm _ _ _

/-- A draw that is not read. -/
theorem drop (n : ℕ) (c : OComp S α) : Eqv (.sample n fun _ => c) c := by
  intro σ h s
  rw [OComp.interp_sample]
  exact PMF.bind_const _ _

end Eqv

/-! ## A property of all outputs, on the runs -/

theorem Post.trivial : ∀ c : OComp S α, Post (fun _ => True) c
  | .pure _ => True.intro
  | .query _ _ k => fun r => Post.trivial (k r)
  | .sample _ k => fun r => Post.trivial (k r)

/-- A property of all outputs holds of every outcome of every run. -/
theorem Post.support {P : α → Prop} {σ : Type} (h : Handler S σ) :
    ∀ {c : OComp S α}, Post P c → ∀ (s : σ), ∀ p ∈ (c.interp h s).support, P p.1
  | .pure a, hp, s, p, hm => by
      rw [OComp.interp_pure, PMF.support_pure, Set.mem_singleton_iff] at hm
      rw [hm]
      exact hp
  | .query o q k, hp, s, p, hm => by
      rw [OComp.interp_query, PMF.mem_support_bind_iff] at hm
      obtain ⟨y, _, hy⟩ := hm
      exact Post.support h (hp y.1) y.2 p hy
  | .sample n k, hp, s, p, hm => by
      rw [OComp.interp_sample, PMF.mem_support_bind_iff] at hm
      obtain ⟨y, _, hy⟩ := hm
      exact Post.support h (hp y) s p hy

/-- The left side of a tie has the tie's property at all its outputs. -/
theorem Tie.toPost {Ω : Type} {μ : PMF Ω} {φ : α → Ω → β} {Q : α → Prop} {c : OComp S α}
    {g : Ω → OComp S β} (h : Tie μ φ Q c g) : Post Q c := by
  induction h with
  | done hq _ => exact hq
  | query _ _ _ ih => exact ih
  | draw _ _ _ ih => exact ih
  | coin _ _ _ _ _ ih => exact ih

/-! ## The same run, with the outputs mapped -/

/-- **The run of c' is the run of c with its outputs mapped by ψ**, and all outputs of c have Q. -/
structure Same (ψ : α → β) (Q : α → Prop) (c : OComp S α) (c' : OComp S β) : Prop where
  run : ∀ (σ : Type) (h : Handler S σ) (s : σ),
    c'.interp h s = (c.interp h s).map fun p => (ψ p.1, p.2)
  post : Post Q c

namespace Same
variable {ψ : α → β} {Q : α → Prop}

theorem pure {a : α} (hq : Q a) : Same (S := S) ψ Q (.pure a) (.pure (ψ a)) :=
  ⟨fun _ _ _ => by rw [OComp.interp_pure, OComp.interp_pure, PMF.pure_map], hq⟩

/-- **Sequential composition.** -/
theorem bind {ψ' : α' → β'} {Q' : α' → Prop} {c : OComp S α} {c' : OComp S β}
    {f : α → OComp S α'} {f' : β → OComp S β'} (h : Same ψ Q c c')
    (hf : ∀ a, Q a → Same ψ' Q' (f a) (f' (ψ a))) : Same ψ' Q' (c.bind f) (c'.bind f') where
  run := fun σ hd s => by
    rw [OComp.interp_bind, OComp.interp_bind, h.run σ hd s, PMF.bind_map, PMF.map_bind]
    exact Prob.bind_congr_on _ fun p hp => (hf p.1 (h.post.support hd s p hp)).run σ hd p.2
  post := h.post.bind fun a ha => (hf a ha).post

theorem sample {n : ℕ} {k : Fin (n + 1) → OComp S α} {k' : Fin (n + 1) → OComp S β}
    (hk : ∀ r, Same ψ Q (k r) (k' r)) : Same ψ Q (.sample n k) (.sample n k') where
  run := fun σ hd s => by
    rw [OComp.interp_sample, OComp.interp_sample, PMF.map_bind]
    exact congrArg _ (funext fun r => (hk r).run σ hd s)
  post := fun r => (hk r).post

/-- A first part that is one algorithm on both sides. -/
theorem left (c₀ : OComp S γ) {f : γ → OComp S α} {f' : γ → OComp S β}
    (h : ∀ x, Same ψ Q (f x) (f' x)) : Same ψ Q (c₀.bind f) (c₀.bind f') where
  run := fun σ hd s => by
    rw [OComp.interp_bind, OComp.interp_bind, PMF.map_bind]
    exact congrArg _ (funext fun p => (h p.1).run σ hd p.2)
  post := (Post.trivial c₀).bind fun x _ => (h x).post

/-- Another algorithm on the right with the same run. -/
theorem congr {c : OComp S α} {c' c'' : OComp S β} (h : Same ψ Q c c') (e : Eqv c'' c') :
    Same ψ Q c c'' :=
  ⟨fun σ hd s => (e σ hd s).trans (h.run σ hd s), h.post⟩

theorem mono {Q' : α → Prop} (hQ : ∀ a, Q a → Q' a) {c : OComp S α} {c' : OComp S β}
    (h : Same ψ Q c c') : Same ψ Q' c c' := ⟨h.run, h.post.mono hQ⟩

/-- A property of all outputs of c joins Q. -/
theorem also {P : α → Prop} {c : OComp S α} {c' : OComp S β} (h : Same ψ Q c c') (hp : Post P c) :
    Same ψ (fun a => Q a ∧ P a) c c' := by
  refine ⟨h.run, ?_⟩
  have hq := h.post
  clear h
  induction c with
  | pure a => exact ⟨hq, hp⟩
  | query o q k ih => exact fun r => ih r (hp r) (hq r)
  | sample n k ih => exact fun r => ih r (hp r) (hq r)

/-- Another form of the map, equal where Q holds. -/
theorem out {ψ' : α → β} (hψ : ∀ a, Q a → ψ a = ψ' a) {c : OComp S α} {c' : OComp S β}
    (h : Same ψ Q c c') : Same ψ' Q c c' where
  run := fun σ hd s => by
    rw [h.run σ hd s]
    show (c.interp hd s).bind _ = (c.interp hd s).bind _
    exact Prob.bind_congr_on _ fun p hp => by
      show PMF.pure (ψ p.1, p.2) = PMF.pure (ψ' p.1, p.2)
      rw [hψ p.1 (h.post.support hd s p hp)]
  post := h.post

/-- From a tie whose output does not hang on the coins, and "all coins first" for its family. -/
theorem ofTie {Ω : Type} {μ : PMF Ω} {c : OComp S α} {g : Ω → OComp S β} {c' : OComp S β}
    (hT : Tie μ (fun a _ => ψ a) Q c g) (hc : CoinsFirst μ g c') : Same ψ Q c c' :=
  ⟨fun σ hd s => by rw [← hc σ hd s, hT.sound_const hd s], hT.toPost⟩

/-- The same, where "all coins first" is known against the left side with its output mapped. -/
theorem ofFirst {c : OComp S α} {c' : OComp S β} (hp : Post Q c)
    (e : Eqv c' (c.bind fun a => .pure (ψ a))) : Same ψ Q c c' :=
  ⟨fun σ hd s => by
    rw [e σ hd s, OComp.interp_bind]
    rfl, hp⟩

end Same

end Rom

#print axioms Rom.Same.bind
#print axioms Rom.Same.ofTie
#print axioms Rom.Eqv.late
