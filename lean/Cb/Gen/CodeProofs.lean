-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/CodeProofs.lean: the proofs of the statements of Cb/Gen/Code.lean, first part: the generic
ones (pairs, families and parts of encodings, `Hiop.Enc`; hiding as a change of the randomness).

The statements on components and complexes are proved in Cb/Gen/CodeProofsComp.lean.
Nothing is defined here that a statement reads.
-/
import Cb.Gen.Code
import Prob.LawEquiv

set_option autoImplicit false

namespace Cb
open Iop Prob Blocks Hiop

theorem laws_prod : Spec.laws_prod := fun _ _ N₁ N₂ h₁ h₂ => ⟨fun m r => by
  show ((N₁.dec (N₁.enc m.1 r.1)).bind fun a =>
      (N₂.dec (N₂.enc m.2 r.2)).map fun b => ((a.1, b.1), (a.2, b.2))) = some (m, r)
  rw [h₁.dec_enc, h₂.dec_enc]
  rfl⟩

theorem dec_fam_iff : Spec.dec_fam_iff := by
  intro A _ _ E N y w
  classical
  show (if h : ∀ a, ((N a).dec (y a)).isSome then
          some
            ((fun a => (((N a).dec (y a)).get (h a)).1), fun a => (((N a).dec (y a)).get (h a)).2)
        else none) = some w ↔
    _
  constructor
  · intro h
    split_ifs at h with hs
    have hw := Option.some.inj h
    intro a
    rw [← hw]
    exact (Option.some_get (hs a)).symm
  · intro h
    have hs : ∀ a, ((N a).dec (y a)).isSome := fun a => by rw [h a]; rfl
    rw [dif_pos hs]
    refine congrArg some (Prod.ext (funext fun a => ?_) (funext fun a => ?_))
    · show (((N a).dec (y a)).get (hs a)).1 = w.1 a
      simp only [h a, Option.get_some]
    · show (((N a).dec (y a)).get (hs a)).2 = w.2 a
      simp only [h a, Option.get_some]

theorem laws_fam : Spec.laws_fam := fun A _ _ E N h =>
  ⟨fun m r => (dec_fam_iff A E N _ (m, r)).2 fun a => (h a).dec_enc (m a) (r a)⟩

theorem hides_iff_equiv : Spec.hides_iff_equiv := by
  intro E N bud
  constructor
  · intro h S hS m m'
    obtain ⟨e, he⟩ := exists_equiv_of_map_eq _ _ (h S hS m m')
    exact ⟨e, fun r p hp => congrFun (he r) ⟨p, hp⟩⟩
  · intro h S hS m m'
    obtain ⟨e, he⟩ := h S hS m m'
    have h1 : N.shows S m = N.shows S m' ∘ e := funext fun r => funext fun p => he r p.1 p.2
    rw [h1, ← PMF.map_comp, map_unif_equiv e]

theorem hides_prod : Spec.hides_prod := by
  intro E₁ E₂ N₁ N₂ b₁ b₂ h₁ h₂
  rw [hides_iff_equiv] at h₁ h₂ ⊢
  intro S hS m m'
  obtain ⟨e₁, he₁⟩ := h₁ _ hS.1 m.1 m'.1
  obtain ⟨e₂, he₂⟩ := h₂ _ hS.2 m.2 m'.2
  refine ⟨Equiv.prodCongr e₁ e₂, fun r p hp => ?_⟩
  cases p with
  | inl p => exact congrArg Sum.inl (he₁ r.1 p (Finset.mem_toLeft.2 hp))
  | inr p => exact congrArg Sum.inr (he₂ r.2 p (Finset.mem_toRight.2 hp))

theorem mem_fibre {A : Type} {E : A → ExtSpec} (S : Finset (ExtSpec.fam E).Pos)
    (a : A) (p : (E a).Pos) :
    p ∈ Enc.fibre S a ↔ (⟨a, p⟩ : (ExtSpec.fam E).Pos) ∈ S := by
  unfold Enc.fibre
  rw [Finset.mem_preimage]

theorem hides_fam : Spec.hides_fam := by
  intro A _ _ E N b h
  rw [hides_iff_equiv]
  intro S hS m m'
  have h' : ∀ a, ∃ e : (N a).Rnd ≃ (N a).Rnd, ∀ r,
      ∀ p ∈ Enc.fibre S a, (E a).rd ((N a).enc (m a) r) p = (E a).rd ((N a).enc (m' a) (e r)) p :=
    fun a => (hides_iff_equiv (E a) (N a) (b a)).1 (h a) _ (hS a) (m a) (m' a)
  choose e he using h'
  refine ⟨Equiv.piCongrRight e, fun r p hp => ?_⟩
  obtain ⟨a, p⟩ := p
  show (⟨a, (E a).rd ((N a).enc (m a) (r a)) p⟩ : Σ a, (E a).Sym) =
    ⟨a, (E a).rd ((N a).enc (m' a) (e a (r a))) p⟩
  rw [he a (r a) p ((mem_fibre S a p).2 hp)]

theorem part_fst : Spec.part_fst := fun E₁ E₂ N₁ N₂ =>
  { loc := fun _ _ _ h => Sum.inl.inj h
    enc := fun _ _ => rfl
    dec := fun y w h => by
      have h' : ((N₁.dec y.1).bind fun a => (N₂.dec y.2).map fun b => ((a.1, b.1), (a.2, b.2))) =
          some w := h
      obtain ⟨a, ha, h2⟩ := Option.bind_eq_some_iff.1 h'
      obtain ⟨b, _, rfl⟩ := Option.map_eq_some_iff.1 h2
      exact ha }

theorem part_snd : Spec.part_snd := fun E₁ E₂ N₁ N₂ =>
  { loc := fun _ _ _ h => Sum.inr.inj h
    enc := fun _ _ => rfl
    dec := fun y w h => by
      have h' : ((N₁.dec y.1).bind fun a => (N₂.dec y.2).map fun b => ((a.1, b.1), (a.2, b.2))) =
          some w := h
      obtain ⟨a, _, h2⟩ := Option.bind_eq_some_iff.1 h'
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h2
      exact hb }

theorem part_sub : Spec.part_sub := fun A A' _ _ _ _ E N σ =>
  { loc := fun y y' q h => by
      have h1 : (⟨σ q.1, (E (σ q.1)).rd (y (σ q.1)) q.2⟩ : Σ a, (E a).Sym) =
          ⟨σ q.1, (E (σ q.1)).rd (y' (σ q.1)) q.2⟩ := h
      have h2 := eq_of_heq (Sigma.mk.inj h1).2
      show (⟨q.1, (E (σ q.1)).rd (y (σ q.1)) q.2⟩ : Σ a', (E (σ a')).Sym) =
        ⟨q.1, (E (σ q.1)).rd (y' (σ q.1)) q.2⟩
      rw [h2]
    enc := fun _ _ => rfl
    dec := fun y w h =>
      (dec_fam_iff A' (fun a' => E (σ a')) (fun a' => N (σ a')) _ _).2 fun a' =>
        (dec_fam_iff A E N y w).1 h (σ a') }

theorem part_sub_whole : Spec.part_sub_whole := fun A A' _ _ _ _ E N σ hσ =>
  { toLaws := part_sub A A' E N σ
    back := fun y w' h => by
      have h1 := (dec_fam_iff A' (fun a' => E (σ a')) (fun a' => N (σ a')) _ _).1 h
      have h2 : ∀ a, ∃ u, (N a).dec (y a) = some u := fun a => by
        obtain ⟨a', rfl⟩ := hσ a
        exact ⟨_, h1 a'⟩
      choose u hu using h2
      exact ⟨(fun a => (u a).1, fun a => (u a).2), (dec_fam_iff A E N y _).2 fun a => hu a⟩
    inj := fun w w' h1 h2 => Prod.ext
      (funext fun a => by obtain ⟨a', rfl⟩ := hσ a; exact congrFun h1 a')
      (funext fun a => by obtain ⟨a', rfl⟩ := hσ a; exact congrFun h2 a') }

theorem dec_prod_iff {E₁ E₂ : ExtSpec} (N₁ : Enc E₁) (N₂ : Enc E₂)
    (y : (E₁.prod E₂).Str) (w : (N₁.prod N₂).Wit) :
    (N₁.prod N₂).dec y = some w ↔
    N₁.dec y.1 = some (w.1.1, w.2.1) ∧ N₂.dec y.2 = some (w.1.2, w.2.2) := by
  show ((N₁.dec y.1).bind fun a => (N₂.dec y.2).map fun b => ((a.1, b.1), (a.2, b.2))) = some w ↔ _
  constructor
  · intro h
    obtain ⟨a, ha, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h2
    exact ⟨ha, hb⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    rfl

theorem part_sum : Spec.part_sum := fun A B _ _ _ _ E N =>
  { loc := fun y y' q h => by
      cases q with
      | inl p =>
        have h1 : (⟨.inl p.1, (E (.inl p.1)).rd (y (.inl p.1)) p.2⟩ : Σ c, (E c).Sym) =
            ⟨.inl p.1, (E (.inl p.1)).rd (y' (.inl p.1)) p.2⟩ := h
        have h2 := eq_of_heq (Sigma.mk.inj h1).2
        show (Sum.inl (⟨p.1, (E (.inl p.1)).rd (y (.inl p.1)) p.2⟩ : Σ a, (E (.inl a)).Sym) :
            (Σ a, (E (.inl a)).Sym) ⊕ (Σ b, (E (.inr b)).Sym)) =
          Sum.inl ⟨p.1, (E (.inl p.1)).rd (y' (.inl p.1)) p.2⟩
        rw [h2]
      | inr p =>
        have h1 : (⟨.inr p.1, (E (.inr p.1)).rd (y (.inr p.1)) p.2⟩ : Σ c, (E c).Sym) =
            ⟨.inr p.1, (E (.inr p.1)).rd (y' (.inr p.1)) p.2⟩ := h
        have h2 := eq_of_heq (Sigma.mk.inj h1).2
        show (Sum.inr (⟨p.1, (E (.inr p.1)).rd (y (.inr p.1)) p.2⟩ : Σ b, (E (.inr b)).Sym) :
            (Σ a, (E (.inl a)).Sym) ⊕ (Σ b, (E (.inr b)).Sym)) =
          Sum.inr ⟨p.1, (E (.inr p.1)).rd (y' (.inr p.1)) p.2⟩
        rw [h2]
    enc := fun _ _ => rfl
    dec := fun y w h => by
      have h1 := (dec_fam_iff (A ⊕ B) E N y w).1 h
      exact (dec_prod_iff _ _ _ _).2
        ⟨(dec_fam_iff A _ _ _ _).2 fun a => h1 (.inl a),
          (dec_fam_iff B _ _ _ _).2 fun b => h1 (.inr b)⟩
    back := fun y w' h => by
      obtain ⟨h1, h2⟩ := (dec_prod_iff _ _ _ _).1 h
      have h1' := (dec_fam_iff A _ _ _ _).1 h1
      have h2' := (dec_fam_iff B _ _ _ _).1 h2
      refine ⟨(fun c => match c with
        | .inl a => w'.1.1 a
        | .inr b => w'.1.2 b, fun c => match c with
        | .inl a => w'.2.1 a
        | .inr b => w'.2.2 b), (dec_fam_iff (A ⊕ B) E N y _).2 fun c => ?_⟩
      cases c with
      | inl a => exact h1' a
      | inr b => exact h2' b
    inj := fun w w' h1 h2 => Prod.ext
      (funext fun c => by
        cases c with
        | inl a => exact congrFun (congrArg Prod.fst h1) a
        | inr b => exact congrFun (congrArg Prod.snd h1) b)
      (funext fun c => by
        cases c with
        | inl a => exact congrFun (congrArg Prod.fst h2) a
        | inr b => exact congrFun (congrArg Prod.snd h2) b) }

end Cb
