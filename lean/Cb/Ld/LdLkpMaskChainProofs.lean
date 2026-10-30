-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskChainProofs.lean: proofs for Cb/Ld/LdLkpMaskChain.lean.

Main names (statements and hypotheses: Cb/Ld/LdLkpMaskChain.lean):
  `mj_seq`, `mj_chain`, `mj_draw`: see their statements in Cb/Ld/LdLkpMaskChain.lean.
  `mj_blind_seq`: see its statement in Cb/Ld/LdLkpMaskChain.lean.
  `mj_step_seq`: a composition steps to a later block if the first steps to the second and the
    second to the later one.
  `mj_chain_cl`: what the whole chain's claim is: the first block's.
  Stated here alone: `mj_chain_blind`: see its statement below; `mj_chain_step`:
    `(D l).Step (D (l + 1))` for all l < n and `(D n).Step D'` give `(MJ.chain X b D n).Step D'`.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskChain

set_option autoImplicit false

namespace Cb
open Iop IOR Prob

theorem mj_seq : Spec.mj_seq := by
  intro E J X₁ X₂ X₃ E₁ E₂ E₃ W₁ W₂ W₃ R₁ R₂ H₁ H₂ D₁ D₂ rd₁ rd₂ rd₃ f₁ f₂ hB hS
  have hL : (D₁.link D₂ rd₁ rd₂).OK H₁ := ⟨f₁.same, f₁.hand, hB.msg, fun _ _ _ _ => rfl, hB.cl, hS⟩
  refine ⟨mm_seq X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ (D₁.data rd₁) (D₂.data rd₂)
      (D₁.link D₂ rd₁ rd₂) f₁.mm f₂.mm hL,
    fun w x c ρ => ?_, fun w x c ρ => ?_⟩
  · rw [Honest.run_seq]
    show rd₃ ((H₂.strat _ _ c.2).run _).2.2 = rd₁ w
    rw [f₂.same, f₁.same]
  · rw [Honest.run_seq]
    show ((H₂.strat _ _ c.2).run _).2.1 =
      D₂.nxt (D₁.nxt x (Plains.fst (Plains.app _ _)) (Rho.fst ρ))
        (Plains.snd (s := R₁.shape) (Plains.app _ _)) (Rho.snd (s := R₁.shape) ρ)
    rw [Plains.fst_app, Plains.snd_app, f₂.hand, f₁.same, f₁.hand]

theorem mj_blind_seq : Spec.mj_blind_seq := by
  intro E J X₁ X₂ X₃ Xi Xo E₁ E₂ E₃ Ei Eo R₁ R₂ R₃ D₁ D₂ D₃ h₁ h₂
  refine ⟨fun M k x ρ => ?_, h₁.cl⟩
  show Plains.app (D₁.msg (D₃.put M k) x (Rho.fst ρ))
      (D₂.msg (D₃.put M k) (D₁.nxt x (D₁.msg (D₃.put M k) x (Rho.fst ρ)) (Rho.fst ρ))
        (Rho.snd (s := R₁.shape) ρ)) =
    Plains.app (D₁.msg k x (Rho.fst ρ))
      (D₂.msg k (D₁.nxt x (D₁.msg k x (Rho.fst ρ)) (Rho.fst ρ)) (Rho.snd (s := R₁.shape) ρ))
  rw [h₁.msg, h₂.msg]

theorem mj_step_seq : Spec.mj_step_seq := by
  intro E J X₁ X₂ X₃ X₄ E₁ E₂ E₃ E₄ R₁ R₂ R₃ D₁ D₂ D₃ h₁ h₂ k x ρ h
  show D₃.Cl
    (D₂.nxt (D₁.nxt x (Plains.fst (Plains.app _ _)) (Rho.fst ρ))
      (Plains.snd (s := R₁.shape) (Plains.app _ _)) (Rho.snd (s := R₁.shape) ρ)) k
  rw [Plains.fst_app, Plains.snd_app]
  exact h₂ k _ _ (h₁ k x _ h)

section Chain
variable {E J K M : Type} {Ex : ExtSpec} {Wp : Type} (X : ℕ → Type)
  (b : ∀ l, BkA K M (X l) (X (l + 1)) Ex Wp) (D : ∀ l, MJ E J (b l).R)

theorem mj_chain_blind {Xi Xo : Type} {Ei Eo : ExtSpec} {R' : IOR Xi Ei Xo Eo} (D' : MJ E J R') :
    ∀ n, (∀ l ≤ n, (D l).Blind D') → (MJ.chain X b D n).Blind D'
  | 0, h => h 0 (le_refl 0)
  | n + 1, h =>
    mj_blind_seq E J _ _ _ _ _ _ _ _ _ _ _ _ _ (MJ.chain X b D n) (D (n + 1)) D'
      (mj_chain_blind D' n fun l hl => h l (Nat.le_succ_of_le hl)) (h (n + 1) (le_refl _))

theorem mj_chain_step :
    ∀ (n : ℕ) {X' : Type} {E' : ExtSpec} {R' : IOR (X (n + 1)) Ex X' E'} (D' : MJ E J R'),
      (∀ l < n, (D l).Step (D (l + 1))) → (D n).Step D' → (MJ.chain X b D n).Step D'
  | 0, _, _, _, _, _, h => h
  | n + 1, _, _, _, D', hs, h =>
      mj_step_seq E J _ _ _ _ _ _ _ _ _ _ _ (MJ.chain X b D n) (D (n + 1)) D'
        (mj_chain_step n (D (n + 1)) (fun l hl => hs l (Nat.lt_succ_of_lt hl))
          (hs n (Nat.lt_succ_self n))) h

end Chain

theorem mj_chain : Spec.mj_chain := by
  intro E J K M Ex Wp X b D rd n
  induction n with
  | zero => intro hF _ _; exact hF 0 (le_refl 0)
  | succ n ih =>
      intro hF hB hS
      exact mj_seq E J _ _ _ _ _ _ _ _ _ _ _ (BkA.chain X b n).H (b (n + 1)).H
        (MJ.chain X b D n) (D (n + 1)) rd rd rd
        (ih (fun l hl => hF l (Nat.le_succ_of_le hl))
          (fun l l' h1 h2 => hB l l' h1 (Nat.le_succ_of_le h2))
          fun l hl => hS l (Nat.lt_succ_of_lt hl))
        (hF (n + 1) (le_refl _))
        (mj_chain_blind X b D (D (n + 1)) n fun l hl =>
          hB l (n + 1) (Nat.lt_succ_of_le hl) (le_refl _))
        (mj_chain_step X b D n (D (n + 1))
          (fun l hl => hS l (Nat.lt_succ_of_lt hl)) (hS n (Nat.lt_succ_self n)))

theorem mj_chain_cl : Spec.mj_chain_cl := by
  intro E J K M Ex Wp X b D n
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem mj_draw : Spec.mj_draw := by
  intro E J X X' Dd _ _ nx Ex W Cl rd
  refine ⟨mm_public X X' Ex Ex (IOR.draw Dd nx Ex) W W (Honest.draw Dd nx Ex W) (J → E) X rd
      (fun x => x) Cl (fun _ _ => ((), ())) ⟨fun p => p.elim (fun e => e.elim) fun e => e.elim⟩
      (fun _ _ => Set.union_empty _) fun _ _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

end Cb
