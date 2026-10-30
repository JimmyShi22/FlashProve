-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdZkPair.lean: zero knowledge of the encoding of two codes side by side from zero knowledge of
each.

Statement (`Spec.ld_zk_pair`) and proof. The analogue, for two codes side by side, of
Cb/Ld/LdSumZkRows.lean (rows of an interleaving).
The file follows the paper that this protocol builds on (lean/CREDITS.md).
In a standard group (Cb/Ld/LdGroupStd.lean) an oracle message holds main rows under a base code
beside mask rows under a mask code (Cb/Ld/LdRel.lean: `LdCode.pair`); the statement is on any two
codes. The two sides are encoded with independent randomness and are read at common long positions;
so the pair hides t long positions if each side does (`LdCode.Zk t`, Cb/Ld/LdRel.lean). All errors
are 0. E is finite and not empty (`[Nonempty E]`). (That paper has this for components read under a
repetition, with the errors added; here each side has any transformation to the common long
positions.) The proof renames the randomness side by side (Prob/LawEquiv.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRel
import Prob.LawEquiv
import Prob.LawKit

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

namespace Spec

def ld_zk_pair : Prop :=
  ∀ (E P : Type) [Fintype E] [Nonempty E] (C₁ C₂ : LdCode E P) (t : ℕ),
    C₁.Zk t → C₂.Zk t → (C₁.pair C₂).Zk t

end Spec

theorem ld_zk_pair : Spec.ld_zk_pair := by
  classical
  intro E P _ _ C₁ C₂ t h₁ h₂ S hS m m'
  obtain ⟨X, hX, hSX⟩ := hS
  have b₁ : C₁.budT t S.toLeft := ⟨X, hX, fun p hp => by
    obtain ⟨x, hx, hpx⟩ := Finset.mem_biUnion.1 (hSX (Finset.mem_toLeft.1 hp))
    exact Finset.mem_biUnion.2 ⟨x, hx, Finset.inl_mem_disjSum.1 hpx⟩⟩
  have b₂ : C₂.budT t S.toRight := ⟨X, hX, fun p hp => by
    obtain ⟨x, hx, hpx⟩ := Finset.mem_biUnion.1 (hSX (Finset.mem_toRight.1 hp))
    exact Finset.mem_biUnion.2 ⟨x, hx, Finset.inr_mem_disjSum.1 hpx⟩⟩
  obtain ⟨e₁, he₁⟩ :=
    exists_equiv_of_map_eq _ _ (h₁ S.toLeft b₁ (fun j => m (.inl j)) fun j => m' (.inl j))
  obtain ⟨e₂, he₂⟩ :=
    exists_equiv_of_map_eq _ _ (h₂ S.toRight b₂ (fun j => m (.inr j)) fun j => m' (.inr j))
  refine map_unif_reindex
    ((Equiv.sumArrowEquivProdArrow C₁.Q C₂.Q E).trans
      ((Equiv.prodCongr e₁ e₂).trans (Equiv.sumArrowEquivProdArrow C₁.Q C₂.Q E).symm))
    _ _ fun r => ?_
  funext p
  obtain ⟨p, hp⟩ := p
  rcases p with p | p
  · have h :=
      eq_of_heq (Sigma.mk.inj (congrFun (he₁ fun q => r (.inl q)) ⟨p, Finset.mem_toLeft.2 hp⟩)).2
    exact Sigma.ext rfl (heq_of_eq h)
  · have h :=
      eq_of_heq (Sigma.mk.inj (congrFun (he₂ fun q => r (.inr q)) ⟨p, Finset.mem_toRight.2 hp⟩)).2
    exact Sigma.ext rfl (heq_of_eq h)

end Cb
