-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/ThruAlongFromJ.lean: the rule with sentences on the verifier's state
(Honest/Law/ThreadStratCJ.lean) gives the yes at the run with them: its premises are ThreadsP and
YesAlongJ.

  ThreadsCJ.toP, ThreadsCJ.along

By what. SaysYesJ.along (Honest/ThruAlongJ.lean).

Limits. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.ThruAlongJ
import Johnson.Desc.ProofFile.Honest.Law.ThreadStratCJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
  {R : Ready W₀ Rc Xi Ky Tr X₀ X}

/-- The part of ThreadsCJ that the run's return reads. -/
def ThreadsCJ.toP (T : ThreadsCJ F Bk H w₀ rc x k R) : ThreadsP F Bk H w₀ rc x k R where
  I₁ := T.I₁
  I₂ := T.I₂
  I₃ := T.I₃
  h₁ := T.h₁
  h₂ := T.h₂
  h₃ := T.h₃
  a₁ := T.a₁
  a₂ := T.a₂
  a₃ := T.b₃

/-- **ThreadsCJ gives YesAlongJ, at every run.** -/
theorem ThreadsCJ.along (T : ThreadsCJ F Bk H w₀ rc x k R) (ρ : Draws) (r : RunC F) :
    YesAlongJ ρ r T.toP T.f₁ T.f₂ T.f₃ T.J₁ T.J₂ T.J₃ where
  y₁ := fun j b hb => SaysYesJ.along (L := ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩) (T.y₁ j b hb) _ _ _ _ _ _
  y₂ := fun j b hb => SaysYesJ.along (L := ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩) (T.y₂ j b hb) _ _ _ _ _ _
  y₃ := fun z₁ z₂ _ _ j b hb =>
    SaysYesJ.along (L := ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩)
      (T.y₃ j b hb) _ _ _ _ _ _
  c₁ := T.c₁
  c₂ := T.c₂
  c₃ := T.c₃
  j₁ := T.j₁
  j₂ := T.j₂
  st₃ := fun e₁ m₁ E₁ e₂ m₂ E₂ _ _ _ _ i₁ i₂ _ _ g₁ g₂ => by
    obtain ⟨s₃, hs⟩ := T.d₃ e₁ m₁ E₁ e₂ m₂ E₂ i₁ i₂ g₁ g₂
    exact ⟨s₃, hs, T.j₃ e₁ e₂ s₃ g₁ g₂ hs⟩
  fin := fun e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃ _ i₁ i₂ i₃ g₁ g₂ g₃ =>
    T.fin e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃ i₁ i₂ i₃ g₁ g₂ g₃

end ProofFile.Honest

#print axioms ProofFile.Honest.ThreadsCJ.toP
#print axioms ProofFile.Honest.ThreadsCJ.along
