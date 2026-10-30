-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WField.lean: the clause `field` of `StandAtW` (WAccepted.lean),
from the letter of the last chain.

  `field_of_said_W`  where the letter gives `SaidField` at `BaseTied` (Thread/SaidField.lean,
                   Thread/BaseTied.lean) at number b: `FieldAtW`

Limits. That a letter gives it at a stand is the letter's: `SaidNext` at the members in front and
`baseTied_at_door` at the start. NOT IN FRONT OF A LAW OVER COINS. Nothing on completeness, on soundness
or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WAccepted
import Johnson.Desc.ProofFile.Honest.Thread.BaseTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open VerifiableInference.Desc (FileDescription)

variable {Xi W₀ Rc Tr X V Pb : Type} {Bk : ProverCoinCounts} {F : FileDescription Xi}

/-- **The clause `field`, from the letter.** -/
theorem field_of_said_W (T : Thread Bk F.S₃ F.Cl V (Local W₀ Rc Xi Tr) X Pb)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (b : ℕ)
    (hS : ∀ k m, Said b k m → SaidField T (BaseTied F T) b k m) : FieldAtW F T Said b := by
  intro k st m E u
  obtain ⟨base, cols, hB, hc, ho⟩ := opened_of_saidField T u.1 (hS k m u.2)
  obtain ⟨r₁, r₂, rest, c₁, c₂, e₁, e₂, h0, h1, h2, h3, h4, h5, h6, h7, -, h9⟩ := hB
  exact ⟨base, cols, e₁, e₂, ⟨r₁, r₂, rest, c₁, c₂, h0, h1, h2, h3, h4, h5, h6, h7⟩, hc, ho, h9⟩

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.field_of_said_W
