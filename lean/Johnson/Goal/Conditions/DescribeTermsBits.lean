-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/DescribeTermsBits.lean: THE GOAL ON BINDING WITH A SECURITY LEVEL, G9bits
(Ladder/Bits.lean), AT A DESCRIPTION WITH THE HONEST SIDE'S TERMS LAID IN
(Johnson/Goal/Conditions/DescribeTerms.lean): from the same laws `BindLaws` as G9, where the coins'
algorithm asks at most 2^40 queries. General in the description. A statement with its proof. A
conditional: no description is built.

Main name (namespace `VerifierAndGoals.Fit`).
  **`G9bits_withTerms`**: the term `G9bits fun o => (D o).withTerms (Q o)`: `BindsAt` at the error
    `bindingErrorInQueries`. By `G9bits_of_bindAt` (Ladder/FitBindsBits.lean) at tMax := `honestBudget` =
    2^48: its one condition on numbers, 2 tMax + q + 2 ≤ 2^50, is arithmetic.

WHO READS EACH LETTER: as in Johnson/Goal/Conditions/DescribeTerms.lean.
NOTHING THAT THE VERIFIER READS STANDS UNDER "THERE IS": the statement has none.

Limits. Those of Johnson/Goal/Conditions/DescribeTerms.lean and Ladder/FitBindsBits.lean.
`bindingErrorInQueries` and the other numbers of Ladder/Bits.lean are choices of this project: what level they
spell is said there, not here. THE VERIFIER IS IDLE. THE COMMITTER IS TIED TO NO PROGRAM.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.DescribeTerms
import Ladder.FitBindsBits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat
open scoped ENNReal

/-- **THE STORED G9bits**, at every family of descriptions with the terms laid in. -/
theorem G9bits_withTerms (D : SecondHashFunctionType → Description) (Q : ∀ o, HonestTerms (D o)) (tP q : ℕ)
    (hq : q ≤ 2 ^ 40)
    (h : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      BindLaws (Q OnBytes.secondHashFunction) Z (settingsOfRead pp) tP q) :
    G9bits fun o => (D o).withTerms (Q o) :=
  G9bits_of_bindAt (fun o => (D o).withTerms (Q o)) honestBudget q
    (by
      have h1 : honestBudget = 2 ^ 48 := rfl
      have h2 : (2 : ℕ) ^ 48 = 281474976710656 := by norm_num
      have h3 : (2 : ℕ) ^ 50 = 1125899906842624 := by norm_num
      have h4 : (2 : ℕ) ^ 40 = 1099511627776 := by norm_num
      rw [h4] at hq
      rw [h1, h2, h3]
      omega)
    (fun Z pp h₁ h₂ => bindAt_withTerms (h Z pp h₁ h₂))
    (fun Z pp h₁ h₂ => commitWithin_withTerms (h Z pp h₁ h₂)) (fun _ _ _ _ => rfl)
    fun Z pp h₁ h₂ => ⟨le_trans (Nat.le_succ _) (le_trans (Nat.le_add_left _ q)
      (h Z pp h₁ h₂).number), le_refl q⟩

end VerifierAndGoals.Fit

#print axioms VerifierAndGoals.Fit.G9bits_withTerms
