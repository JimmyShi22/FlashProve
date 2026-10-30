-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/K5/AtFull.lean: the head's example: THREE OF THE FOUR PARTS OF THE LOT's TEST AT
A PLAN (`k5LotB_of_Q`, Johnson/Desc/First/Att/Row/K5LotNoPad.lean: h₁ · h₂ · h₄) AT ALL TWELVE
ATTENTION PLANS OF publicOfO's OWN VALUE AT THE STORED FULL-SIZE FILES. A joining: the twelve closed
facts g0 … g11 (Johnson/AtFull/K5/G0.lean … G11.lean) through `own_of_atOwn`
(Johnson/AtFull/K5/OwnTie.lean).
  **`k5Q_zFull_of_rest`**: from hsz (the layout file has 224,975 bytes): ∃ W, publicOfO returns W at
    the three files ∧ ∀ g < 12, ∃ a, W.A[g]? = some a ∧ nRounds a.own = 162 ∧
    planOkOwn a.own = true ∧ claimsOkAtQ a = true.

Limits. hsz IS A PREMISE: until it is laid in this is an "if". The fourth part (h₃: the test on the
padding keys accepts) IS NOT HERE, and nothing here says who shows it. Nothing on soundness.

-/
import Johnson.AtFull.K5.OwnTie
import Johnson.AtFull.K5.G0
import Johnson.AtFull.K5.G1
import Johnson.AtFull.K5.G2
import Johnson.AtFull.K5.G3
import Johnson.AtFull.K5.G4
import Johnson.AtFull.K5.G5
import Johnson.AtFull.K5.G6
import Johnson.AtFull.K5.G7
import Johnson.AtFull.K5.G8
import Johnson.AtFull.K5.G9
import Johnson.AtFull.K5.G10
import Johnson.AtFull.K5.G11

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.K5
open OnBytes OnBytes.Model
open VerifiableInference.PlanWritten (publicOfO)
open VerifiableInference.Desc.First VerifiableInference.Desc.First.Att.P H2K5.Row

/-- The twelve closed facts as one statement. -/
theorem g_all : ∀ g, g < 12 → atOwn g k5Q3 = true
  | 0, _ => g0 | 1, _ => g1 | 2, _ => g2 | 3, _ => g3 | 4, _ => g4 | 5, _ => g5
  | 6, _ => g6 | 7, _ => g7 | 8, _ => g8 | 9, _ => g9 | 10, _ => g10 | 11, _ => g11
  | n + 12, h => absurd h (by omega)

/-- **Under hsz: three of the four parts, at publicOfO's own twelve plans.** -/
theorem k5Q_zFull_of_rest (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) :
    ∃ W : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok W ∧
      ∀ g, g < 12 → ∃ a, W.A[g]? = some a ∧ nRounds a.own = 162 ∧ planOkOwn a.own = true ∧
        claimsOkAtQ a = true := by
  obtain ⟨W, hX, H⟩ := own_of_atOwn hsz
  refine ⟨W, hX, fun g hg => ?_⟩
  obtain ⟨a, ha, hf⟩ := H g k5Q3 (g_all g hg)
  unfold k5Q3 at hf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
  exact ⟨a, ha, hf.1.1, hf.1.2, hf.2⟩

end Johnson.AtFull.K5

#print axioms Johnson.AtFull.K5.g_all
#print axioms Johnson.AtFull.K5.k5Q_zFull_of_rest
