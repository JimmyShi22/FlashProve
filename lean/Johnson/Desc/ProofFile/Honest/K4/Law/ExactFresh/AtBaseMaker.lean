-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/AtBaseMaker.lean: K4's hand-in for its simulators at
`baseMaker` (E2E/BaseMaker.lean), by that name: two calls of Law/ExactFresh/AtFiles.lean.

  `k4SimulatorAtBaseMaker`   **at every return of `baseMaker files`.**
  `k4SimulatorBaseMakerReturns`   **in scope and live it returns, with all of that.**
  `k4KindPaysAtBaseMaker`   **the three clauses of the kind K4 at its return and the one G.**

Limits. Those of Law/ExactFresh/AtFiles.lean, of which nothing is taken back: THE SPENDER's HALF; fresh
TRUE AND EMPTY; NO JOINT LAW; A := B := False. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.AtFiles
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.KindAtOverlay
import E2E.BaseMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.ExactFresh
open VerifierAndGoals (asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open ProofFile.Honest.Term (baseMaker matrixInput)
open AtPublicFiles.AtFiles

/-- **AT EVERY RETURN OF `baseMaker`, FOR ALL PUBLIC FILES IN SCOPE, READ AND LIVE: THE SPENDER's HALF;
fresh TRUE AND EMPTY; NO JOINT LAW; AT A := B := False.** -/
theorem k4SimulatorAtBaseMaker (files : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (scope : VerifierAndGoals.InScope files = true) (read : VerifierAndGoals.readFiles files = .ok pp)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : baseMaker files = .ok returned) : K4AtBase matrixInput returned :=
  k4SimulatorAtTheFiles files scope read live matrixInput OnBytes.secondHashFunction _ openHonest made

/-- **IN SCOPE AND LIVE `baseMaker` RETURNS, AND ALL OF IT STANDS THERE: THE SPENDER's HALF; fresh TRUE
AND EMPTY; NO JOINT LAW; AT A := B := False.** -/
theorem k4SimulatorBaseMakerReturns (files : VerifierAndGoals.PublicFiles) (scope : VerifierAndGoals.InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) :
    ∃ returned, baseMaker files = .ok returned ∧ K4AtBase matrixInput returned :=
  k4SimulatorAtTheMatrices files scope live _ openHonest

/-- **THE THREE CLAUSES OF THE KIND K4 AT `baseMaker`'s RETURN AND THE ONE G, FOR ALL PUBLIC FILES IN
SCOPE, READ AND LIVE: THE SPENDER's HALF; fresh TRUE AND EMPTY; NO JOINT LAW; A' := B' := False.**
mine, hk, hm, R, hR: the rows that `overlaySlots` lays with K4's slot among a kind's own lots. Lt, hbare:
letters that keep a row. -/
theorem k4KindPaysAtBaseMaker {Ky X₀ : Type} (files : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (scope : VerifierAndGoals.InScope files = true) (read : VerifierAndGoals.readFiles files = .ok pp)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : baseMaker files = .ok returned)
    (mine : List (SLot (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst))
    (hk : (mine.find? fun s => s.name == "K4") =
      some (k4SLotByPub id matrixInput.weights fun _ _ => k4LookAt))
    (hm : ∀ L ∈ (ProofFile.Honest.Term.baseFilling files).lots, ∀ s,
      (mine.find? fun s => s.name == L.name) = some s →
      (s.rows returned.Z returned.G).map (·.half) = L.halves returned.Z returned.G)
    (R : AtPublicFiles.TheSides.Rows FullSizeMatrix IndexCommitterCoins ProofFile.Inst Ky Cells X₀ Unit)
    (hR : R.first = rowsOfLots returned.Z returned.G
      ((ProofFile.Honest.Term.baseFilling files).lots.map (AtPublicFiles.TheSides.overlayLot mine)))
    (Lt : AtPublicFiles.TheSides.Letters returned.F returned.B FullSizeMatrix IndexCommitterCoins Ky Cells X₀ Unit)
    (hbare : ∀ q, (Lt.first q).bare = q) (f₁ : List (Fall returned.F.S₁))
    (f₂ : List (Fall returned.F.S₂)) (f₃ : List (Fall returned.F.S₃)) :
    (∀ L ∈ (AtPublicFiles.TheSides.theSides returned.F Lt R f₁ f₂ f₃).first, L.place.kind = .K4 →
      ∀ σ, L.side returned.F.first.blocksInOrder f₁ = some σ →
      ∃ A' B', Good (preOf 0 0 (earlierOf returned.F 0) returned.F.first.blocksInOrder L.place) .own σ
        returned.B (orderOf returned.F) 0 0 A' B' L.On L.bud) ∧
    (∀ L ∈ (AtPublicFiles.TheSides.theSides returned.F Lt R f₁ f₂ f₃).shared, L.place.kind = .K4 →
      ∀ σ, L.side returned.F.shared.blocksInOrder f₂ = some σ →
      ∃ A' B', Good (preOf 1 0 (earlierOf returned.F 1) returned.F.shared.blocksInOrder L.place) .shared σ
        returned.B (orderOf returned.F) 1 0 A' B' L.On L.bud) ∧
    ∀ L ∈ (AtPublicFiles.TheSides.theSides returned.F Lt R f₁ f₂ f₃).second, L.place.kind = .K4 →
      ∀ σ, L.side returned.F.second.blocksInOrder f₃ = some σ →
      ∃ A' B', Good (preOf 2 returned.F.lastChainFirstTreeNumber (earlierOf returned.F 2) returned.F.second.blocksInOrder
          L.place) .own σ returned.B (orderOf returned.F) 2 returned.F.lastChainFirstTreeNumber A' B' L.On L.bud := by
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_of_live files scope read live
  exact k4KindPaysAtOverlay h matrixInput OnBytes.secondHashFunction _ openHonest made mine hk hm R hR Lt hbare
    f₁ f₂ f₃

end ProofFile.Honest.K4.ExactFresh

#print axioms ProofFile.Honest.K4.ExactFresh.k4SimulatorAtBaseMaker
#print axioms ProofFile.Honest.K4.ExactFresh.k4SimulatorBaseMakerReturns
#print axioms ProofFile.Honest.K4.ExactFresh.k4KindPaysAtBaseMaker
