-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/KindPaysAtBase.lean: `KindPays … .K4` by its name, at
`baseMaker`'s return, through H2's kind-free law `kindPays_of_lot` (E2E/KindPaysOfALot.lean).

  `kindPays_K4_at_base`   **in scope and live: the maker returns, `K4AtBase` stands there, and KindPays
      at the kind K4 holds at the sides of every overlay whose lots hold K4's slot, at letters that
      narrow.**

Limits. Those of Law/ExactFresh/AtFiles.lean, of which nothing is taken back: THE SPENDER's HALF;
fresh TRUE AND EMPTY; NO JOINT LAW; A' := B' := False. In the shared and the second chain KindPays
holds for want of a block: TRUE AND EMPTY THERE. At the base filling. Letters that hold nowhere narrow
and leave exact and fresh asked nowhere: what a run meets is the rule's other premises. No property is
claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.AtBaseMaker
import E2E.KindPaysOfALot

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.ExactFresh
open VerifierAndGoals (asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open ProofFile.Honest.Term (baseMaker baseFilling matrixInput)
open VerifiableInference.Desc (KindName)
open VerifiableInference.Compilation (KindPays)
open AtPublicFiles.AtFiles
open AtPublicFiles.TheSides (Letters Narrows overlaySlots theSides block_of_seated kindPays_of_lot)

/-- K4's slot at the base filling. -/
noncomputable abbrev k4BaseSlot : SLot (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst :=
  k4SLotByPub id matrixInput.weights fun _ _ => k4LookAt

/-- **IN SCOPE AND LIVE: `baseMaker` RETURNS; K4's HAND-IN STANDS THERE; AND KindPays AT THE KIND K4 HOLDS
AT THE SIDES OF EVERY OVERLAY WITH K4's SLOT, AT LETTERS THAT NARROW: THE SPENDER's HALF; fresh TRUE
AND EMPTY; NO JOINT LAW; A' := B' := False.** -/
theorem kindPays_K4_at_base (files : VerifierAndGoals.PublicFiles) (scope : VerifierAndGoals.InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) :
    ∃ A, baseMaker files = .ok A ∧ K4AtBase matrixInput A ∧
      ∀ (mine : List (SLot (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit
          ProofFile.Inst))
        (named : ∀ s ∈ mine, (ProofFile.Honest.Term.baseFilling files).lots.any
          (fun L => L.name == s.name) = true)
        (apart : (mine.map (·.name)).Nodup)
        (hm : ∀ L ∈ (baseFilling files).lots, ∀ s, (mine.find? fun s => s.name == L.name) = some s →
          (s.rows A.Z A.G).map (·.half) = L.halves A.Z A.G)
        (shared : List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins OnBytes.TableKey) Unit OnBytes.TableKey))
        (hs : shared.map (·.half) = (baseFilling files).shared A.Z A.G)
        (second : List (Unlettered (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit
          ProofFile.Inst))
        (h₃ : second.map (·.half) = (baseFilling files).second A.Z A.G)
        (Ls : Letters A.F A.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit)
        (f₁ : List (Fall A.F.S₁)) (f₂ : List (Fall A.F.S₂)) (f₃ : List (Fall A.F.S₃)),
        k4BaseSlot ∈ mine → (∀ u, Narrows (Ls.first u) u) →
        KindPays (theSides A.F Ls
          (overlaySlots (baseFilling files) A.Z A.G mine named apart hm shared hs second h₃).rows
          f₁ f₂ f₃) .K4 := by
  obtain ⟨pp, read⟩ := LPFPol.read_of_scope scope
  obtain ⟨A, made, hb⟩ := k4SimulatorBaseMakerReturns files scope live
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_of_live files scope read live
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF :=
    Except.ok.inj ((atPure_ok made).2.2.1.symm.trans h.laid.value)
  have plan : A.F.planOk = true := eF ▸ h.laid.planOk
  obtain ⟨n2, n3⟩ := noK4PlaceInTheLaterChains (atPure_ok made).2.2.1 plan
  refine ⟨A, made, hb, ?_⟩
  intro mine named apart hm shared hs second h₃ Ls f₁ f₂ f₃ hslot hn
  refine kindPays_of_lot mine named apart hm shared hs second h₃ Ls f₁ f₂ f₃ .K4 [k4BaseSlot]
    (fun l hl => by rw [List.mem_singleton.1 hl]; exact hslot) ?_ ?_ ?_ ?_
  · intro M hM
    by_cases hx : ∃ y ∈ M.halves A.Z A.G, y.place.kind = .K4
    · obtain ⟨y, hy, hk⟩ := hx
      have hL : ((HLot.byPub matrixInput.weights fun wt => k4HLot id wt fun _ _ => k4LookAt),
          KindName.K4) ∈ widerPairs matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest :=
        List.mem_of_getElem? (i := 6) rfl
      obtain rfl := pair_only matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest hL
        (by decide) M (lot_of_kind _ _ _ _ A.Z A.G M hM y hy hk)
      exact Or.inl ⟨k4BaseSlot, List.mem_singleton.2 rfl, rfl⟩
    · exact Or.inr fun y hy hk => hx ⟨y, hy, hk⟩
  · intro l hl u hu _ σ hσ
    obtain rfl := List.mem_singleton.1 hl
    exact ⟨hn u, _, _, (hb.2.1.atEveryRow u hu).good f₁ σ hσ _ .own _ 0 0⟩
  · intro u _ hk σ hσ
    obtain ⟨b, hbk, e⟩ := block_of_seated hσ
    exact absurd (e ▸ hk) (n2 b hbk)
  · intro u _ hk σ hσ
    obtain ⟨b, hbk, e⟩ := block_of_seated hσ
    exact absurd (e ▸ hk) (n3 b hbk)

end ProofFile.Honest.K4.ExactFresh

#print axioms ProofFile.Honest.K4.ExactFresh.kindPays_K4_at_base
