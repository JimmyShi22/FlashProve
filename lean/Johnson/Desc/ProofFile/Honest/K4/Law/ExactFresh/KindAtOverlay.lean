-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/KindAtOverlay.lean: the three clauses of the rule's
premises at the kind K4 (index privacy's `KindPays G .K4`, to the letter) at the one G: the rows that
IOP's `overlaySlots` (E2E/TheSides.lean) lays at the base filling with K4's lot `k4SLotByPub` among a
kind's own lots. CONDITIONAL: on h, hA, and on the slot's being K4's.

  `k4KindHandsInAtReturn`   `k4KindHandsIn` at the maker's own description.
  `k4_row_of_overlay`   a row of the overlaid lots at a place of the kind K4 is a row of K4's lot.
  `k4KindPaysAtOverlay`   **the three clauses at `theSides` of those rows.**

Limits. THE SPENDER's HALF; fresh TRUE AND EMPTY; NO JOINT LAW; `Good` at A and B False; in the shared
and the second chain the clauses hold because no such list has a side. Letters: whatever they are, so
long as they keep a row (hbare). No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.KindHandsIn
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.AtBase
import E2E.TheSides

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.ExactFresh
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open P5J (AtMgA TS)
open AtPublicFiles.TheSides

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h, hA and the one premise on the lists. **`k4KindHandsIn` AT THE MAKER's OWN
DESCRIPTION: THE SPENDER's HALF; fresh TRUE AND EMPTY; NO JOINT LAW; A' := B' := False.** -/
theorem k4KindHandsInAtReturn {W₀ Rc Ky Tr X₀ X W₂ Rc₂ Tr₂ X₂ X₀₂ : Type}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {P : OnlineProverParts W₂ Rc₂ Tr₂ X₀₂ X₂} {A : OnlineProverWithDescription W₂ Rc₂ Tr₂ X₀₂ X₂}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (cells : Tr → Cells)
    (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    (G : Sides A.F A.B W₀ Rc Ky Tr X₀ X)
    (only : ∀ L ∈ G.first, L.place.kind = .K4 → L.bare ∈ (k4SLot cells weights look).rows A.Z A.G) :
    (∀ L ∈ G.first, L.place.kind = .K4 → ∀ σ, L.side A.F.first.blocksInOrder G.falls₁ = some σ →
      ∃ A' B', Good (preOf 0 0 (earlierOf A.F 0) A.F.first.blocksInOrder L.place) .own σ A.B (orderOf A.F) 0 0
        A' B' L.On L.bud) ∧
    (∀ L ∈ G.shared, L.place.kind = .K4 → ∀ σ, L.side A.F.shared.blocksInOrder G.falls₂ = some σ →
      ∃ A' B', Good (preOf 1 0 (earlierOf A.F 1) A.F.shared.blocksInOrder L.place) .shared σ A.B (orderOf A.F)
        1 0 A' B' L.On L.bud) ∧
    ∀ L ∈ G.second, L.place.kind = .K4 → ∀ σ, L.side A.F.second.blocksInOrder G.falls₃ = some σ →
      ∃ A' B', Good (preOf 2 A.F.lastChainFirstTreeNumber (earlierOf A.F 2) A.F.second.blocksInOrder L.place) .own σ A.B
        (orderOf A.F) 2 A.F.lastChainFirstTreeNumber A' B' L.On L.bud := by
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF :=
    Except.ok.inj ((atPure_ok hA).2.2.1.symm.trans h.laid.value)
  obtain ⟨AZ, AG, AF, AB, AH, Ar, Arows⟩ := A
  dsimp only at eF G only ⊢
  subst eF
  exact k4KindHandsIn h hA cells weights look G only

variable {W₀ : Type}

/-- **A row of the overlaid lots at a place of the kind K4 is a row of K4's lot**, at the base filling,
where K4's slot is the one named "K4". -/
theorem k4_row_of_overlay (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Zq : ProofFile.Pub) (Gr : ProofFile.Ground)
    (mine : List (SLot (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst))
    (hk : (mine.find? fun s => s.name == "K4") =
      some (k4SLotByPub id I.weights fun _ _ => k4LookAt))
    (hm : ∀ L ∈ (onlineProverPartsInUse I o S O).lots, ∀ s, (mine.find? fun s => s.name == L.name) = some s →
      (s.rows Zq Gr).map (·.half) = L.halves Zq Gr)
    {row : Unlettered (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst}
    (hr : row ∈ rowsOfLots Zq Gr ((onlineProverPartsInUse I o S O).lots.map (overlayLot mine)))
    (hkind : row.place.kind = .K4) :
    row ∈ (k4SLotByPub (Rc := IndexCommitterCoins) (X := Unit) id I.weights fun _ _ => k4LookAt).rows Zq Gr := by
  obtain ⟨s, hs, hrs⟩ := List.mem_flatMap.1 hr
  obtain ⟨L₀, hL₀, rfl⟩ := List.mem_map.1 hs
  have hhalf : row.half ∈ L₀.halves Zq Gr := by
    rw [← overlay_half (hm L₀ hL₀)]
    exact List.mem_map_of_mem hrs
  have hpair := lot_of_kind I o S O Zq Gr L₀ hL₀ row.half hhalf hkind
  have hL : ((HLot.byPub I.weights fun wt => k4HLot id wt fun _ _ => k4LookAt),
      KindName.K4) ∈ widerPairs I o S O :=
    List.mem_of_getElem? (i := 6) rfl
  obtain rfl := pair_only I o S O hL (by decide) L₀ hpair
  have eo : overlayLot mine (HLot.byPub I.weights fun wt => k4HLot id wt fun _ _ => k4LookAt) =
      k4SLotByPub id I.weights fun _ _ => k4LookAt := by
    have en : (HLot.byPub (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (W := Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
        (X := Unit) I.weights fun wt => k4HLot id wt fun _ _ => k4LookAt).name = "K4" := rfl
    unfold overlayLot
    rw [en, hk]
  rw [eo] at hrs
  exact hrs

/-- CONDITIONAL: on h, hA and K4's slot. **THE THREE CLAUSES AT THE ONE G: THE SPENDER's HALF; fresh
TRUE AND EMPTY; NO JOINT LAW; A' := B' := False.** s: the rows that `overlaySlots` lays. Lt: letters
that keep a row. -/
theorem k4KindPaysAtOverlay {Ky X₀ : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o S O) = .ok A)
    (mine : List (SLot (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst))
    (hk : (mine.find? fun s => s.name == "K4") =
      some (k4SLotByPub id I.weights fun _ _ => k4LookAt))
    (hm : ∀ L ∈ (onlineProverPartsInUse I o S O).lots, ∀ s, (mine.find? fun s => s.name == L.name) = some s →
      (s.rows A.Z A.G).map (·.half) = L.halves A.Z A.G)
    (R : AtPublicFiles.TheSides.Rows W₀ IndexCommitterCoins ProofFile.Inst Ky Cells X₀ Unit)
    (hR : R.first = rowsOfLots A.Z A.G ((onlineProverPartsInUse I o S O).lots.map (overlayLot mine)))
    (Lt : AtPublicFiles.TheSides.Letters A.F A.B W₀ IndexCommitterCoins Ky Cells X₀ Unit) (hbare : ∀ q, (Lt.first q).bare = q)
    (f₁ : List (Fall A.F.S₁)) (f₂ : List (Fall A.F.S₂)) (f₃ : List (Fall A.F.S₃)) :
    (∀ L ∈ (theSides A.F Lt R f₁ f₂ f₃).first, L.place.kind = .K4 →
      ∀ σ, L.side A.F.first.blocksInOrder f₁ = some σ →
      ∃ A' B', Good (preOf 0 0 (earlierOf A.F 0) A.F.first.blocksInOrder L.place) .own σ A.B (orderOf A.F) 0 0
        A' B' L.On L.bud) ∧
    (∀ L ∈ (theSides A.F Lt R f₁ f₂ f₃).shared, L.place.kind = .K4 →
      ∀ σ, L.side A.F.shared.blocksInOrder f₂ = some σ →
      ∃ A' B', Good (preOf 1 0 (earlierOf A.F 1) A.F.shared.blocksInOrder L.place) .shared σ A.B (orderOf A.F)
        1 0 A' B' L.On L.bud) ∧
    ∀ L ∈ (theSides A.F Lt R f₁ f₂ f₃).second, L.place.kind = .K4 →
      ∀ σ, L.side A.F.second.blocksInOrder f₃ = some σ →
      ∃ A' B', Good (preOf 2 A.F.lastChainFirstTreeNumber (earlierOf A.F 2) A.F.second.blocksInOrder L.place) .own σ A.B
        (orderOf A.F) 2 A.F.lastChainFirstTreeNumber A' B' L.On L.bud := by
  refine k4KindHandsInAtReturn h hA id (I.weights A.Z) (fun _ _ => k4LookAt) _ ?_
  intro L hL hkind
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hL
  rw [hbare]
  have hq' : q ∈ rowsOfLots A.Z A.G ((onlineProverPartsInUse I o S O).lots.map (overlayLot mine)) :=
    hR ▸ hq
  have hk' : q.place.kind = .K4 := by rw [← (Lt.keeps₁ q).1]; exact hkind
  exact k4_row_of_overlay I o S O A.Z A.G mine hk hm hq' hk'

end ProofFile.Honest.K4.ExactFresh

#print axioms ProofFile.Honest.K4.ExactFresh.k4KindHandsInAtReturn
#print axioms ProofFile.Honest.K4.ExactFresh.k4_row_of_overlay
#print axioms ProofFile.Honest.K4.ExactFresh.k4KindPaysAtOverlay
