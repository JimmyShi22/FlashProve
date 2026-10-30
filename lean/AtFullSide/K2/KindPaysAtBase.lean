-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/KindPaysAtBase.lean: KindPays at the sides that E2E/TheSides.lean builds at the base
filling, for the kind "the code switch" (K2), by the one lemma kindPays_of_lot.

  lots_alone         of the base filling's lots every lot but the kind's lays no side of the kind
  kindPays_k2_at_base   the statement: its letters are the caller's: the list mine holds this kind's
                     lot with its simulators, and the letters narrow On and the bound at most

By: simulatorAtTheBase (SidesMeetGood), others_no_kind, kindPays_of_lot (E2E/KindPaysOfALot.lean).

Limits. KindPays holds of a G without a row of the kind for want of rows: what ties G to the base
filling is mine, named, hm. All limits of simulatorAtTheBase hold.
-/
import AtFullSide.K2.SimulatorAtTheBaseProof
import E2E.KindPaysOfALot

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K2
open ProofFile.Honest ProofFile.Honest.Term ProofFile.Honest.K2 ProofFile.Honest.FirstFill
open AtPublicFiles.AtFiles AtPublicFiles.Cut
open AtPublicFiles.TheSides
open VerifiableInference.Desc (KindName)
open VerifiableInference.Compilation (KindPays)

/-- **No other lot of the base filling lays a side of the kind.** -/
theorem lots_alone {W₀ : Type} (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots, M.name = (switchFillLot I S).name ∨
      ∀ x ∈ M.halves Z G, x.place.kind ≠ .K2 := by
  intro M hM
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((h | rfl) | rfl) | rfl
  · rw [widerFillAt_lots] at h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
    by_cases k : q.2 = .K2
    · have e : q = (switchFillLot I S, .K2) :=
        List.inj_on_of_nodup_map widerPairs_nodup hq
          (List.Mem.tail _ (List.Mem.head _)) k
      exact .inl (by rw [e])
    · exact .inr fun x hx e => k (((widerKinds I o S O Z G).all q hq x hx).symm.trans e)
  · exact .inr fun x hx e => by
      have t := closeLotAt_kinds I S Z G x hx
      rw [e] at t
      cases t
  · exact .inr fun x hx e => by
      have t := proxLotAt_kinds I S Z G x hx
      rw [e] at t
      cases t
  · refine .inr fun x hx e => ?_
    rw [wLotAt_halves] at hx
    cases hm : OnBytes.linMessageW Z.first.lin with
    | none =>
      rw [hm] at hx
      cases hx
    | some msg =>
      rw [hm] at hx
      obtain rfl := List.mem_singleton.1 hx
      cases e

/-- **The kind pays at the sides built at the base filling.** -/
theorem kindPays_k2_at_base {Z : VerifierAndGoals.PublicFiles} (scope : VerifierAndGoals.InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    (mine : List (SLot (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst))
    (named : ∀ s ∈ mine, (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
      openHonest).lots.any (fun L => L.name == s.name) = true)
    (apart : (mine.map (·.name)).Nodup)
    (hm : ∀ L ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
        openHonest).lots, ∀ s, (mine.find? fun s => s.name == L.name) = some s →
      (s.rows A.Z A.G).map (·.half) = L.halves A.Z A.G)
    (shared : List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins OnBytes.TableKey) Unit OnBytes.TableKey))
    (hs : shared.map (·.half) = (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction
      OnBytes.HonestTrace.Sz.ref openHonest).shared A.Z A.G)
    (second : List (Unlettered (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit
      ProofFile.Inst))
    (h₃ : second.map (·.half) = (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction
      OnBytes.HonestTrace.Sz.ref openHonest).second A.Z A.G)
    (Ls : Letters A.F A.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit)
    (f₁ : List (Fall A.F.S₁)) (f₂ : List (Fall A.F.S₂)) (f₃ : List (Fall A.F.S₃))
    (hmine : baseSimLot ∈ mine)
    (hN : ∀ u ∈ baseSimLot.rows A.Z A.G, Narrows (Ls.first u) u) :
    KindPays (theSides A.F Ls
      (overlaySlots _ A.Z A.G mine named apart hm shared hs second h₃).rows f₁ f₂ f₃) .K2 := by
  obtain ⟨pp, read⟩ := H2K.Sizes.inScope_readFiles scope
  obtain ⟨Zp, Np, cF, x₀, h⟩ := P5J.head_exists_at_name Z scope read live (P5J.owed_of_live live)
  obtain ⟨-, -, hG, -⟩ := simulatorAtTheBase.2.2 Z scope live
  obtain ⟨o1, o2⟩ := others_no_kind h hA
  obtain ⟨-, -, -, -, -, -, -, -, e2, e3, -⟩ := atPure_ok hA
  refine kindPays_of_lot mine named apart hm shared hs second h₃ Ls f₁ f₂ f₃ .K2 [baseSimLot]
    (fun l hl => by obtain rfl := List.mem_singleton.1 hl; exact hmine) (fun M hM => ?_)
    (fun l hl u hu _ σ hσ => ?_) (fun u hu hk => ?_) (fun u hu hk => ?_)
  · rcases lots_alone matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G M hM
      with e | e
    · exact .inl ⟨baseSimLot, List.Mem.head _, e.symm⟩
    · exact .inr e
  · obtain rfl := List.mem_singleton.1 hl
    obtain ⟨σ', hs', g⟩ := hG FullSizeMatrix IndexCommitterCoins Unit Unit _ A hA matrixInput.weights id u hu f₁
    obtain rfl : σ' = σ := Option.some.inj (hs'.symm.trans hσ)
    exact ⟨hN u hu, fun _ _ _ _ => False, fun _ _ _ _ => False, g _⟩
  · have hm' : u.half ∈ A.H.shared := by
      rw [e2, ← hs]
      exact List.mem_map_of_mem hu
    exact absurd (beq_iff_eq.2 hk) (List.filter_eq_nil_iff.1 o1 _ hm')
  · have hm' : u.half ∈ A.H.second := by
      rw [e3, ← h₃]
      exact List.mem_map_of_mem hu
    exact absurd (beq_iff_eq.2 hk) (List.filter_eq_nil_iff.1 o2 _ hm')

end AtFullSide.K2

#print axioms AtFullSide.K2.lots_alone
#print axioms AtFullSide.K2.kindPays_k2_at_base
