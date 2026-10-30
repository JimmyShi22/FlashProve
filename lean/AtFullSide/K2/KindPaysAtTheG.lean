-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/KindPaysAtTheG.lean: KindPays for the kind "the code switch" (K2) at the letters' G: at
the sides theG builds from the kinds' rows at the base filling.

  kindPays_k2_rows     at any letters that narrow a row at most, at any description equal to the
                       return's, at rows K that hold this kind's lot
  kindPays_k2_at_theG  at theGAtBase
  kindPays_k2_theG     at TheLetters.theG: the socket's own name

By: kindPays_of_kindRows (E2E/KindPaysOfALot.lean), SidesMeetGood in simulatorAtTheBase,
others_no_kind, lots_alone. The step from the top at the return's description to h.description is
one equation (atPure_at_laid); the letters of the threads keep On and the bound whole.

Limits. KindRows is a hole of the letters: that baseSimLot stands in it is the premise hmine. All
limits of simulatorAtTheBase hold.
-/
import AtFullSide.K2.KindPaysAtBase
import AtFullSide.Honest.TheLetters

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K2
open ProofFile.Honest ProofFile.Honest.Term ProofFile.Honest.K2 ProofFile.Honest.FirstFill
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.AtFiles AtPublicFiles.Cut
open AtPublicFiles.TheSides
open AtPublicFiles.TheG (ThreadParts theLetters)
open VerifiableInference.Desc (KindName FileDescription)
open VerifiableInference.Compilation (KindPays)

variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **The kind pays at rows that hold its lot**, at any letters that narrow it at most. -/
theorem kindPays_k2_rows (scope : VerifierAndGoals.InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (made : baseMaker Z = .ok A) {F : FileDescription ProofFile.Inst} (eF : A.F = F)
    (Ls : Letters F A.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit)
    (K : KindRows (baseFilling Z) A.Z A.G)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (hmine : baseSimLot ∈ K.lots)
    (hN : ∀ u ∈ baseSimLot.rows A.Z A.G, Narrows (Ls.first u) u) :
    KindPays (theSides F Ls K.slots.rows f₁ f₂ f₃) .K2 := by
  subst eF
  obtain ⟨pp, read⟩ := H2K.Sizes.inScope_readFiles scope
  obtain ⟨Zp, Np, cF, x₀, h⟩ := P5J.head_exists_at_name Z scope read live (P5J.owed_of_live live)
  obtain ⟨-, -, hG, -⟩ := simulatorAtTheBase.2.2 Z scope live
  obtain ⟨o1, o2⟩ := others_no_kind h made
  obtain ⟨-, -, -, -, -, -, -, -, e2, e3, -⟩ := atPure_ok made
  have n2 : ∀ x ∈ (baseFilling Z).shared A.Z A.G, x.place.kind ≠ .K2 := fun x hx hk =>
    List.filter_eq_nil_iff.1 o1 x (by rw [e2]; exact hx) (beq_iff_eq.2 hk)
  have n3 : ∀ x ∈ (baseFilling Z).second A.Z A.G, x.place.kind ≠ .K2 := fun x hx hk =>
    List.filter_eq_nil_iff.1 o2 x (by rw [e3]; exact hx) (beq_iff_eq.2 hk)
  refine kindPays_of_kindRows K Ls f₁ f₂ f₃ .K2 [baseSimLot]
    (fun l hl => by obtain rfl := List.mem_singleton.1 hl; exact hmine) (fun M hM => ?_)
    (fun x hx hk => absurd hk (n2 x hx)) (fun x hx hk => absurd hk (n3 x hx))
    (fun l hl u hu _ σ hσ => ?_) (fun u hu hk => ?_) (fun u hu hk => ?_)
  · rcases lots_alone matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G M hM
      with e | e
    · exact .inl ⟨baseSimLot, List.Mem.head _, e.symm⟩
    · exact .inr e
  · obtain rfl := List.mem_singleton.1 hl
    obtain ⟨σ', hs', g⟩ := hG FullSizeMatrix IndexCommitterCoins Unit Unit _ A made matrixInput.weights id u hu f₁
    obtain rfl : σ' = σ := Option.some.inj (hs'.symm.trans hσ)
    exact ⟨hN u hu, fun _ _ _ _ => False, fun _ _ _ _ => False, g _⟩
  · obtain ⟨x, hx, e⟩ := List.any_eq_true.1 (K.shared_named u hu)
    exact absurd (by rw [beq_iff_eq.1 e]; exact hk) (n2 x hx)
  · obtain ⟨x, hx, e⟩ := List.any_eq_true.1 (K.second_named u hu)
    exact absurd (by rw [beq_iff_eq.1 e]; exact hk) (n3 x hx)

/-- **At G at the base filling.** -/
theorem kindPays_k2_at_theG {Wt : Type} (scope : VerifierAndGoals.InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (made : baseMaker Z = .ok A) (h : HeadAtReturn Z A) (T : ThreadParts A Wt)
    (K : KindRows (baseFilling Z) A.Z A.G) (hmine : baseSimLot ∈ K.lots) :
    KindPays (theGAtBase h T K) .K2 :=
  kindPays_k2_rows scope live made (atPure_at_laid h.head.laid made).2 (theLetters h T) K _ _ _
    hmine fun u _ => narrows_of_bare (by cases u; rfl)

end AtFullSide.K2

namespace AtFullSide.K2
open AtFullSide.Honest.TheLetters
open AtPublicFiles.AtFiles AtPublicFiles.Cut
open VerifiableInference.Compilation (KindPays)
open ProofFile.Honest ProofFile.Honest.Term
open ProofFile.Honest.FirstThread (HeadAtReturn)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

/-- **At the letters' own name.** -/
theorem kindPays_k2_theG {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (scope : VerifierAndGoals.InScope Z = true) (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (made : baseMaker Z = .ok A) (h : HeadAtReturn Z A) {O : OpenShared A} (P : OpenLast h O)
    (K : OpenG A Z) (hmine : baseSimLot ∈ K.rows.lots) :
    KindPays (theG h P K) .K2 :=
  kindPays_k2_at_theG scope live made h (parts h P) K.rows hmine

end AtFullSide.K2

#print axioms AtFullSide.K2.kindPays_k2_rows
#print axioms AtFullSide.K2.kindPays_k2_at_theG
#print axioms AtFullSide.K2.kindPays_k2_theG
