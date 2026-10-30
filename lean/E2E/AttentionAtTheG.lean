-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/AttentionAtTheG.lean: KindPays of the attention segments' own rounds (kind K5: the label of that
sub-protocol in the description) at G as E2E/TheG.lean lays it at a return of the base maker.

  kindPays_K5_at_rows   at any description equal to the return's, at the rows that KindRows lays, at
                        letters that keep or narrow the bound
  kindPays_K5_at_theG   CONDITIONAL: made; h; hk: at theGAtBase

What the law says and does not say is in the head of Honest/K5/Law/AttentionAtAFilling.lean: it is the
spender's half. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import E2E.AttentionAtTheBase
import E2E.KindPaysOfALot
import E2E.TheG
import Johnson.Desc.ProofFile.Honest.K5.Law.FindAtBase

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.TheSides
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.K5
open ProofFile.Honest.Term (baseMaker baseFilling theGAtBase)
open VerifiableInference.Desc (Chain FileDescription KindName)
open VerifiableInference.Compilation (KindPays)

variable {W₀ Rc X₀ X : Type}

/-- **KindPays at this kind at the rows that the kinds lay, at a description equal to the return's.**
CONDITIONAL: made; e; hl; hAlone; hk; hbud. -/
theorem kindPays_K5_at_rows {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} (made : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    {F : FileDescription ProofFile.Inst} (e : F = A.F) (hl : AttentionLawAt A) (K : KindRows P A.Z A.G)
    (Ls : Letters F A.B W₀ Rc OnBytes.TableKey Cells X₀ X)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (hAlone : ∀ M ∈ P.lots, M = k5LotK (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) id keyOfK3 ∨
      ∀ x ∈ M.halves A.Z A.G, x.place.kind ≠ KindName.K5)
    (hk : k5SLot (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) (Pb := ProofFile.Inst) id keyOfK3 ∈ K.lots)
    (hbud : ∀ u n ds asks, (Ls.first u).bud n ds asks → u.bud n ds asks) :
    KindPays (theSides F Ls K.slots.rows f₁ f₂ f₃) KindName.K5 := by
  subst e
  obtain ⟨-, -, -, -, -, -, -, -, eS, eT, -⟩ := atPure_ok made
  refine kindPays_of_kindRows K Ls f₁ f₂ f₃ KindName.K5 [k5SLot id keyOfK3] (fun l h => ?_)
    (fun M hM => ?_) (fun h hh hk' => ?_) (fun h hh hk' => ?_) (fun l h u hu _ σ hσ => ?_)
    (fun u _ hk' σ hσ => ?_) (fun u _ hk' σ hσ => ?_)
  · rw [List.mem_singleton.1 h]
    exact hk
  · rcases hAlone M hM with rfl | hno
    · exact Or.inl ⟨_, List.mem_singleton.2 rfl,
        congrArg HLot.name (k5SLot_toHLot (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X)
          (Pb := ProofFile.Inst) id keyOfK3)⟩
    · exact Or.inr hno
  · exact absurd hk' (hl.kindPlaces.2.2.2.1 h (by rw [eS]; assumption))
  · exact absurd hk' (hl.kindPlaces.2.2.2.2 h (by rw [eT]; assumption))
  · obtain rfl := List.mem_singleton.1 h
    obtain ⟨-, hall⟩ := hl.rows u hu
    obtain ⟨hG, -⟩ := hall f₁ σ hσ
    exact ⟨⟨fun v ca m front _ => hl.on u hu v ca m front, hbud u⟩,
      fun _ _ _ _ => False, fun _ _ _ _ => False, hG _ _ _ fun _ _ _ _ h => h⟩
  · obtain ⟨b, hb, e⟩ := block_of_seated hσ
    exact absurd (e ▸ hk') (hl.kindPlaces.2.1 b hb)
  · obtain ⟨b, hb, e⟩ := block_of_seated hσ
    exact absurd (e ▸ hk') (hl.kindPlaces.2.2.1 b hb)

/-- **KindPays at this kind at G at a return of the base maker.** CONDITIONAL: made; h; hk: this kind's
lot is among the lots that K lays. -/
theorem kindPays_K5_at_theG {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {Wt : Type}
    (made : baseMaker files = .ok A) (h : ProofFile.Honest.FirstThread.HeadAtReturn files A)
    (T : AtPublicFiles.TheG.ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hk : k5SLot (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) (Pb := ProofFile.Inst) id keyOfK3 ∈
      K.lots) :
    KindPays (theGAtBase h T K) KindName.K5 :=
  kindPays_K5_at_rows made (ProofFile.Honest.atPure_at_laid h.head.laid made).2.symm
    (AtPublicFiles.AtFiles.HonestTerm.Attention.attention_law_at_base made h.head) K _ _ _ _
    (lot_alone _ _ _ _ (k5_pair_only _ _ _ _) A.Z A.G) hk fun _ _ _ _ x => x

end AtPublicFiles.TheSides

#print axioms AtPublicFiles.TheSides.kindPays_K5_at_rows
#print axioms AtPublicFiles.TheSides.kindPays_K5_at_theG
