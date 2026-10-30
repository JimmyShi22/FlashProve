-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/AttentionAtTheOneG.lean: at files that pass, G at the description that a return of the base maker
holds: KindPays of the attention segments' own rounds (kind K5: the label of that sub-protocol in the
description), and the five statements on its lists.

  kindPays_K5_at_return        CONDITIONAL: made; h; hk: at theGOfReturn
  attention_lists_at_return    CONDITIONAL: made; h; hk: at theGOfReturn
  kindPays_K5_at_the_one_G     CONDITIONAL: scope; live: the return and the head exist, kinds' rows that
                               hold this kind's lot exist, and at all such rows and thread parts both
                               hold

That some files pass is not said here: SomeFilesPass names that. It is the spender's half.
No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import E2E.AttentionRunDebtsAtTheG
import E2E.AttentionSlotAtTheFilling
import AtFullSide.K1.HeadAtBaseMaker

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.TheSides
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.K5
open ProofFile.Honest.Term (baseMaker baseFilling)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.TheG (ThreadParts theGOfReturn)
open VerifiableInference.Desc (FileDescription KindName)
open VerifiableInference.Compilation (KindPays)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {Wt : Type}

/-- **KindPays at this kind at G at the return's own description.** CONDITIONAL: made; h; hk. -/
theorem kindPays_K5_at_return (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hk : k5SLot (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) (Pb := ProofFile.Inst) id keyOfK3 ∈
      K.lots) :
    KindPays (theGOfReturn made h T K) KindName.K5 :=
  castSides_of (Q := fun _ G => KindPays G KindName.K5) _ (kindPays_K5_at_theG made h T K hk)

/-- **The five statements at G at the return's own description.** CONDITIONAL: made; h; hk. -/
theorem attention_lists_at_return (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hk : k5SLot (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) (Pb := ProofFile.Inst) id keyOfK3 ∈
      K.lots) :
    AttentionListsAt (theGOfReturn made h T K) (rowsOfReturn A) :=
  castSides_of (Q := fun _ G => AttentionListsAt G (rowsOfReturn A)) _
    (attention_lists_at_theG made h T K hk)

/-- **At files that pass.** CONDITIONAL: scope; live: two tests on the public files. -/
theorem kindPays_K5_at_the_one_G (files : VerifierAndGoals.PublicFiles) (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) :
    ∃ (A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) (made : baseMaker files = .ok A)
      (h : HeadAtReturn files A),
      (∃ K : KindRows (baseFilling files) A.Z A.G,
        k5SLot (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) (Pb := ProofFile.Inst) id keyOfK3 ∈
          K.lots) ∧
      ∀ (Wt : Type) (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G),
        k5SLot (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) (Pb := ProofFile.Inst) id keyOfK3 ∈
          K.lots →
        KindPays (theGOfReturn made h T K) KindName.K5 ∧
          AttentionListsAt (theGOfReturn made h T K) (rowsOfReturn A) := by
  obtain ⟨A, made⟩ := ProofFile.Honest.K1.baseMaker_returns files scope live
  obtain ⟨h, -⟩ := ProofFile.Honest.K1.headAtReturn_baseMaker files scope live made
  exact ⟨A, made, h, ⟨attentionKindRows files A.Z A.G, attention_in_kindRows files A.Z A.G⟩,
    fun _ T K hk =>
      ⟨kindPays_K5_at_return made h T K hk, attention_lists_at_return made h T K hk⟩⟩

end AtPublicFiles.TheSides

#print axioms AtPublicFiles.TheSides.kindPays_K5_at_return
#print axioms AtPublicFiles.TheSides.attention_lists_at_return
#print axioms AtPublicFiles.TheSides.kindPays_K5_at_the_one_G
