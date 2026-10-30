-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/AttentionSlotAtTheFilling.lean: the lot of the rows with simulators of the attention segments' own
rounds (kind K5: the label of that sub-protocol in the description) FITS ITS SLOT in the filling, found
BY ITS NAME: every lot of the filling that bears its name is that lot with its simulators forgotten.
This is what E2E/TheSides.lean asks of a kind's lot (overlaySlots, its argument hm; KindRows, its field
lots_fit). The sister of K6/Term/SlotAtTheFilling.lean.

  attention_fits_the_base_slot, attention_fits_the_online_slot   a lot of the filling of that name is
                      the rows' lot
  attention_fit_at_name   the rows' halves are that lot's sides, at every public part and ground
  attention_named_base    the base filling has a lot of that name
  attentionKindRows   KindRows at the base filling with this lot alone on the first chain and no row on
                      the other two
  attention_in_kindRows   the lot stands in it: the premise hk of kindPays_K5_at_theG at those rows

What it is not. Equations of lots and inequalities of names. At rows that lay other kinds' lots too,
whoever writes the list shows hk by the list itself and hm at this slot by attention_fit_at_name.
Nothing on a run. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import E2E.TheSides
import E2E.AttentionLawAtTheTerm
import Johnson.Desc.ProofFile.Honest.K5.Law.FindAtBase

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.TheSides
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm.Attention
open ProofFile.Honest ProofFile.Honest.K5
open ProofFile.Honest.Term (baseFilling onlineFilling tableCoins matrixInput)
open VerifiableInference.Desc (KindName)

/-- The rows' lot at the base filling's letters. -/
abbrev attentionBaseLot : SLot (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit
    ProofFile.Inst :=
  k5SLot (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) (Pb := ProofFile.Inst) id keyOfK3

/-- **A lot of the base filling that bears the name is this lot, its simulators forgotten.** No
premise. -/
theorem attention_fits_the_base_slot (files : VerifierAndGoals.PublicFiles) :
    ∀ L ∈ (baseFilling files).lots, L.name = "K5: the attention segments' own rounds" →
      attentionBaseLot.toHLot = L := by
  intro L hL hn
  have hL' : L ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
      openHonest).lots := hL
  rw [widerFillAtCPUOWM_lots, widerFillAt_lots] at hL'
  simp only [widerPairs, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hL'
  rcases hL' with (((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl) | rfl) | rfl
  case inl.inl.inl.inr.inr.inr.inr.inr.inr.inr.inl => exact k5SLot_toHLot id keyOfK3
  all_goals exact absurd hn (by decide)

/-- **The same at the online filling.** No premise. -/
theorem attention_fits_the_online_slot (files : VerifierAndGoals.PublicFiles) :
    ∀ L ∈ (onlineFilling files).lots, L.name = "K5: the attention segments' own rounds" →
      (attentionRows files).toHLot = L := by
  intro L hL hn
  obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
  have e₀ := attention_fits_the_base_slot files L₀ h₀ hn
  have e₁ : (attentionRows files).toHLot =
      HLot.thru (Local.thru id (tableCoins files)) (Local.thru id (tableCoins files))
        (k5LotK (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) id openHonest.keyOf) :=
    attention_lot_own files
  rw [e₁, ← e₀]
  exact congrArg _ (k5SLot_toHLot id keyOfK3).symm

/-- **The rows' halves are the sides of the filling's lot of that name**, at every public part and
ground. -/
theorem attention_fit_at_name (files : VerifierAndGoals.PublicFiles) (Z : ProofFile.Pub) (Gr : ProofFile.Ground) :
    ∀ L ∈ (baseFilling files).lots, L.name = "K5: the attention segments' own rounds" →
      (attentionBaseLot.rows Z Gr).map (·.half) = L.halves Z Gr := by
  intro L hL hn
  rw [← attention_fits_the_base_slot files L hL hn]
  rfl

/-- **The base filling has a lot of that name.** -/
theorem attention_named_base (files : VerifierAndGoals.PublicFiles) :
    (baseFilling files).lots.any (fun L => L.name == attentionBaseLot.name) = true := by
  refine List.any_eq_true.2 ⟨k5LotK id openHonest.keyOf, ?_, ?_⟩
  · show _ ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).lots
    rw [fillPairs_lots]
    exact List.mem_map.2 ⟨_, k5_pair_mem _ _ _ _, rfl⟩
  · rfl

/-- **This lot alone on the first chain, no row on the other two.** -/
def attentionKindRows (files : VerifierAndGoals.PublicFiles) (Z : ProofFile.Pub) (Gr : ProofFile.Ground) :
    KindRows (baseFilling files) Z Gr where
  lots := [attentionBaseLot]
  named := fun s hs => by
    obtain rfl := List.mem_singleton.1 hs
    exact attention_named_base files
  apart := List.nodup_singleton _
  lots_fit := fun L hL s hs => by
    have hm := List.mem_of_find?_eq_some hs
    have hp := List.find?_some hs
    obtain rfl := List.mem_singleton.1 hm
    exact attention_fit_at_name files Z Gr L hL (beq_iff_eq.1 hp).symm
  shared := []
  shared_named := fun _ h => by cases h
  shared_apart := List.nodup_nil
  shared_fit := fun _ _ _ h => by cases h
  second := []
  second_named := fun _ h => by cases h
  second_apart := List.nodup_nil
  second_fit := fun _ _ _ h => by cases h

/-- The lot stands in these rows. -/
theorem attention_in_kindRows (files : VerifierAndGoals.PublicFiles) (Z : ProofFile.Pub) (Gr : ProofFile.Ground) :
    attentionBaseLot ∈ (attentionKindRows files Z Gr).lots :=
  List.mem_singleton.2 rfl

end AtPublicFiles.TheSides

#print axioms AtPublicFiles.TheSides.attention_fits_the_base_slot
#print axioms AtPublicFiles.TheSides.attention_fits_the_online_slot
#print axioms AtPublicFiles.TheSides.attention_fit_at_name
#print axioms AtPublicFiles.TheSides.attention_named_base
#print axioms AtPublicFiles.TheSides.attentionKindRows
#print axioms AtPublicFiles.TheSides.attention_in_kindRows
