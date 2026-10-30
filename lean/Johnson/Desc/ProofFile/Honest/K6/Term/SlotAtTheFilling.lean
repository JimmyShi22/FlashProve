--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/SlotAtTheFilling.lean: the lot of the rows with simulators of the
sub-protocol "the output head's own rounds" (kind K6) FITS ITS SLOT in the online honest prover's
filling, found BY ITS NAME: every lot of the filling that bears its name is that lot with its
simulators forgotten. This is the premise under which a function of other authors lays a kind's lot over
the filling's own (`overlaySlots`, E2E/TheSides.lean, its argument hm; that file is not imported here).

What it is not. An equation of lots, and twelve inequalities of names. Nothing on a law, a run, or any
property of the protocol.

  `headSimulatorLot_name`   the lot's name, written out
  `headSimulatorLot_fits_the_base_slot`, `…_the_online_slot`   a lot of the filling of that name is it
  `headSimulatorLot_overlays_the_base`, `…_the_online_filling`   the premise hm, to its letter, at the
        list that holds this lot alone. At a longer list the search takes the FIRST lot of the name: whoever
        joins several kinds' lots calls the two lemmas above instead
-/
import Johnson.Desc.ProofFile.Honest.K6.Term.SimulatorAtTheHonestProver

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open ProofFile.Honest.Term (matrixInput tableCoins onlineFilling)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge

/-- The lot's name. -/
theorem headSimulatorLot_name {W₀ Rc X : Type} (weights : Pub → W₀ → Weights) :
    (headSimulatorLot (Rc := Rc) (X := X) weights).name = "the output head's own rounds (K6)" := rfl

/-- **A lot of the base filling that bears the name is this lot, its simulators forgotten.** No
premise. -/
theorem headSimulatorLot_fits_the_base_slot :
    ∀ L ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
      openHonest).lots, L.name = "the output head's own rounds (K6)" →
      (headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights).toHLot = L := by
  intro L hL hn
  rw [widerFillAtCPUOWM_lots, widerFillAt_lots] at hL
  simp only [widerPairs, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hL
  rcases hL with (((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl) | rfl) | rfl
  case inl.inl.inl.inr.inr.inr.inr.inr.inr.inr.inr.inl => exact headSimulatorLot_toHLot _
  all_goals exact absurd hn (by decide)

/-- The same at the online filling. No premise. -/
theorem headSimulatorLot_fits_the_online_slot (files : VerifierAndGoals.PublicFiles) :
    ∀ L ∈ (onlineFilling files).lots, L.name = "the output head's own rounds (K6)" →
      (headSimulatorLot (Rc := (protocolAtFiles files).EncodingRandomness) (X := Unit) matrixInput.weights).toHLot = L := by
  intro L hL hn
  obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
  have e₀ := headSimulatorLot_fits_the_base_slot L₀ h₀ hn
  rw [← e₀, headSimulatorLot_toHLot (Rc := IndexCommitterCoins)]
  exact headSimulatorLot_through (X := Unit) (id : FullSizeMatrix → FullSizeMatrix) (tableCoins files) matrixInput.weights

/-- **The premise under which the lot is laid over the base filling's own**, at the list that holds
this lot alone. -/
theorem headSimulatorLot_overlays_the_base :
    ∀ L ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
      openHonest).lots, ∀ s,
      ([headSimulatorLot (Rc := IndexCommitterCoins) (X := Unit) matrixInput.weights].find?
        fun s => s.name == L.name) = some s → s.toHLot = L := by
  intro L hL s hs
  have hm := List.mem_of_find?_eq_some hs
  have hp := List.find?_some hs
  obtain rfl := List.mem_singleton.1 hm
  exact headSimulatorLot_fits_the_base_slot L hL (beq_iff_eq.1 hp).symm

/-- The same at the online filling. -/
theorem headSimulatorLot_overlays_the_online_filling (files : VerifierAndGoals.PublicFiles) :
    ∀ L ∈ (onlineFilling files).lots, ∀ s,
      ([headSimulatorLot (Rc := (protocolAtFiles files).EncodingRandomness) (X := Unit) matrixInput.weights].find?
        fun s => s.name == L.name) = some s → s.toHLot = L := by
  intro L hL s hs
  have hm := List.mem_of_find?_eq_some hs
  have hp := List.find?_some hs
  obtain rfl := List.mem_singleton.1 hm
  exact headSimulatorLot_fits_the_online_slot files L hL (beq_iff_eq.1 hp).symm

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.headSimulatorLot_name
#print axioms ProofFile.Honest.K6.headSimulatorLot_fits_the_base_slot
#print axioms ProofFile.Honest.K6.headSimulatorLot_fits_the_online_slot
#print axioms ProofFile.Honest.K6.headSimulatorLot_overlays_the_base
#print axioms ProofFile.Honest.K6.headSimulatorLot_overlays_the_online_filling
