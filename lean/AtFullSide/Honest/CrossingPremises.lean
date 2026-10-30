-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/CrossingPremises.lean: THREE PREMISES OF THE STEP FROM THE BASE PROVER TO THE ONLINE PROVER, PAID AT THE LETTERS OF THE ONE OBJECT (AtFullSide/Honest/TheOneObject.lean).
The laws that carry the hypotheses of the rule on a run from a prover H to the rows' prover over H read through two maps (`rows_of_thruJ`, Johnson/Desc/ProofFile/Honest/ThruThreadsJ.lean;
`yesAt_of_base_threadsJ`, E2E/CompleteAsIOPBaseThreads.lean) take four premises beside these hypotheses. Here three of them, at H := A.H, the maps `id` and `tableCoins Z`, the named member
`matrixInput.dummy`, the sides `theSides h` and the committer `cmAlong (AZ Z) PadZ (holdZ Z)`.

  **`crossing_rows`**          hrows: the sides' prover over the prover read through is that prover. No premise: the sides are made of that prover's own rows
  **`crossing_range`**         hd: the range's test answers alike at the two named members. From the base maker's return
  **`crossing_columns_all`**   the committer's columns show the words that the prover read through stores, at EVERY matrix and EVERY table randomness. From the head's scope and the return
  **`crossing_columns`**       hcols: that at every tied request. The tie is not used: it is an instance of the line above

Limits. The fourth premise (the committer's key is the prover's) is not here. This file proves no property of a prover or a protocol.
-/
import AtFullSide.Honest.TheOneObject
import AtFullSide.Honest.CommittedColumnsAtMaker
import E2E.BaseMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput matrixFilling tableCoins named_in_range baseMaker committedColumns_atFilling)
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.Committed AtPublicFiles.TheFalls
open VerifierAndGoals (PublicFiles readFiles)

local instance (priority := high) nonemptyPadZ_crossingPremises : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

local instance (priority := high) nonemptyRunValue_crossingPremises : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_crossingPremises : Inhabited RunValue := ⟨fun _ => 0⟩

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **hrows**: the sides' prover over the prover read through is that prover. -/
theorem crossing_rows (h : HeadAtReturn Z A) :
    (theSides h).prover (A.H.thru id (tableCoins Z) matrixInput.dummy) =
      A.H.thru id (tableCoins Z) matrixInput.dummy :=
  sidesForCompleteness_prover (onlineReturn Z A) h.places h.firstChain
    (theSlots (onlineReturn Z A) h.places h.firstChain)

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **hd**: the range's test answers alike at the two named members. -/
theorem crossing_range (made : baseMaker Z = .ok A) :
    A.H.inRange (id matrixInput.dummy) = A.H.inRange A.H.dummy := by
  obtain ⟨e₁, e₂⟩ := inRange_of_atPure made
  rw [e₁, e₂]
  show matrixFilling.inRange matrixInput.dummy = matrixFilling.inRange matrixFilling.dummy
  rw [named_in_range, (K5.parts_of_atPure made).2.range]

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- The committer's columns show the stored words, at every matrix and every table randomness. -/
theorem crossing_columns_all (h : HeadAtReturn Z A) (made : baseMaker Z = .ok A) (M : FullSizeMatrix) (ρ : (protocolAtFiles Z).EncodingRandomness) :
    CommittedColumns (cmAlong (AZ Z) PadZ (holdZ Z)) 0 A.H id (tableCoins Z) M ρ :=
  committedColumns_atFilling Z h.head.scope OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest made M ρ

/-- **hcols**: that at every tied request. -/
theorem crossing_columns (h : HeadAtReturn Z A) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (made : baseMaker Z = .ok A) :
    ∀ n w x, TiedRequest h hr n w x →
      CommittedColumns (cmAlong (AZ Z) PadZ (holdZ Z)) 0 A.H id (tableCoins Z) w.1 w.2.1 :=
  fun _ w _ _ => crossing_columns_all h made w.1 w.2.1

end AtFullSide.Honest

#print axioms AtFullSide.Honest.crossing_rows
#print axioms AtFullSide.Honest.crossing_range
#print axioms AtFullSide.Honest.crossing_columns_all
#print axioms AtFullSide.Honest.crossing_columns
