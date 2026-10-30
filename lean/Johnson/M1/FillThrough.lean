-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- our 52 in the filling that the term reads.
/-
Johnson/M1/FillThrough.lean: the term's filling is the unread filling read through `OnlineProverParts.through`. A
lifted sender read through is the sender at the reader composed, by `Part.lift_thru` and
`lift_sendPart`. So at a return of the maker at the filling read through, the prover's first chain
holds our sender itself at each of K1's 51 jobs and at W's job, at the reader composed: no law on a
row read through is called. No property of the protocol is claimed here.
-/
import Johnson.M1.FillTerm
import Johnson.Desc.ProofFile.Honest.ThruK13
import Johnson.SendSim.Seat.Lifted

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open OnBytes.SendSim.Seat (lotJobs wJobs liftedHalf jobOver)

variable {W₀ W₀' Rc' : Type}

/-- The reader of the input of the filling read through. -/
def witThru (I : WiderIn W₀) (Z : ProofFile.Pub) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) :
    Local W₀' Rc' ProofFile.Inst Cells → PlaceIn ProofFile.Inst :=
  witOf I Z ∘ Local.thru g rd

/-- **A lifted sender read through is the sender at the reader composed.** -/
theorem lifted_thru (I : WiderIn W₀) (Z : ProofFile.Pub) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins)
    (J : SendJob (PlaceIn ProofFile.Inst) Unit) :
    Placed.thru (Local.thru g rd) (Local.thru g rd)
        (liftedHalf (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (witOf I Z) J) =
      ⟨J.P.place, [sendPart (V := Local W₀' Rc' ProofFile.Inst Cells) (jobOver J (witThru I Z g rd))]⟩ := by
  unfold liftedHalf Placed.thru
  simp only [List.map_cons, List.map_nil]
  rw [Part.lift_thru]
  rfl

/-- **K1's own lot and W's, at a return of the maker at the filling read through**: our sender
itself, at the reader composed, is a side of the prover's first chain. -/
theorem k1_in_through {I : WiderIn W₀} {o : ProofFile.SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz}
    {O : OnlineProverArguments} {g : W₀' → W₀} {rd : Rc' → IndexCommitterCoins} {d' : W₀'} {pol lay KL : ByteArray}
    {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (h : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)) = .ok A)
    {J : SendJob (PlaceIn ProofFile.Inst) Unit}
    (hJ : J ∈ lotJobs (X := Unit) (lotNo o A.Z) (lotData S) A.Z A.G) :
    (⟨J.P.place, [sendPart (V := Local W₀' Rc' ProofFile.Inst Cells)
      (jobOver J (witThru I A.Z g rd))]⟩ : Placed _ _ _) ∈ A.H.first := by
  obtain ⟨-, -, -, -, -, -, -, hf, -⟩ := atPure_ok h
  rw [hf, ← lifted_thru]
  obtain ⟨L, hL, hm⟩ := List.mem_flatMap.1 (k1_in_fill I o S O A.Z A.G hJ)
  refine List.mem_flatMap.2 ⟨HLot.thru (Local.thru g rd) (Local.thru g rd) L,
    List.mem_map.2 ⟨L, ?_, rfl⟩, List.mem_map.2 ⟨_, hm, rfl⟩⟩
  rw [widerFillAtCPUOWM_lots]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hL))

/-- W's job, likewise. -/
theorem w_in_through {I : WiderIn W₀} {o : ProofFile.SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz}
    {O : OnlineProverArguments} {g : W₀' → W₀} {rd : Rc' → IndexCommitterCoins} {d' : W₀'} {pol lay KL : ByteArray}
    {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (h : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)) = .ok A)
    {J : SendJob (PlaceIn ProofFile.Inst) Unit}
    (hJ : J ∈ wJobs (X := Unit) (lotNo o A.Z) (K13.wDataAt O.pile) A.Z A.G) :
    (⟨J.P.place, [sendPart (V := Local W₀' Rc' ProofFile.Inst Cells)
      (jobOver J (witThru I A.Z g rd))]⟩ : Placed _ _ _) ∈ A.H.first := by
  obtain ⟨-, -, -, -, -, -, -, hf, -⟩ := atPure_ok h
  rw [hf, ← lifted_thru]
  obtain ⟨M, hM, he⟩ := hex_wM I o S O A.Z A.G
  refine List.mem_flatMap.2 ⟨HLot.thru (Local.thru g rd) (Local.thru g rd) M,
    List.mem_map.2 ⟨M, hM, rfl⟩, List.mem_map.2 ⟨_, ?_, rfl⟩⟩
  rw [he, OnBytes.SendSim.Seat.wHalves_eq]
  exact List.mem_map.2 ⟨J, hJ, rfl⟩

end Johnson.M1

#print axioms Johnson.M1.k1_in_through
#print axioms Johnson.M1.w_in_through
