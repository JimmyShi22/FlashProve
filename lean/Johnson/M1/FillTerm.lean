-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- our 52 in the filling of the term.
/-
Johnson/M1/FillTerm.lean: at the unread filling from which the term's filling is read through
(`onlineProverPartsInUse`), at a return of the maker: the prover's first chain holds our sender at K1's
own lot's 51 jobs and at W's job, at the filling's own letters. Read through `OnlineProverParts.through` by the law
that carries a row's sentences, so stated at the unread input. No property of the protocol is claimed
here.
-/
import Johnson.M1.FillTies
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.SendSim.Seat.LotW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open OnBytes.SendSim.Seat (lotJobs wJobs liftedHalf)

variable {W₀ : Type}

/-- **K1's own lot, in the term's unread filling.** -/
theorem k1_in_term {I : WiderIn W₀} {o : ProofFile.SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
    {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (h : onlineProverFromPublicFiles o pol lay KL (onlineProverPartsInUse I o S O) = .ok A)
    {J : SendJob (PlaceIn ProofFile.Inst) Unit}
    (hJ : J ∈ lotJobs (X := Unit) (lotNo o A.Z) (lotData S) A.Z A.G) :
    liftedHalf (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (witOf I A.Z) J ∈ A.H.first := by
  obtain ⟨-, -, -, -, -, -, -, hf, -⟩ := atPure_ok h
  rw [hf]
  obtain ⟨L, hL, hm⟩ := List.mem_flatMap.1 (k1_in_fill I o S O A.Z A.G hJ)
  refine List.mem_flatMap.2 ⟨L, ?_, hm⟩
  rw [widerFillAtCPUOWM_lots]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hL))

/-- **W's job, in the term's unread filling.** -/
theorem w_in_term {I : WiderIn W₀} {o : ProofFile.SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
    {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (h : onlineProverFromPublicFiles o pol lay KL (onlineProverPartsInUse I o S O) = .ok A)
    {J : SendJob (PlaceIn ProofFile.Inst) Unit}
    (hJ : J ∈ wJobs (X := Unit) (lotNo o A.Z) (K13.wDataAt O.pile) A.Z A.G) :
    liftedHalf (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (witOf I A.Z) J ∈ A.H.first := by
  obtain ⟨-, -, -, -, -, -, -, hf, -⟩ := atPure_ok h
  rw [hf]
  obtain ⟨M, hM, he⟩ := hex_wM I o S O A.Z A.G
  refine List.mem_flatMap.2 ⟨M, hM, ?_⟩
  rw [he, OnBytes.SendSim.Seat.wHalves_eq]
  exact List.mem_map.2 ⟨J, hJ, rfl⟩

end Johnson.M1

#print axioms Johnson.M1.k1_in_term
#print axioms Johnson.M1.w_in_term
