-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- the filling lays K1's own lot as our lot.
/-
Johnson/M1/FillTies.lean: the prover's sides that the filling `widerFillAt` lays at K1's own lot are
the sender's, job by job, at the filling's own letters: the numbers `lotNo o Z`, the data `lotData S`
and the reader of the input. And at a return of the maker they are among the prover's first chain.
No property of the protocol is claimed here.
-/
import Johnson.Desc.ProofFile.Honest.AtPureWiderAt
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.SendSim.Seat.Lot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open OnBytes.SendSim.Seat (lotJobs lotHalves_eq liftedHalf sendLot placeHalf_eq)

variable {W₀ V X : Type}

/-- The reader of the input at which the filling lays K1's sides, at one public part. -/
def witOf (I : WiderIn W₀) (Z : ProofFile.Pub) :
    Local W₀ IndexCommitterCoins ProofFile.Inst Cells → PlaceIn ProofFile.Inst :=
  fun w => ⟨w.x, ⟨w.trace, I.weights Z w.w₀, w.rc⟩⟩

/-- **K1's first lot of the filling is our lot at the filling's own letters.** -/
theorem k1_halves (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    (HLot.byPub I.weights (LongLots.plain (W₀ := W₀) (X := X) o S O).k1).halves Z G =
      (lotJobs (X := X) (lotNo o Z) (lotData S) Z G).map (liftedHalf (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
        (witOf I Z)) :=
  lotHalves_eq (witOf I Z) (lotNo o Z) (lotData S) Z G

/-- **Each of our jobs is a side of the filling's first chain.** -/
theorem k1_in_fill (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Z : ProofFile.Pub) (G : ProofFile.Ground) {J : SendJob (PlaceIn ProofFile.Inst) Unit}
    (hJ : J ∈ lotJobs (X := Unit) (lotNo o Z) (lotData S) Z G) :
    liftedHalf (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (witOf I Z) J ∈
      firstOf Z G (widerFillAt I o S O).lots := by
  refine List.mem_flatMap.2 ⟨_, List.mem_cons_self .., ?_⟩
  have h := k1_halves (X := Unit) I o S O Z G
  show _ ∈ (HLot.byPub I.weights (LongLots.plain (W₀ := W₀) (X := Unit) o S O).k1).halves Z G
  rw [h]
  exact List.mem_map.2 ⟨J, hJ, rfl⟩

/-- **At a return of the maker**: the prover's first chain holds each of our jobs at that return's
public part and ground. -/
theorem k1_in_prover {I : WiderIn W₀} {o : ProofFile.SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
    {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (h : onlineProverFromPublicFiles o pol lay KL (widerFillAt I o S O) = .ok A)
    {J : SendJob (PlaceIn ProofFile.Inst) Unit}
    (hJ : J ∈ lotJobs (X := Unit) (lotNo o A.Z) (lotData S) A.Z A.G) :
    liftedHalf (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (witOf I A.Z) J ∈ A.H.first := by
  obtain ⟨-, -, -, -, -, -, -, hf, -⟩ := atPure_ok h
  rw [hf]
  exact k1_in_fill I o S O A.Z A.G hJ

end Johnson.M1

#print axioms Johnson.M1.k1_in_prover
