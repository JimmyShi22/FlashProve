-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K1's two hypotheses of `overlaySlots`, at the unread filling.
/-
Johnson/M1/K1Socket.lean: at the readers `id`, `id`, the halves of K1's own lot and of W's are the
filling's own lots' halves: the hypothesis that `overlaySlots` (E2E/TheSides.lean) asks of each. No
property of the protocol is claimed here.
-/
import Johnson.M1.K1Lot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open OnBytes.SendSim.Seat (lotJobs wJobs liftedHalf jobOver sendRow)

variable {W₀ Pb : Type}

/-- **K1's own lot at the unread filling.** -/
theorem k1_socket (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ((k1Lot (Pb := Pb) (W₀' := W₀) (Rc' := IndexCommitterCoins) I o S id id).rows Z G).map (·.half) =
      (HLot.byPub I.weights (LongLots.plain (W₀ := W₀) (X := Unit) o S O).k1).halves Z G := by
  rw [k1_halves]
  show ((lotJobs (X := Unit) (lotNo o Z) (lotData S) Z G).map fun J =>
    sendRow (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Pb := Pb) J.P.place
      (jobOver J (witThru I Z id id))).map (·.half) = _
  rw [List.map_map]
  rfl

/-- **W's lot at the unread filling.** -/
theorem w_socket (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (O : OnlineProverArguments) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ((wLot (Pb := Pb) (W₀' := W₀) (Rc' := IndexCommitterCoins) I o O id id).rows Z G).map (·.half) =
      (wLotAt (X := Unit) I o O).halves Z G := by
  have e : (wLotAt (X := Unit) I o O).halves Z G =
      (wJobs (X := Unit) (lotNo o Z) (K13.wDataAt O.pile) Z G).map
        (liftedHalf (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (witOf I Z)) :=
    OnBytes.SendSim.Seat.wHalves_eq (witOf I Z) (lotNo o Z) (K13.wDataAt O.pile) Z G
  rw [e]
  show ((wJobs (X := Unit) (lotNo o Z) (K13.wDataAt O.pile) Z G).map fun J =>
    sendRow (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Pb := Pb) J.P.place
      (jobOver J (witThru I Z id id))).map (·.half) = _
  rw [List.map_map]
  rfl

end Johnson.M1

#print axioms Johnson.M1.k1_socket
#print axioms Johnson.M1.w_socket
