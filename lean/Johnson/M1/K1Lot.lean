-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K1's two lots of the term's filling, with their simulators.
/-
Johnson/M1/K1Lot.lean: lots of rows (SLot) whose reader and jobs may hang on the public part, and the
two that the term's filling needs: K1's own lot and W's. Without the simulators they ARE the filling's
two lots read through: equations of lots. No property of the protocol is claimed here.
-/
import Johnson.M1.FillThrough
import Johnson.SendSim.Seat.LotOf
import Johnson.SendSim.Seat.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open OnBytes.SendSim.Seat (lotJobs wJobs liftedHalf jobOver sendRow)

variable {W₀ W₀' Rc' Pb : Type}

/-- A lot of our rows, at a reader and jobs that hang on the public part. -/
def sendLotZ {V W W' X : Type} (name : String) (wit : ProofFile.Pub → W → W')
    (jobs : ProofFile.Pub → ProofFile.Ground → List (SendJob W' X)) : SLot V W X Pb :=
  ⟨name, fun Z G => (jobs Z G).map fun J => sendRow J.P.place (jobOver J (wit Z))⟩

/-- **K1's own lot of the term's filling, with its simulators.** -/
def k1Lot (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (g : W₀' → W₀)
    (rd : Rc' → IndexCommitterCoins) :
    SLot (Local W₀' Rc' ProofFile.Inst Cells) (Local W₀' Rc' ProofFile.Inst Cells) Unit Pb :=
  sendLotZ "K1: the first segment's opening, each link's reads and digits"
    (fun Z => witThru I Z g rd) fun Z G => lotJobs (X := Unit) (lotNo o Z) (lotData S) Z G

/-- **W's lot of the term's filling, with its simulators.** -/
def wLot (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (O : OnlineProverArguments) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) :
    SLot (Local W₀' Rc' ProofFile.Inst Cells) (Local W₀' Rc' ProofFile.Inst Cells) Unit Pb :=
  sendLotZ "K1 and K13: W's commitment, the request's own group and the row (Eval)"
    (fun Z => witThru I Z g rd) fun Z G => wJobs (X := Unit) (lotNo o Z) (K13.wDataAt O.pile) Z G

/-- **K1's own lot, without its simulators, is the filling's first lot read through.** -/
theorem k1Lot_toHLot (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) :
    (k1Lot (Pb := Pb) I o S g rd).toHLot =
      HLot.thru (Local.thru g rd) (Local.thru g rd)
        (HLot.byPub I.weights (LongLots.plain (W₀ := W₀) (X := Unit) o S O).k1) := by
  refine HLot.ext' rfl ?_
  funext Z G
  show (((lotJobs (X := Unit) (lotNo o Z) (lotData S) Z G).map fun J =>
      sendRow (V := Local W₀' Rc' ProofFile.Inst Cells) (Pb := Pb) J.P.place
        (jobOver J (witThru I Z g rd))).map (·.half)) =
    ((HLot.byPub I.weights (LongLots.plain (W₀ := W₀) (X := Unit) o S O).k1).halves Z G).map
      (Placed.thru (Local.thru g rd) (Local.thru g rd))
  rw [k1_halves, List.map_map, List.map_map]
  refine List.map_congr_left fun J _ => ?_
  exact (lifted_thru I Z g rd J).symm

/-- **W's lot, without its simulators, is the filling's lot of W read through.** -/
theorem wLot_toHLot (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (O : OnlineProverArguments) (g : W₀' → W₀)
    (rd : Rc' → IndexCommitterCoins) :
    (wLot (Pb := Pb) I o O g rd).toHLot =
      HLot.thru (Local.thru g rd) (Local.thru g rd) (wLotAt (X := Unit) I o O) := by
  refine HLot.ext' rfl ?_
  funext Z G
  show (((wJobs (X := Unit) (lotNo o Z) (K13.wDataAt O.pile) Z G).map fun J =>
      sendRow (V := Local W₀' Rc' ProofFile.Inst Cells) (Pb := Pb) J.P.place
        (jobOver J (witThru I Z g rd))).map (·.half)) =
    ((wLotAt (X := Unit) I o O).halves Z G).map (Placed.thru (Local.thru g rd) (Local.thru g rd))
  have e : (wLotAt (X := Unit) I o O).halves Z G =
      (wJobs (X := Unit) (lotNo o Z) (K13.wDataAt O.pile) Z G).map
        (liftedHalf (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (witOf I Z)) :=
    OnBytes.SendSim.Seat.wHalves_eq (witOf I Z) (lotNo o Z) (K13.wDataAt O.pile) Z G
  rw [e, List.map_map, List.map_map]
  refine List.map_congr_left fun J _ => ?_
  exact (lifted_thru I Z g rd J).symm

end Johnson.M1

#print axioms Johnson.M1.k1Lot_toHLot
#print axioms Johnson.M1.wLot_toHLot
