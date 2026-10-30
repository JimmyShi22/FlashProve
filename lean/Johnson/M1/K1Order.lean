-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K1's own lot stands first in the term's filling, W's last.
/-
Johnson/M1/K1Order.lean: the first chain's list of the term's filling begins with the halves of K1's own
lot and ends with the halves of W's: an equation of lists, in order, between which stand the other
lots read through. No property of the protocol is claimed here.
-/
import Johnson.M1.K1Lot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc

variable {W₀ W₀' Rc' Pb : Type}

/-- The lots between K1's own and W's, unread. -/
def midOf (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    List (HLot (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit) :=
  (widerFillAt I o S O).lots.tail ++ [closeLotAt I S] ++ [proxLotAt I S]

/-- The unread filling's lots: K1's first, W's last. -/
theorem lots_shape (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (onlineProverPartsInUse I o S O).lots =
      HLot.byPub I.weights (LongLots.plain (W₀ := W₀) (X := Unit) o S O).k1 ::
        (midOf I o S O ++ [wLotAt I o O]) := by
  rw [widerFillAtCPUOWM_lots]
  rfl

/-- **The term's first chain, in order.** -/
theorem first_shape (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d' : W₀') (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    firstOf Z G (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)).lots =
      ((k1Lot (Pb := Pb) I o S g rd).rows Z G).map (·.half) ++
        (firstOf Z G ((midOf I o S O).map (HLot.thru (Local.thru g rd) (Local.thru g rd))) ++
          ((wLot (Pb := Pb) I o O g rd).rows Z G).map (·.half)) := by
  show firstOf Z G ((onlineProverPartsInUse I o S O).lots.map
    (HLot.thru (Local.thru g rd) (Local.thru g rd))) = _
  rw [lots_shape]
  have e1 := congrArg (fun L : HLot _ _ _ => L.halves Z G) (k1Lot_toHLot (Pb := Pb) I o S O g rd)
  have e2 := congrArg (fun L : HLot _ _ _ => L.halves Z G) (wLot_toHLot (Pb := Pb) I o O g rd)
  simp only [firstOf, List.map_cons, List.map_append, List.flatMap_cons, List.flatMap_append,
    List.map_nil, List.flatMap_nil, List.append_nil] at e1 e2 ⊢
  rw [← show ((k1Lot (Pb := Pb) I o S g rd).toHLot).halves Z G = _ from e1,
    ← show ((wLot (Pb := Pb) I o O g rd).toHLot).halves Z G = _ from e2]
  rfl

end Johnson.M1

#print axioms Johnson.M1.first_shape
