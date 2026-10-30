-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Slot/AtFill.lean: the closing of a segment (K10): THE LOT THAT THE ROWS' HALVES ARE IS
IN THE FILLING OF THE ONLINE PROVER. `closingsSLotAt` (Honest/AtPureWiderK10Rows.lean), without its simulators, is
`closeLotAt`; `closeLotAt` is a member of `widerFillOwnCPUOWM`'s lots; read through, it is a member of the lots of that
filling read through by `OnlineProverParts.through`, which is how the term's filling is made.

  `closing_socket`         the rows' halves are the lot's, in the form of `overlaySlots`' `RowSlots`
  `closeLot_in_filling`    `closeLotAt` among the lots of `widerFillOwnCPUOWM`
  `closeLot_in_at`         the same at `onlineProverPartsInUse`
  `closeLot_through`       read through, among the lots of `OnlineProverParts.through` of that filling
  **`rows_in_through`**    the same of the rows' own lot: what `closingsSLotAt` lays, without its simulators and read
      through, is a lot of the filling read through

Limits. A statement on lists of lots: it does not say that no other lot lays a half at these places (`closeLotAt_kinds`
and `closeLotAt_clean` speak to that), nor that the maker returns at this filling.
No property of the protocol is
claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.ThruK13
import Johnson.Desc.ProofFile.Honest.AtPureWiderK10Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.Slot

variable {W₀ W₀' Rc' X : Type}

/-- **The socket's form**: the rows' halves are the lot's. -/
theorem closing_socket (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ((closingsSLotAt (X := X) I S).rows Z G).map (·.half) = (closeLotAt (X := X) I S).halves Z G :=
  congrFun (congrFun (congrArg HLot.halves (closingsSLotAt_toHLot (X := X) I S)) Z) G

/-- **`closeLotAt` is a lot of the filling.** -/
theorem closeLot_in_filling (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    closeLotAt I S ∈ (widerFillOwnCPUOWM own₀ L I o S O).lots := by
  show closeLotAt I S ∈ (((widerFillOwn own₀ L I o S O).lots ++ [closeLotAt I S]) ++ [proxLotAt I S]) ++
    [wLotAt I o O]
  simp

/-- At `onlineProverPartsInUse`. -/
theorem closeLot_in_at (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    closeLotAt I S ∈ (onlineProverPartsInUse I o S O).lots :=
  closeLot_in_filling () (LongLots.plain o S O) I o S O

/-- **Read through.** -/
theorem closeLot_through (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d' : W₀') (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (closeLotAt I S).thru (Local.thru g rd) (Local.thru g rd) ∈
      (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)).lots :=
  List.mem_map_of_mem (closeLot_in_at I o S O)

/-- **The rows' own lot, read through, is a lot of the filling read through.** -/
theorem rows_in_through (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d' : W₀') (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ((closingsSLotAt (X := Unit) I S).toHLot).thru (Local.thru g rd) (Local.thru g rd) ∈
      (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)).lots := by
  rw [closingsSLotAt_toHLot]
  exact closeLot_through g rd d' I o S O

end ProofFile.Honest.K10.Slot

#print axioms ProofFile.Honest.K10.Slot.closing_socket
#print axioms ProofFile.Honest.K10.Slot.closeLot_in_filling
#print axioms ProofFile.Honest.K10.Slot.closeLot_in_at
#print axioms ProofFile.Honest.K10.Slot.closeLot_through
#print axioms ProofFile.Honest.K10.Slot.rows_in_through
