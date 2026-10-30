-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/AtPureWiderK10Rows.lean: the closings' list of the filling
`widerFillOwnC`, with simulators: `closeLotAt`'s twin for `SLot`. It stands under the same match on
the first chain as `closeLotAt`, with the same readers, data of rows and filler, and keeps that
list's silent default: no row where the chain is not made.

  `closingsSLotAt`   the lot
  `closingsSLotAt_ok`, `closingsSLotAt_error`   its rows where the chain is made, and where it is not
  `closingsSLotAt_toHLot`   the lot without its simulators is `closeLotAt`
  `closingsSLotAt_of_open`   its rows at an opened description's letters
-/
import Johnson.Desc.ProofFile.Honest.AtPureWiderK10
import Johnson.Desc.ProofFile.Honest.K10.RowsOfClosings

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Chain FileDescription)

variable {W₀ X : Type}

/-- **`closeLotAt`, with simulators.** -/
def closingsSLotAt (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) :
    SLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X Inst :=
  { name := (closeLotAt (X := X) I S).name
    rows := fun Z G =>
      match ProofFile.onlineFirstChainAt Z with
      | .ok cF =>
        (K10.closingsSLot (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩)
          (widerRows S Z G) (K10.stAtZero cF.blocksInOrder fun ξ : Inst => ProofFile.startS Z ξ.pub)).rows Z G
      | .error _ => [] }

/-- Where the first chain is made: the rows of `closingsSLot`, the filler's two letters by name. -/
theorem closingsSLotAt_ok (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) {Z : Pub} (G : Ground)
    {cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl} (h : ProofFile.onlineFirstChainAt Z = .ok cF) :
    (closingsSLotAt (X := X) I S).rows Z G =
      (K10.closingsSLot (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩)
        (widerRows S Z G)
        (K10.stAtZero cF.blocksInOrder fun ξ : Inst => ProofFile.startS Z ξ.pub)).rows Z G := by
  show (match ProofFile.onlineFirstChainAt Z with
    | .ok cF =>
      (K10.closingsSLot (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩)
        (widerRows S Z G) (K10.stAtZero cF.blocksInOrder fun ξ : Inst => ProofFile.startS Z ξ.pub)).rows Z G
    | .error _ => []) = _
  rw [h]

/-- Where it is not made: no row. -/
theorem closingsSLotAt_error (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) {Z : Pub} (G : Ground)
    {e : String} (h : ProofFile.onlineFirstChainAt Z = .error e) :
    (closingsSLotAt (X := X) I S).rows Z G = [] := by
  show (match ProofFile.onlineFirstChainAt Z with
    | .ok cF =>
      (K10.closingsSLot (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩)
        (widerRows S Z G) (K10.stAtZero cF.blocksInOrder fun ξ : Inst => ProofFile.startS Z ξ.pub)).rows Z G
    | .error _ => []) = _
  rw [h]

/-- **The lot without its simulators is the list that the filling lays.** -/
theorem closingsSLotAt_toHLot (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) :
    (closingsSLotAt (X := X) I S).toHLot = closeLotAt I S := by
  have h : (fun (Z : Pub) (G : Ground) =>
      ((closingsSLotAt (X := X) I S).rows Z G).map (·.half)) =
      (closeLotAt (X := X) I S).halves := by
    funext Z G
    cases e : ProofFile.onlineFirstChainAt Z with
    | ok cF =>
      rw [closingsSLotAt_ok I S G e, closeLotAt_ok I S G e]
      exact congrFun (congrFun (congrArg HLot.halves (K10.closingsSLot_toHLot (X := X)
        (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩)
        (widerRows S Z G) (K10.stAtZero cF.blocksInOrder fun ξ : Inst => ProofFile.startS Z ξ.pub))) Z) G
    | error m =>
      rw [closingsSLotAt_error I S G e, closeLotAt_error I S G e] <;> rfl
  exact congrArg (HLot.mk (closeLotAt (X := X) I S).name) h

/-- **Its rows at an opened description's letters.** -/
theorem closingsSLotAt_of_open (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (G : Ground)
    {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Z : Pub}
    {Bs : ProofFile.PureBase} {base : List (Block VerifiableInference.Desc.First.S ProofFile.Cl)}
    {c : Chain VerifiableInference.Desc.First.S ProofFile.Cl} {Sh : ProofFile.SharedSeat}
    {Se : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c Sh Se) :
    (closingsSLotAt (X := X) I S).rows Z G =
      (K10.closingsSLot (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩)
        (widerRows S Z G)
        (K10.stAtZero c.blocksInOrder fun ξ : Inst => ProofFile.startS Z ξ.pub)).rows Z G :=
  closingsSLotAt_ok I S G (ToldDesc.pureChainAt_of_open O)

end ProofFile.Honest

#print axioms ProofFile.Honest.closingsSLotAt
#print axioms ProofFile.Honest.closingsSLotAt_ok
#print axioms ProofFile.Honest.closingsSLotAt_error
#print axioms ProofFile.Honest.closingsSLotAt_toHLot
#print axioms ProofFile.Honest.closingsSLotAt_of_open
