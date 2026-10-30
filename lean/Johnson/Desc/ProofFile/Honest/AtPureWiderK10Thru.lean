-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/AtPureWiderK10Thru.lean: the closings' list (kind K10) read through
(Honest/Thru.lean). Reading the closing's part through is the same part at the job that reads its
input through. So the list `closeLotAt` read through is a list of rows with simulators at the new letters,
at the readers composed with the reading through.

  `K10.closePart_read_through`   the part read through is the part at the job carried over
  `K10.closingRow_half_thru`   a row's half read through is the row's half at the readers composed
  `closingsSLotThru`   the list with simulators at the new letters
  `closingsSLotThru_toHLot`   without its simulators it is `closeLotAt` read through

This file proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureWiderK10Rows
import Johnson.Desc.ProofFile.Honest.Thru

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc.First.Close (Par)

section
variable {V V' W W' X : Type}

/-- **The part read through is the part at the job carried over.** -/
theorem closePart_read_through (see : V' → V) (wit : W' → W) (J : CloseJob W) (F : FoldWords) :
    Part.thru see wit (closePart (foldShellT true J F) : Part V W X) =
      closePart (foldShellT true (J.over wit) F) := by
  simp only [Part.thru, Part.lift, closePart, Part.andThen, foldShellT, closeBatPart, List.map_cons,
    List.map_map, List.map_append, List.map_nil]
  rfl

end

variable {W₀ W₀' Rc Rc' Xi Tr X : Type}

/-- **A row's half read through** is the row's half at the readers composed. -/
theorem closingRow_half_thru (g : W₀' → W₀) (rd : Rc' → Rc)
    (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi)
    (Z : ProofFile.Pub) (G : ProofFile.Ground) (Q : Par) :
    Placed.thru (Local.thru g rd) (Local.thru g rd)
        (closingRow (X := X) readers rows stAt Z G Q).half =
      (closingRow (X := X) (readers ∘ Local.thru g rd) rows stAt Z G Q).half := by
  show (⟨closePlace Q, [Part.thru (Local.thru g rd) (Local.thru g rd)
    (closePart (foldShellT true (closingJob readers rows stAt Z G Q) foldWords))]⟩ :
      Placed (Local W₀' Rc' Xi Tr) (Local W₀' Rc' Xi Tr) X) = _
  rw [closePart_read_through]
  rfl

end ProofFile.Honest.K10

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Chain FileDescription)

variable {W₀ W₀' Rc' X : Type}

/-- **`closeLotAt` read through, with simulators.** -/
def closingsSLotThru (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (g : W₀' → W₀)
    (rd : Rc' → IndexCommitterCoins) :
    SLot (Local W₀' Rc' Inst Cells) (Local W₀' Rc' Inst Cells) X Inst :=
  { name := (closeLotAt (X := X) I S).name
    rows := fun Z G =>
      match ProofFile.onlineFirstChainAt Z with
      | .ok cF =>
        (K10.closingsSLot
          ((fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩) ∘
            Local.thru g rd)
          (widerRows S Z G) (K10.stAtZero cF.blocksInOrder fun ξ : Inst => ProofFile.startS Z ξ.pub)).rows Z G
      | .error _ => [] }

/-- **Without its simulators it is `closeLotAt` read through.** -/
theorem closingsSLotThru_toHLot (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (g : W₀' → W₀)
    (rd : Rc' → IndexCommitterCoins) :
    (closingsSLotThru (X := X) I S g rd).toHLot =
      HLot.thru (Local.thru g rd) (Local.thru g rd) (closeLotAt (X := X) I S) := by
  refine HLot.ext' rfl ?_
  funext Z G
  cases e : ProofFile.onlineFirstChainAt Z with
  | ok cF =>
    have h1 : (closingsSLotThru (X := X) I S g rd).rows Z G =
        (K10.closingsSLot
          ((fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩) ∘
            Local.thru g rd)
          (widerRows S Z G) (K10.stAtZero cF.blocksInOrder fun ξ : Inst => ProofFile.startS Z ξ.pub)).rows Z G := by
      show (match ProofFile.onlineFirstChainAt Z with
        | .ok cF =>
          (K10.closingsSLot
            ((fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩) ∘
              Local.thru g rd)
            (widerRows S Z G) (K10.stAtZero cF.blocksInOrder fun ξ : Inst => ProofFile.startS Z ξ.pub)).rows Z G
        | .error _ => []) = _
      rw [e]
    have h3 := congrFun (congrFun (congrArg HLot.halves (K10.closingsSLot_toHLot (X := X)
      (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩)
      (widerRows S Z G) (K10.stAtZero cF.blocksInOrder fun ξ : Inst => ProofFile.startS Z ξ.pub))) Z) G
    show ((closingsSLotThru (X := X) I S g rd).rows Z G).map (·.half) =
      ((closeLotAt (X := X) I S).halves Z G).map (Placed.thru (Local.thru g rd) (Local.thru g rd))
    rw [h1, closeLotAt_ok I S G e, ← h3]
    show ((K10.closePars Z).map (K10.closingRow _ _ _ Z G)).map (·.half) =
      (((K10.closePars Z).map (K10.closingRow _ _ _ Z G)).map (·.half)).map _
    simp only [List.map_map]
    refine List.map_congr_left fun Q _ => ?_
    exact (K10.closingRow_half_thru g rd _ _ _ Z G Q).symm
  | error m =>
    have h1 : (closingsSLotThru (X := X) I S g rd).rows Z G = [] := by
      show (match ProofFile.onlineFirstChainAt Z with
        | .ok cF =>
          (K10.closingsSLot
            ((fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩) ∘
              Local.thru g rd)
            (widerRows S Z G) (K10.stAtZero cF.blocksInOrder fun ξ : Inst => ProofFile.startS Z ξ.pub)).rows Z G
        | .error _ => []) = _
      rw [e]
    show ((closingsSLotThru (X := X) I S g rd).rows Z G).map (·.half) =
      ((closeLotAt (X := X) I S).halves Z G).map (Placed.thru (Local.thru g rd) (Local.thru g rd))
    rw [h1, closeLotAt_error I S G e]
    rfl

/-- **Its halves at a chain that `onlineFirstChainAt` makes** are `seatLotC`'s at the readers composed. -/
theorem closeLotAt_thru_halves (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (g : W₀' → W₀)
    (rd : Rc' → IndexCommitterCoins) {Z : ProofFile.Pub} {cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl}
    (G : ProofFile.Ground) (e : ProofFile.onlineFirstChainAt Z = .ok cF) :
    (HLot.thru (Local.thru g rd) (Local.thru g rd) (closeLotAt (X := X) I S)).halves Z G =
      (K10.seatLotC (X := X)
        ((fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩) ∘
          Local.thru g rd)
        (widerRows S Z G) (K10.stAtZero cF.blocksInOrder fun ξ : Inst => ProofFile.startS Z ξ.pub)).halves Z G := by
  rw [← closingsSLotThru_toHLot]
  have h1 : (closingsSLotThru (X := X) I S g rd).rows Z G =
      (K10.closingsSLot
        ((fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩) ∘
          Local.thru g rd)
        (widerRows S Z G) (K10.stAtZero cF.blocksInOrder fun ξ : Inst => ProofFile.startS Z ξ.pub)).rows Z G := by
    show (match ProofFile.onlineFirstChainAt Z with
      | .ok cF =>
        (K10.closingsSLot
          ((fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, I.weights Z w.w₀, w.rc⟩) ∘
            Local.thru g rd)
          (widerRows S Z G) (K10.stAtZero cF.blocksInOrder fun ξ : Inst => ProofFile.startS Z ξ.pub)).rows Z G
      | .error _ => []) = _
    rw [e]
  show ((closingsSLotThru (X := X) I S g rd).rows Z G).map (·.half) = _
  rw [h1]
  exact congrFun (congrFun (congrArg HLot.halves (K10.closingsSLot_toHLot (X := X) _ _ _)) Z) G

end ProofFile.Honest

#print axioms ProofFile.Honest.closeLotAt_thru_halves
#print axioms ProofFile.Honest.K10.closePart_read_through
#print axioms ProofFile.Honest.K10.closingRow_half_thru
#print axioms ProofFile.Honest.closingsSLotThru
#print axioms ProofFile.Honest.closingsSLotThru_toHLot
