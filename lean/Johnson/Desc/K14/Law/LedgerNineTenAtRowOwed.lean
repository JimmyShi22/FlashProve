-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerNineTenAtRowOwed.lean: THE JOIN OF THE PROXIMITY TEST's OWN FACTS AT THE
SUB-PROTOCOLS 9 AND 10 TO THE SHARED CHAIN's ROW AS THE LEDGER's TOP CUTS IT, AT THE SEAT: TWO
PROPOSITIONS BY def: NO PROOF HERE. The ledger's tops (ledger_field_laid, row8_top, k14_law_top)
still bear NF : NineFacts … x9 dBA dtA and TF : TenFacts … x10 dBB dtB as premises, under «for all
the made letters with hlf».

(Where this and lean/THEOREM.md differ, the page holds.)
K12's files have both structures as theorems in scope at the value that
is laid (nine_facts_laid, ten_facts_laid: Johnson/Loose/H2K12/NineTenAtLaid.lean), of a piece that
an «there is» gives at a place of piecesAt's own second row. What is owed is that this piece is the
one that stands at number 9, at number 10, of the row that the top reads.
(Both are proved in Johnson/Desc/K14/Law/LedgerNineTenAtRow.lean: nine_at_row, ten_at_row.)

  NineAtRowOwed   at the seat (seatFF, SeatTies: Johnson/Desc/K14/Law/LedgerSeatOwed.lean), at every
                  cut of the three chains' lists and every filling of piecesAt's letters as the top
                  has them: there are t₂, dB, dt with NineFacts at whatever piece stands at number 9
  TenAtRowOwed    the like at number 10, with the place's numbers nO that N.O holds
In the row f has number 0, "LIN point"'s piece 1, and so on: x9 and x10 have 9 and 10.
How it is spent: πA := pGu N · rA := rUFull · t₂A, dBA, dtA out of the «there is»; then NF at any
    made letters by hlf (the row's list at number 9 is x9). The like for TF.
Can it be met? Only where SeatTies has a member: that proofDataAndDecisionOfPublicFiles returns at files in scope is shown by
    no theorem.
What is not claimed. Nothing on soundness.
-/
import Johnson.Desc.K14.Law.LedgerSeatOwed
import Johnson.Desc.K12.Coin.NineTenFacts
import Johnson.Desc.K12.Law.SitsChains
import Johnson.Desc.K12.Law.PlacesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Maker OnBytes.Flat _root_.Run _root_.Run.PQ _root_.Iop
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open H2K.JointK (pGu pGomega)
open H2K.Member (rUFull rOFull)

/-- OWED: the proximity test's own facts at whatever piece stands at number 9 of the row. -/
def NineAtRowOwed : Prop :=
  ∀ (Cells Tok : Type) (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF)
    (Z : ProofFile.Pub) (N : H2U.Places4) (B' : ProofFile.SecondSeat) (c : Chain First.S ProofFile.Cl),
    SeatTies o S D r Z N B' c →
    ∀ (c₁ : Block (seatFF o Z N B' c).S₁ (seatFF o Z N B' c).Cl) (k₁ : List (Block (seatFF o Z N B'
        c).S₁ (seatFF o Z N B' c).Cl))
      (c₂ : Block (seatFF o Z N B' c).S₂ (seatFF o Z N B' c).Cl) (k₂ : List (Block (seatFF o Z N B'
          c).S₂ (seatFF o Z N B' c).Cl))
      (c₃ : Block (seatFF o Z N B' c).S₃ (seatFF o Z N B' c).Cl) (k₃ : List (Block (seatFF o Z N B'
          c).S₃ (seatFF o Z N B' c).Cl))
      (e₁ : (i : ℕ) → (ds : List RDT) →
        ((seatFF o Z N B' c).XiPub × (seatFF o Z N B' c).S₁) × (frameAt D (allOf D) D.key₁ 0).E.Str
            →
        Iop.Tr (uLT (ckP .two) ds) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
      (e₂ : (i : ℕ) → (ds : List RDT) →
        (((seatFF o Z N B' c).XiPub × (seatFF o Z N B' c).S₁) × (seatFF o Z N B' c).S₂) × (frameAt D
            (allOf D) D.key₂ 0).E.Str →
        Iop.Tr (uLT (ckP .two) ds) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
      (e₃ : (i : ℕ) → (ds : List RDT) →
        (((seatFF o Z N B' c).XiPub × (seatFF o Z N B' c).S₁ × (seatFF o Z N B' c).S₂) × (seatFF o Z
            N B' c).S₃) ×
          (frameAt D (allOf D) D.key₃ (seatFF o Z N B' c).lastChainFirstTreeNumber).E.Str →
        Iop.Tr (uLT (ckP .two) ds) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
      (dW wEnd : Wit Cells Tok MsgT),
      (seatFF o Z N B' c).first.blocksInOrder = c₁ :: k₁ → (seatFF o Z N B' c).shared.blocksInOrder = c₂ :: k₂ →
      (seatFF o Z N B' c).second.blocksInOrder = c₃ :: k₃ →
      ∃ (t₂ : ℕ) (dB : RDT) (dt : List RDT),
        ∀ x : Piece (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((ProofFile.InstPub × First.S) × St) ProofFile.Cl
            (Wit Cells Tok MsgT),
          ((atDesc (seatFF o Z N B' c) (piecesAt (ckP .two) (seatFF o Z N B' c) D c₁ k₁ c₂ k₂ c₃ k₃
              (restCap e₁) (restCap e₂)
              (restCap e₃) dW wEnd)).p₂ ::
            (atDesc (seatFF o Z N B' c) (piecesAt (ckP .two) (seatFF o Z N B' c) D c₁ k₁ c₂ k₂ c₃ k₃
                (restCap e₁) (restCap e₂)
              (restCap e₃) dW wEnd)).l₂)[9]? = some x →
          H2K.JointK.NineFacts (frameAt D (allOf D) D.key₂ 0) (pGu N) rUFull
            (VerifiableInference.Desc.oraclesOf (seatFF o Z N B' c).first.blocksInOrder).length t₂
            (Seat.onGu (proximityTestKind guardedProximityTestParts (pGu N) : Block T12 Unit)) x dB dt

/-- OWED: the like at number 10. -/
def TenAtRowOwed : Prop :=
  ∀ (Cells Tok : Type) (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF)
    (Z : ProofFile.Pub) (N : H2U.Places4) (B' : ProofFile.SecondSeat) (c : Chain First.S ProofFile.Cl),
    SeatTies o S D r Z N B' c →
    ∀ (c₁ : Block (seatFF o Z N B' c).S₁ (seatFF o Z N B' c).Cl) (k₁ : List (Block (seatFF o Z N B'
        c).S₁ (seatFF o Z N B' c).Cl))
      (c₂ : Block (seatFF o Z N B' c).S₂ (seatFF o Z N B' c).Cl) (k₂ : List (Block (seatFF o Z N B'
          c).S₂ (seatFF o Z N B' c).Cl))
      (c₃ : Block (seatFF o Z N B' c).S₃ (seatFF o Z N B' c).Cl) (k₃ : List (Block (seatFF o Z N B'
          c).S₃ (seatFF o Z N B' c).Cl))
      (e₁ : (i : ℕ) → (ds : List RDT) →
        ((seatFF o Z N B' c).XiPub × (seatFF o Z N B' c).S₁) × (frameAt D (allOf D) D.key₁ 0).E.Str
            →
        Iop.Tr (uLT (ckP .two) ds) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
      (e₂ : (i : ℕ) → (ds : List RDT) →
        (((seatFF o Z N B' c).XiPub × (seatFF o Z N B' c).S₁) × (seatFF o Z N B' c).S₂) × (frameAt D
            (allOf D) D.key₂ 0).E.Str →
        Iop.Tr (uLT (ckP .two) ds) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
      (e₃ : (i : ℕ) → (ds : List RDT) →
        (((seatFF o Z N B' c).XiPub × (seatFF o Z N B' c).S₁ × (seatFF o Z N B' c).S₂) × (seatFF o Z
            N B' c).S₃) ×
          (frameAt D (allOf D) D.key₃ (seatFF o Z N B' c).lastChainFirstTreeNumber).E.Str →
        Iop.Tr (uLT (ckP .two) ds) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
      (dW wEnd : Wit Cells Tok MsgT),
      (seatFF o Z N B' c).first.blocksInOrder = c₁ :: k₁ → (seatFF o Z N B' c).shared.blocksInOrder = c₂ :: k₂ →
      (seatFF o Z N B' c).second.blocksInOrder = c₃ :: k₃ →
      ∃ nO : H2U.PlaceNums, N.O = some nO ∧ ∃ (t₂ : ℕ) (dB : RDT) (dt : List RDT),
        ∀ x : Piece (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((ProofFile.InstPub × First.S) × St) ProofFile.Cl
            (Wit Cells Tok MsgT),
          ((atDesc (seatFF o Z N B' c) (piecesAt (ckP .two) (seatFF o Z N B' c) D c₁ k₁ c₂ k₂ c₃ k₃
              (restCap e₁) (restCap e₂)
              (restCap e₃) dW wEnd)).p₂ ::
            (atDesc (seatFF o Z N B' c) (piecesAt (ckP .two) (seatFF o Z N B' c) D c₁ k₁ c₂ k₂ c₃ k₃
                (restCap e₁) (restCap e₂)
              (restCap e₃) dW wEnd)).l₂)[10]? = some x →
          H2K.JointK.TenFacts (frameAt D (allOf D) D.key₂ 0) (pGomega nO) rOFull
            (VerifiableInference.Desc.oraclesOf (seatFF o Z N B' c).first.blocksInOrder).length t₂
            (Seat.onGomega (proximityTestKind guardedProximityTestParts (pGomega nO) : Block T12 Unit)) x dB dt

end Desc.K14.Law
