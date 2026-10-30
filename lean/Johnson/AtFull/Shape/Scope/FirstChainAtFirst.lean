-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/FirstChainAtFirst.lean: THE FIRST CHAIN's TWO DEBTS AT THE BASE PROVER's FIRST THREAD:
THE TWO FIELDS yes₁ AND carry₁ OF FromThreadsJ, from the run on shapes, a letter of the term's Said, and the
twelve fields of values that stand open. halved is paid here by halved_first_base, the attention's reads and
the head's reads by their laws. The list of falls f₁ is free; the term's is firstFalls A parts.numbers.

  SortValuesRest          SortValuesLeft less readsAtt and readsHead
  first_chain_at_first    **yes₁ ∧ carry₁**

Limits. An implication: hyes and the twelve fields are premises. Nothing says that a field can be met.
Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.ValuesLeft
import Johnson.AtFull.Shape.K1ValuesAttHead
import Johnson.AtFull.Shape.K1ValuesHead
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.Thread.WalkedTo
import Johnson.Desc.ProofFile.Honest.K1.Pay.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Strs Place OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest (Shape Thread ProverCoinCounts Coins Mid Prover Local SaidOk ValuesJ NextJ AcceptedJ shapeJ halved
  OnlineProverWithDescription onlineProverFromPublicFiles onlineProverPartsInUse WiderIn OnlineProverArguments IndexCommitterCoins Cells SaidWalk Fall fallsBy)
open ProofFile.Honest.FirstThread
open VerifiableInference.Desc.K2.Honest (carryExact)
open ProofFile.Honest (ridersOf csHead kpBy ReadyInput)

/-- **THE TWELVE FIELDS LEFT**: SortValuesLeft less the attention's reads and the head's. It is a
definition: a premise's form. -/
structure SortValuesRest {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S ProofFile.Cl V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (J : Nat → S → Prop) (Zs : Shape S)
    (fall : Nat → S → List Fmt.Drawn → Option String) : Prop where
  layers : ∀ l, l < 24 → l % 2 = 0 → ValuesJ T Said J Zs fall (14 * l + 3 + 1)
  batch : ∀ l, l < 24 → ValuesJ T Said J Zs fall (14 * l + 8 + 1)
  behind : ∀ l, l < 24 → ValuesJ T Said J Zs fall (14 * l + 9 + 1)
  equation : ∀ l, l < 24 → ValuesJ T Said J Zs fall (14 * l + 10 + 1)
  reply : ValuesJ T Said J Zs fall (337 + 1)
  switchHead : ValuesJ T Said J Zs fall (337 + 2)
  head : ValuesJ T Said J Zs fall (337 + 4)
  lookHead : ValuesJ T Said J Zs fall (337 + 8)
  batchHead : ValuesJ T Said J Zs fall (337 + 10)
  behindHead : ValuesJ T Said J Zs fall (337 + 11)
  equationHead : ValuesJ T Said J Zs fall (337 + 12)
  test : ValuesJ T Said J Zs fall (353 + 1)

variable {files : VerifierAndGoals.PublicFiles} {W₀ : Type} (I : WiderIn W₀) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {Bs : ProofFile.PureBase}

/-- **yes₁ AND carry₁ OF FromThreadsJ AT THE FIRST THREAD OF THE BASE PROVER.** -/
theorem first_chain_at_first (hK : O.keyOf = ProofFile.Honest.K5.keyOfK3)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz O) = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (B : Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → List OpenedColumn → Prop)
    (m₀ : Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (f₁ : List (Fall TS))
    (hyes : (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)).yes startShA 358 = true)
    (Rest : SortValuesRest (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
      (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀))
      (fallsBy f₁ h.description.first.blocksInOrder)) :
    (∀ b, b < (firstThread h parts w).bs.length →
      AcceptedJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
        (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
        (fallsBy f₁ h.description.first.blocksInOrder) b) ∧
    (∀ b, b < (firstThread h parts w).bs.length →
      NextJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
        (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
        (fallsBy f₁ h.description.first.blocksInOrder) b) := by
  have h4 : halved h.firstChain.blocksInOrder A.H.first = true := by
    have e := ProofFile.Honest.K1.Pay.halved_first_base I Sz O hK h.head hA
    rw [(ProofFile.Honest.atPure_at_laid h.head.laid hA).2] at e
    exact e
  have ra := readsAtt_at_head h.head hB A.H parts.script
    (fallsAfterBatching (firstFalls A parts.numbers) h.firstChain)
    (carryExact A.Z (P5J.At.arr A.Z)) 0 h.description.t₁ h.description.t₂ 339
    (ReadyInput h.description A.H)
    (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
    (kpBy (firstClauses h)) w
    (SaidWalk (firstThread h parts w) B m₀) (fallsBy f₁ h.description.first.blocksInOrder) hyes h4
  have rh := k1_valuesJ_head h.head hB (firstThread h parts w)
    (SaidWalk (firstThread h parts w) B m₀) (fallsBy f₁ h.description.first.blocksInOrder) rfl rfl
    (fun _ _ _ _ h0 => ⟨_, h0⟩)
    (ProofFile.Honest.fitsAt_of_halved (firstThread h parts w) h4 342) hyes
  exact debts_at_head h.head hB A.H parts.script
    (fallsAfterBatching (firstFalls A parts.numbers) h.firstChain)
    (carryExact A.Z (P5J.At.arr A.Z)) 0 h.description.t₁ h.description.t₂ 339
    (ReadyInput h.description A.H)
    (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
    (kpBy (firstClauses h)) w
    (SaidWalk (firstThread h parts w) B m₀) (fun _ _ _ a => a.1.1)
    (fallsBy f₁ h.description.first.blocksInOrder) hyes h4
    ⟨Rest.layers, ra, Rest.batch, Rest.behind, Rest.equation, Rest.reply, Rest.switchHead, Rest.head,
      rh, Rest.lookHead, Rest.batchHead, Rest.behindHead, Rest.equationHead, Rest.test⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.first_chain_at_first
