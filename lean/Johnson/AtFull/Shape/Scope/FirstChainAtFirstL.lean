-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/FirstChainAtFirstL.lean: first_chain_at_first's ROAD WITH THE LAST TEST PAID BY
ITS ACCEPTANCE: at the base prover's first thread, yes₁ and carry₁ of FromThreadsJ, where each sort of the
eleven that stand open is paid by its values or by the two debts (PaidJ), and the member 354 by one premise
AcceptedJ (AcceptedS gives it: acceptedJ_of): NextJ there comes off the table's strong Carries, no test on
values.

  PaidRest                   the eleven fields, paid either way
  first_chain_at_first_L     **yes₁ ∧ carry₁**

Limits. An implication: hyes, hL and the eleven fields are premises. The list of falls f₁ is free; the term's
is firstFalls A parts.numbers. The crossing to the term is another's. Nothing on soundness, completeness or
hiding.
-/
import Johnson.AtFull.Shape.Scope.FirstChainAtFirst
import Johnson.AtFull.Shape.Scope.SortOf
import Johnson.AtFull.Shape.NextWithoutValues

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Strs Place OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest (Shape Thread ProverCoinCounts Coins Mid Prover Local SaidOk ValuesJ NextJ AcceptedJ AcceptedS shapeJ
  halved OnlineProverWithDescription onlineProverFromPublicFiles onlineProverPartsInUse WiderIn OnlineProverArguments IndexCommitterCoins Cells SaidWalk Fall fallsBy acceptedJ_of)
open ProofFile.Honest.FirstThread
open VerifiableInference.Desc.K2.Honest (carryExact)
open ProofFile.Honest (ridersOf csHead kpBy ReadyInput)

/-- **THE ELEVEN FIELDS LEFT**, each paid by its values or by the two debts. A premise's form. -/
structure PaidRest {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S ProofFile.Cl V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (J : Nat → S → Prop) (Zs : Shape S)
    (fall : Nat → S → List Fmt.Drawn → Option String) : Prop where
  layers : ∀ l, l < 24 → l % 2 = 0 → PaidJ T Said J Zs fall (14 * l + 3 + 1)
  batch : ∀ l, l < 24 → PaidJ T Said J Zs fall (14 * l + 8 + 1)
  behind : ∀ l, l < 24 → PaidJ T Said J Zs fall (14 * l + 9 + 1)
  equation : ∀ l, l < 24 → PaidJ T Said J Zs fall (14 * l + 10 + 1)
  reply : PaidJ T Said J Zs fall (337 + 1)
  switchHead : PaidJ T Said J Zs fall (337 + 2)
  head : PaidJ T Said J Zs fall (337 + 4)
  lookHead : PaidJ T Said J Zs fall (337 + 8)
  batchHead : PaidJ T Said J Zs fall (337 + 10)
  behindHead : PaidJ T Said J Zs fall (337 + 11)
  equationHead : PaidJ T Said J Zs fall (337 + 12)

variable {files : VerifierAndGoals.PublicFiles} {W₀ : Type} (I : WiderIn W₀) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {Bs : ProofFile.PureBase}

/-- **yes₁ AND carry₁, THE LAST TEST BY ITS ACCEPTANCE.** -/
theorem first_chain_at_first_L (hK : O.keyOf = ProofFile.Honest.K5.keyOfK3)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz O) = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (B : Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → List OpenedColumn → Prop)
    (m₀ : Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (f₁ : List (Fall TS))
    (hyes : (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)).yes startShA 358 = true)
    (hL : AcceptedJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
      (fallsBy f₁ h.description.first.blocksInOrder) (353 + 1))
    (Rest : PaidRest (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
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
  have R := reached_fields_head h.head A.H parts.script
    (fallsAfterBatching (firstFalls A parts.numbers) h.firstChain)
    (carryExact A.Z (P5J.At.arr A.Z)) 0 h.description.t₁ h.description.t₂ 339
    (ReadyInput h.description A.H)
    (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
    (kpBy (firstClauses h)) w
    (SaidWalk (firstThread h parts w) B m₀) (fun _ _ _ a => a.1.1)
    (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
    (fallsBy f₁ h.description.first.blocksInOrder) Bs.G₀
  have H : SortOf (PaidJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
      (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) (fallsBy f₁ h.description.first.blocksInOrder)) :=
    { switch := fun l a b => .inl (R.1 l a b)
      layers := Rest.layers
      readsAtt := fun l a b => .inl (ra l a b)
      batch := Rest.batch
      behind := Rest.behind
      equation := Rest.equation
      close := fun l a => .inl (R.2.2.1 l a)
      reply := Rest.reply
      switchHead := Rest.switchHead
      head := Rest.head
      readsHead := .inl rh
      lookHead := Rest.lookHead
      batchHead := Rest.batchHead
      behindHead := Rest.behindHead
      equationHead := Rest.equationHead
      closeHead := .inl R.2.2.2
      finish := .inl R.2.1
      test := .inr ⟨hL,
        nextJ_of_carries _ _ _ (n := 358) (by omega) hyes
          (table_frames h.head hB 354 rfl (firstThread h parts w).ft).1⟩ }
  exact debts_of_paid h.head hB (firstThread h parts w) rfl
    (SaidWalk (firstThread h parts w) B m₀) (fallsBy f₁ h.description.first.blocksInOrder) hyes h4 H

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.first_chain_at_first_L
