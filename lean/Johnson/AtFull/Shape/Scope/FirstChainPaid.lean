-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/FirstChainPaid.lean: FirstChainFields' NEXT TURN, AT THE TERM's LIST OF FALLS firstFalls A parts.numbers:
the members behind the batchings (14 l + 10, 348) paid by k8_behind_valuesJ_first (AtFullSide/K8/BehindValuesFirst.lean),
funsHeld at the stands of the batchings by held_at_stand | held_at_stand_head (Honest/K8/HeldAtStand.lean), and the falls' cover
at the 25 batchings by front_cover | front_cover_head.

  PaidLeft             the three fields left
  first_chain_paid     **yes₁ ∧ carry₁**

Limits. An implication: hyes, hL and the three fields are premises.
Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.FirstChainFields
import AtFullSide.K8.BehindValuesFirst
import Johnson.Desc.ProofFile.Honest.K8.HeldAtStand
import Johnson.AtFull.Shape.Scope.FrontCover

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Strs Place OpenedColumn)
open VerifiableInference.Desc.First (S)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest (Shape Thread ProverCoinCounts Coins Mid Local ValuesJ NextJ AcceptedJ shapeJ OnlineProverWithDescription onlineProverFromPublicFiles
  onlineProverPartsInUse WiderIn OnlineProverArguments IndexCommitterCoins Cells SaidWalk Fall fallsBy)
open ProofFile.Honest.FirstThread

/-- **THE THREE FIELDS LEFT.** A premise's form. -/
structure PaidLeft {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S ProofFile.Cl V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (J : Nat → S → Prop) (Zs : Shape S)
    (fall : Nat → S → List Fmt.Drawn → Option String) : Prop where
  layers : ∀ l, l < 24 → l % 2 = 0 → PaidJ T Said J Zs fall (14 * l + 3 + 1)
  equation : ∀ l, l < 24 → PaidJ T Said J Zs fall (14 * l + 10 + 1)
  equationHead : PaidJ T Said J Zs fall (337 + 12)

variable {files : VerifierAndGoals.PublicFiles} {W₀ : Type} (I : WiderIn W₀) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {Bs : ProofFile.PureBase}

set_option maxRecDepth 100000 in
/-- **yes₁ AND carry₁ AT THE TERM's FALLS.** -/
theorem first_chain_paid (hK : O.keyOf = ProofFile.Honest.K5.keyOfK3)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz O) = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (B : Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → List OpenedColumn → Prop)
    (m₀ : Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (hyes : (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)).yes startShA 358 = true)
    (hL : AcceptedJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
      (fallsBy (firstFalls A parts.numbers) h.description.first.blocksInOrder) (353 + 1))
    (Rest : PaidLeft (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
      (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀))
      (fallsBy (firstFalls A parts.numbers) h.description.first.blocksInOrder)) :
    (∀ b, b < (firstThread h parts w).bs.length →
      AcceptedJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
        (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
        (fallsBy (firstFalls A parts.numbers) h.description.first.blocksInOrder) b) ∧
    (∀ b, b < (firstThread h parts w).bs.length →
      NextJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
        (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
        (fallsBy (firstFalls A parts.numbers) h.description.first.blocksInOrder) b) := by
  have hstart : ∀ k v hd, ∃ z, ∀ s₀, (firstThread h parts w).begun k v hd s₀ → s₀ = ProofFile.startS A.Z z :=
    fun _ _ _ => ⟨_, fun _ h0 => h0⟩
  have eG : seatGround A = Bs.G₀ := seatGround_of_base hB
  have bh : ∀ l, l < 24 → ValuesJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
      (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀))
      (fallsBy (firstFalls A parts.numbers) h.description.first.blocksInOrder) (14 * l + 9 + 1) := by
    intro l hl
    have k := AtFullSide.K8.Term.k8_behind_valuesJ_first h parts w
      (SaidWalk (firstThread h parts w) B m₀) (fun _ _ _ a => a.1.1)
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA) (l := l) (by omega)
    rw [eG, if_neg (by omega)] at k
    exact k
  have bhh : ValuesJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
      (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀))
      (fallsBy (firstFalls A parts.numbers) h.description.first.blocksInOrder) (337 + 11) := by
    have k := AtFullSide.K8.Term.k8_behind_valuesJ_first h parts w
      (SaidWalk (firstThread h parts w) B m₀) (fun _ _ _ a => a.1.1)
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA) (l := 24) (by omega)
    rw [eG, if_pos rfl] at k
    exact k
  exact first_chain_fields I Sz O hK hA h parts w hB B m₀ (firstFalls A parts.numbers) hyes hL
    (front_cover h parts.numbers)
    (ProofFile.Honest.K8.held_at_stand h.head (firstThread h parts w) rfl rfl hstart _ _)
    (front_cover_head h parts.numbers)
    (ProofFile.Honest.K8.held_at_stand_head h.head (firstThread h parts w) rfl rfl hstart _ _)
    { layers := Rest.layers, behind := fun l hl => .inl (bh l hl), equation := Rest.equation,
      behindHead := .inl bhh, equationHead := Rest.equationHead }

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.first_chain_paid
