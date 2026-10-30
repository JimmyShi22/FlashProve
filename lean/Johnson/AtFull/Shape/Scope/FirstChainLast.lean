-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/FirstChainLast.lean: FirstChainPaid's NEXT TURN: THE ONE EQUATION OF EACH SEGMENT (14 l + 11, 349) BY
equation_field | equationHead_field (Honest/K9/EqValuesJ.lean), from the closed test eqSizesYes at the 25 borders, AND THE FIELD
layers by k4_layers_field_first_thread (Honest/K4/Law/ValuesFieldBase.lean) at K4's lot of the filling.

  first_chain_last     **yes₁ ∧ carry₁** from hyes, hL, hsizes and hsizesH

Limits. Conditional: these four are premises, and none is paid here. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.FirstChainPaid
import Johnson.Desc.ProofFile.Honest.K9.EqValuesJ
import Johnson.Desc.ProofFile.Honest.K4.Law.ValuesFieldBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference.Desc (OpenedColumn)
open P5J (TS)
open ProofFile.Honest (Coins Mid Local NextJ AcceptedJ shapeJ OnlineProverWithDescription onlineProverFromPublicFiles onlineProverPartsInUse WiderIn OnlineProverArguments
  IndexCommitterCoins Cells SaidWalk fallsBy)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K9 (eqSizesYes)

variable {files : VerifierAndGoals.PublicFiles} {W₀ : Type} (I : WiderIn W₀) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {Bs : ProofFile.PureBase}

set_option maxRecDepth 100000 in
/-- **yes₁ AND carry₁: WHAT IS LEFT IS THE PREMISE LIST.** -/
theorem first_chain_last (hK : O.keyOf = ProofFile.Honest.K5.keyOfK3)
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
    (hsizes : ∀ l, l < 24 →
      eqSizesYes (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀) startShA (14 * l + 10 + 1) = true)
    (hsizesH : eqSizesYes (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀) startShA (337 + 12) = true) :
    (∀ b, b < (firstThread h parts w).bs.length →
      AcceptedJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
        (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
        (fallsBy (firstFalls A parts.numbers) h.description.first.blocksInOrder) b) ∧
    (∀ b, b < (firstThread h parts w).bs.length →
      NextJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
        (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
        (fallsBy (firstFalls A parts.numbers) h.description.first.blocksInOrder) b) := by
  have hbegun : ∀ k v hd s₀, (firstThread h parts w).begun k v hd s₀ → ∃ z, s₀ = ProofFile.startS A.Z z :=
    fun _ _ _ _ h0 => ⟨_, h0⟩
  have eq := fun l hl => ProofFile.Honest.K9.equation_field (Bs := Bs) h.head (firstThread h parts w) rfl rfl
    hbegun (SaidWalk (firstThread h parts w) B m₀)
    (fallsBy (firstFalls A parts.numbers) h.description.first.blocksInOrder) startShA (n := 358) (by omega)
    hyes l hl (hsizes l hl)
  have eqh := ProofFile.Honest.K9.equationHead_field (Bs := Bs) h.head (firstThread h parts w) rfl rfl
    hbegun (SaidWalk (firstThread h parts w) B m₀)
    (fallsBy (firstFalls A parts.numbers) h.description.first.blocksInOrder) startShA (n := 358) (by omega)
    hyes hsizesH
  obtain ⟨⟨M, hM, hE⟩, ho⟩ := ProofFile.Honest.K4.k4_lot_at_widerFillAtCPUOWM I OnBytes.secondHashFunction Sz O A.Z A.G
  have ly := ProofFile.Honest.K4.k4_layers_field_first_thread h parts w
    (SaidWalk (firstThread h parts w) B m₀) hB hA _ _ _ hM hE ho
    (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
  exact first_chain_paid I Sz O hK hA h parts w hB B m₀ hyes hL
    { layers := fun l hl he => .inl (ly l hl he), equation := fun l hl => .inl (eq l hl), equationHead := .inl eqh }

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.first_chain_last
