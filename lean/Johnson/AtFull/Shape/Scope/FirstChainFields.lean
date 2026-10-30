-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/FirstChainFields.lean: FirstChainBatch's NEXT TURN: THE OUTPUT HEAD (341) PAID BY
valuesAtTheOutputHead (Honest/K6/Term/Values.lean), AND THE HEAD'S BATCHING (347) PAID BUT FOR ITS fall AND ITS held:
batch_values_head, with ends by endsTestAcceptsAtEveryStandOfTheBatching (the same file).

  FieldsRest            the five fields left
  first_chain_fields    **yes₁ ∧ carry₁**

Limits. An implication: hyes, hL, the falls' cover (hfall, hfallH), held, heldH and the five fields are premises. Nothing on
soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.FirstChainBatch
import Johnson.Desc.ProofFile.Honest.K6.Term.Values

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
open ProofFile.Honest.K9 (StandJ)

/-- **THE FIVE FIELDS LEFT.** A premise's form. -/
structure FieldsRest {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S ProofFile.Cl V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (J : Nat → S → Prop) (Zs : Shape S)
    (fall : Nat → S → List Fmt.Drawn → Option String) : Prop where
  layers : ∀ l, l < 24 → l % 2 = 0 → PaidJ T Said J Zs fall (14 * l + 3 + 1)
  behind : ∀ l, l < 24 → PaidJ T Said J Zs fall (14 * l + 9 + 1)
  equation : ∀ l, l < 24 → PaidJ T Said J Zs fall (14 * l + 10 + 1)
  behindHead : PaidJ T Said J Zs fall (337 + 11)
  equationHead : PaidJ T Said J Zs fall (337 + 12)

variable {files : VerifierAndGoals.PublicFiles} {W₀ : Type} (I : WiderIn W₀) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {Bs : ProofFile.PureBase}

set_option maxRecDepth 100000 in
/-- **yes₁ AND carry₁ WITH THE OUTPUT HEAD AND THE HEAD'S BATCHING IN.** -/
theorem first_chain_fields (hK : O.keyOf = ProofFile.Honest.K5.keyOfK3)
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
    (hfall : ∀ l, l < 24 → ∀ s ds, fallsBy f₁ h.description.first.blocksInOrder (14 * l + 8 + 1) s ds = none →
      ProofFile.Honest.K8.k8Front s ds = none)
    (held : ∀ l, l < 24 → ∀ s, StandJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA) (14 * l + 8 + 1) s →
      ∀ tl funs, s.tl? = some tl → s.funs? = some funs → tl.funsHeld funs = true)
    (hfallH : ∀ s ds, fallsBy f₁ h.description.first.blocksInOrder (337 + 10) s ds = none →
      ProofFile.Honest.K8.k8Front s ds = none)
    (heldH : ∀ s, StandJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA) (337 + 10) s →
      ∀ tl funs, s.tl? = some tl → s.funs? = some funs → tl.funsHeld funs = true)
    (Rest : FieldsRest (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
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
  have hstart : ∀ k v hd, ∃ z, ∀ s₀, (firstThread h parts w).begun k v hd s₀ → s₀ = ProofFile.startS A.Z z :=
    fun _ _ _ => ⟨_, fun _ h0 => h0⟩
  have hd : ValuesJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
      (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) (fallsBy f₁ h.description.first.blocksInOrder) (337 + 4) :=
    ProofFile.Honest.K6.Term.valuesAtTheOutputHead _ _ _ _ _ _ _ _ _ _ _ h.head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _
  have hbh := ProofFile.Honest.K9.batch_values_head h.head hB (firstThread h parts w) rfl rfl hstart
    (ProofFile.Honest.K9.no_side_at_base I OnBytes.secondHashFunction Sz O hA)
    (SaidWalk (firstThread h parts w) B m₀)
    (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
    (fallsBy f₁ h.description.first.blocksInOrder) hfallH heldH
    (fun s hs => ProofFile.Honest.K6.Term.endsTestAcceptsAtEveryStandOfTheBatching _ _ _ _ _ _ _ _ _ _ _
      h.head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB hs)
  exact first_chain_batch I Sz O hK hA h parts w hB B m₀ f₁ hyes hL hfall held
    { layers := Rest.layers, behind := Rest.behind, equation := Rest.equation, head := .inl hd,
      batchHead := .inl hbh, behindHead := Rest.behindHead, equationHead := Rest.equationHead }

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.first_chain_fields
