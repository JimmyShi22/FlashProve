-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/FirstChainBatch.lean: FirstChainFilled's NEXT TURN: THE BATCHINGS IN FRONT OF THE HEAD'S LINK
PAID BUT FOR hfall AND held. batch_values (Honest/K9/BatchValuesJ.lean) takes env from planEnvB_env (Honest/K4/Law/PlanEnvAtThread.lean) and vals from valsTS_at_stand (ValsTSAtStand.lean); of its
premises hfall and held stay, named. The base prover has no side of the kind K9 (no_side_at_base).

  BatchRest             the seven fields left
  first_chain_batch     **yes₁ ∧ carry₁**

Limits. An implication: hyes, hL, hfall, held and the seven fields are premises. hfall binds the caller to a list of falls
that holds k8Front at the 24 members: the cover on f₁: speaks_of_mem (E2E/TheFalls.lean) with k8FrontFall (Honest/K8/Falls.lean)
in firstFalls. held is a fact on values at the stands: eqPreB's first clause. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.FirstChainFilled
import Johnson.Desc.ProofFile.Honest.K9.BatchValuesJ
import Johnson.Desc.ProofFile.Honest.K9.NoSideAtBase
import Johnson.Desc.ProofFile.Honest.K4.Law.PlanEnvAtThread
import Johnson.AtFull.Shape.ValsTSAtStand

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

/-- **THE SEVEN FIELDS LEFT.** A premise's form. -/
structure BatchRest {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S ProofFile.Cl V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (J : Nat → S → Prop) (Zs : Shape S)
    (fall : Nat → S → List Fmt.Drawn → Option String) : Prop where
  layers : ∀ l, l < 24 → l % 2 = 0 → PaidJ T Said J Zs fall (14 * l + 3 + 1)
  behind : ∀ l, l < 24 → PaidJ T Said J Zs fall (14 * l + 9 + 1)
  equation : ∀ l, l < 24 → PaidJ T Said J Zs fall (14 * l + 10 + 1)
  head : PaidJ T Said J Zs fall (337 + 4)
  batchHead : PaidJ T Said J Zs fall (337 + 10)
  behindHead : PaidJ T Said J Zs fall (337 + 11)
  equationHead : PaidJ T Said J Zs fall (337 + 12)

variable {files : VerifierAndGoals.PublicFiles} {W₀ : Type} (I : WiderIn W₀) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {Bs : ProofFile.PureBase}

set_option maxRecDepth 100000 in
/-- **yes₁ AND carry₁ WITH THE BATCHINGS IN FRONT OF THE HEAD PAID.** -/
theorem first_chain_batch (hK : O.keyOf = ProofFile.Honest.K5.keyOfK3)
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
    (Rest : BatchRest (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
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
  have hb := ProofFile.Honest.K9.batch_values h.head hB (firstThread h parts w) rfl rfl hstart
    (ProofFile.Honest.K9.no_side_at_base I OnBytes.secondHashFunction Sz O hA)
    (SaidWalk (firstThread h parts w) B m₀)
    (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
    (fallsBy f₁ h.description.first.blocksInOrder) hfall held
    (ProofFile.Honest.K4.planEnvB_env h.head hB (firstThread h parts w) rfl rfl hstart _ _)
    (fun g hg a ha s hs => by
      obtain ⟨k, m, E, hT, hJ⟩ := hs
      exact valsTS_at_stand h.head hB (firstThread h parts w)
        (fun _ _ _ r => r.2) (fun _ _ hR => hR) startShA hyes hg ha hT.1 hJ)
  exact first_chain_filled I Sz O hK hA h parts w hB B m₀ f₁ hyes hL
    { layers := Rest.layers, batch := fun l hl => .inl (hb l hl), behind := Rest.behind,
      equation := Rest.equation, head := Rest.head, batchHead := Rest.batchHead,
      behindHead := Rest.behindHead, equationHead := Rest.equationHead }

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.first_chain_batch
