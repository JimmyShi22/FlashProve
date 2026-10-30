-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/GroundAtHeadW.lean: UNDER THE LIBRARY's HEAD, WHERE `onlineProverFromPublicFiles` RETURNS: THE GROUND THAT
`onlineProverFromPublicFiles` HANDS ITS FILLING IS THE GROUND OF THE MAKER's OPENING: `A.G = Bs.G₀`: so laws at `Bs.G₀`
and laws at `A.G` speak of one ground. GENERAL IN THE FILLING.

  `ground_at_head`   `A.G = Bs.G₀`

Limits.
- That `onlineProverFromPublicFiles` returns is a premise (hA); the opening O is the head's.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.AtHead
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.P5J.ChainFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain Block)
open ProofFile.Honest
open P5J (TS)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The ground that `onlineProverFromPublicFiles` hands is the opening's.** -/
theorem ground_at_head {W₀ Rc Tr X₀ X : Type}
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D₀ r₀ Zp Np cF)
    {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) : A.G = Bs.G₀ := by
  have hZ := (atPure_at_laid L hA).1
  obtain ⟨-, hG, -⟩ := atPure_ok hA
  rw [hZ] at hG
  exact Option.some.inj (hG.symm.trans O.blank)

end AtFullSide.K12

#print axioms AtFullSide.K12.ground_at_head
