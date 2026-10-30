-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WLaid.lean: laws on the value of ProofFile's `LastLetters` (WLaidDefs.lean).

  `lastLetters_depths` the depths at a return of the maker
  `rest_at_filling`    at the filling the frame hands the test's coins at every k

Limits. `TakenDepths` is a premise. `logLength` alone. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WLaidDefs
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WDepths
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFilling
import Johnson.Desc.ProofFile.Honest.Thread.TheLaterThreads

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Third (S₃)
open ProofFile.Honest.K12.Light (ManyJob)
open ProofFile.Honest.FirstThread (HeadAtReturn LastLetters)
open P5J (F0T AtMgA)
open AtFullSide.K12 (jobAtFill job_at_filling lent_at_filling)

section
variable {W₀ Rc Tr X₀ X W₂ : Type} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **The depths at a return of the maker.** -/
theorem lastLetters_depths {files : VerifierAndGoals.PublicFiles} (h : HeadAtReturn files A) (r₁ n₀ : ℕ)
    (toCommon : Local W₀ Rc ProofFile.Inst Tr → W₂)
    (tb₁ : Fmt.TreeSource → Coins A.B → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Place × Table)
    (tb₂ : Fmt.TreeSource → Coins A.B → W₂ → List Fmt.Drawn → Place × Table)
    (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) X) (own₀ : X)
    (hp : J.p = (ProofFile.Honest.K12.AtProof.fourOf h.places).W)
    (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k)
    (hrest : ∀ k : Coins A.B, ∃ c, handedRest 2 J k = some c)
    (hD : TakenDepths r₁ toCommon tb₁ tb₂) :
    ∀ d ∈ A.F.second.blocksInOrder.flatMap (·.rounds), ∀ o ∈ d.opens, ∀ k w hd,
      (lastTable r₁ toCommon tb₁ tb₂ (ownLast J own₀ n₀) o.2 k w hd).2.logLength = o.1.a := by
  obtain ⟨filling, hret⟩ := h.returned
  obtain ⟨-, -, hF, -⟩ := atPure_ok hret
  have eF : A.F = F0T OnBytes.secondHashFunction A.Z h.places h.firstChain :=
    Except.ok.inj (hF.symm.trans h.head.laid.value)
  rw [eF]
  exact table_depths_last h.head.toAtMg
    (ProofFile.Honest.K14.alike_last_at_laid h.head.scope h.head.laid) r₁ n₀ toCommon tb₁ tb₂ J own₀ hp hk
    hrest hD

end

/-- **At the filling the frame hands the test's coins at every k.** -/
theorem rest_at_filling {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    {M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit}
    (hs : A.H.second = [(proverSideOfProximityTest M.toRun.toTest).needsField])
    (hp : M.p = (ProofFile.Honest.K12.AtProof.fourOf Np).W) (k : Coins A.B) :
    ∃ c, handedRest 2 M.toRun.toTest k = some c := by
  obtain ⟨c, hc⟩ := lent_at_filling h I S O hA k _ (by rw [hs]; exact List.mem_singleton.2 rfl)
  have ep : M.toRun.toTest.p.place = ProofFile.Honest.K12.AtProof.placeW := by
    show M.p.place = _
    rw [hp]
    exact ProofFile.Honest.K12.AtProof.p12At_place _ _
  have hc' : lendRow A.B (A.B.rowsOf 2) (k.look 2) ProofFile.Honest.K12.AtProof.placeW
      [Part.needsField (firstPart M.toRun.toTest : Part (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) _ _),
        Part.needsField (restPart M.toRun.toTest)] 0 = .ok c := hc
  have e := lendRow_second hc'
  have e2 : lendPart A.B (A.B.rowsOf 2) (k.look 2) ⟨ProofFile.Honest.K12.AtProof.placeW, 1⟩
        (restPart (V := Empty) M.toRun.toTest) =
      lendPart A.B (A.B.rowsOf 2) (k.look 2) ⟨ProofFile.Honest.K12.AtProof.placeW, 1⟩
        (Part.needsField (restPart (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) M.toRun.toTest)) :=
    eq_of_heq (lendPart_cross _ _ _ _ _ _ rfl rfl rfl)
  unfold handedRest
  rw [ep, e2, e]
  exact ⟨_, rfl⟩

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.lastLetters_depths
#print axioms ProofFile.Honest.K12.AtFile.rest_at_filling
