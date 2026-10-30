-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the slot at the first chain's last test.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/SlotL.lean: the frame's three fields that the rule joins
(fits, exact, fresh) at the side that testSide seats at the first chain's last proximity test, under
the head, at every job at that place where the fresh table came earlier. exact is at the condition
OnEntry (Entry.lean) and the bound budBoth. Public premises: hplan (planB at the seated place; a
named premise of pubTiesT_head_L), To. On the book: that no entry spends of the test's two parts.

Conditional. OnEntry is not shown at a run here. fresh says nothing of the first fresh table's
owner, whose sentence is its sender's. No property of the protocol is claimed.

  slot_firstChainTest   the statement, at every simulators' job
  slot_atSimulatorJob, good_atSimulatorJob   at the job of stateAtFirstChainTest; Good at A := False
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.Entry
import Johnson.Desc.ProofFile.Honest.K12.Sim2.FreshAny
import AtFullSide.K12.RestTiesAtWL
import Johnson.Desc.ProofFile.Honest.K12.Sim2.PublicL

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof
open ProofFile.Honest.Small (ExactMember FreshMember noneSpent)
open H2K.Member (codesFull)

/-- **The slot.** -/
theorem slot_firstChainTest {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) {V W X Pb : Type} (J : TestJob W X) (Js : SimJob Pb)
    (hJ : J.p = (fourOf Np).L) (hfr : J.fresh.isNone = false) (hs : Js.p = (fourOf Np).L)
    (ho : Js.own = false) (hplan : planB (fourOf Np).L codesFull 1 = true)
    (φ : Face V W Pb) (chain firstTree : ℕ) (os : List (Fmt.Shape × Fmt.TreeSource))
    (hos : os.length = 1) (To : OpenTies J Js chain os)
    (fs : List (Fall (P5J.F0T o Zp Np cF).S₁))
    (σ : Side (P5J.F0T o Zp Np cF).S₁ (P5J.F0T o Zp Np cF).Cl V W X Pb)
    (hσ : testSide (P5J.F0T o Zp Np cF).first.blocksInOrder J Js fs = some σ)
    (Bk : ProverCoinCounts) (ord : List Place)
    (hB : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    σ.fits = true ∧
      (∀ u ∈ σ.members, ExactMember φ σ chain firstTree (OnEntry φ J Js codesFull chain os)
        (budBoth Js) u) ∧
      ∀ u ∈ σ.members, FreshMember φ σ Bk ord (budBoth Js) u := by
  obtain ⟨T₀, -, hall⟩ := first_any_head_L (V := V) h J Js hJ hfr hs ho
  obtain ⟨hfit, hmem, -⟩ := hall fs σ hσ
  have T : PubTiesT J Js codesFull os.length := by
    rw [hos]
    exact pubTiesT_head_L h J Js hJ hfr hs ho hplan
  refine ⟨hfit, fun u hu => ?_, fun u hu => fresh_member φ σ Bk ord _ u (hB u hu)⟩
  rw [hmem] at hu
  exact exact_both_entry φ σ J Js codesFull chain firstTree os hfr T₀ T To u hu

/-- **The slot at the simulators' job**, at the state on entry stateAtFirstChainTest (DoorAtL.lean). The public
premises are paid. What is left: OnEntry in the sentence; the test on the book. -/
theorem slot_atSimulatorJob {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) {V W X : Type} (J : TestJob W X)
    (hJ : J.p = (fourOf Np).L) (hfr : J.fresh.isNone = false) (q : VerifiableInference.Desc.K12.P12)
    (hq : q = (fourOf Np).L) (op : List (ℕ × ℕ × ℕ))
    (hop : op = osL.map fun x => ((srcOf 0 x.2).1, (srcOf 0 x.2).2, x.1.a))
    (φ : Face V W ProofFile.Inst) (firstTree : ℕ)
    (fs : List (Fall (P5J.F0T o Zp Np cF).S₁))
    (σ : Side (P5J.F0T o Zp Np cF).S₁ (P5J.F0T o Zp Np cF).Cl V W X ProofFile.Inst)
    (hσ : testSide (P5J.F0T o Zp Np cF).first.blocksInOrder J (simulatorJobAtFirstChainTest Zp q op) fs = some σ)
    (Bk : ProverCoinCounts) (ord : List Place)
    (hB : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    σ.fits = true ∧
      (∀ u ∈ σ.members, ExactMember φ σ 0 firstTree
        (OnEntry φ J (simulatorJobAtFirstChainTest Zp q op) codesFull 0 osL) (budBoth (simulatorJobAtFirstChainTest Zp q op)) u) ∧
      ∀ u ∈ σ.members, FreshMember φ σ Bk ord (budBoth (simulatorJobAtFirstChainTest Zp q op)) u :=
  slot_firstChainTest h J (simulatorJobAtFirstChainTest Zp q op) hJ hfr hq rfl (planB_head_L h) φ 0 firstTree osL osL_length
    (openTies_L h J hJ q op hop) fs σ hσ Bk ord hB

/-- **Good as one term, at A := False**, as K6's head_good has it: plays and acc hold there for
nothing, and the frame's rule does not spend them (Law/Rule/Row.lean's head). exact, fresh and fits
are the three that it spends. -/
theorem good_atSimulatorJob {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) {V W X : Type} (J : TestJob W X)
    (hJ : J.p = (fourOf Np).L) (hfr : J.fresh.isNone = false) (q : VerifiableInference.Desc.K12.P12)
    (hq : q = (fourOf Np).L) (op : List (ℕ × ℕ × ℕ))
    (hop : op = osL.map fun x => ((srcOf 0 x.2).1, (srcOf 0 x.2).2, x.1.a))
    (φ : Face V W ProofFile.Inst) (firstTree : ℕ)
    (fs : List (Fall (P5J.F0T o Zp Np cF).S₁))
    (σ : Side (P5J.F0T o Zp Np cF).S₁ (P5J.F0T o Zp Np cF).Cl V W X ProofFile.Inst)
    (hσ : testSide (P5J.F0T o Zp Np cF).first.blocksInOrder J (simulatorJobAtFirstChainTest Zp q op) fs = some σ)
    (Bk : ProverCoinCounts) (ord : List Place)
    (hB : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true)
    (B : Coins Bk → (P5J.F0T o Zp Np cF).S₁ → ProofFile.Honest.Mid W X → Env → Prop)
    (pre : List (ℕ × ℕ × List Fmt.DeclaredRound)) :
    Good pre φ σ Bk ord 0 firstTree (fun _ _ _ _ => False) B
      (OnEntry φ J (simulatorJobAtFirstChainTest Zp q op) codesFull 0 osL) (budBoth (simulatorJobAtFirstChainTest Zp q op)) :=
  have a := slot_atSimulatorJob h J hJ hfr q hq op hop φ firstTree fs σ hσ Bk ord hB
  { fits := a.1
    plays := fun _ _ _ _ _ hA => hA.elim
    acc := fun _ _ _ _ _ hA => hA.elim
    exact := fun u hu ca m front ds asks hOn hs _ hf hb hh hst =>
      a.2.1 u hu ca m front ds asks hOn hs hf hb hh hst
    fresh := fun u hu => a.2.2 u hu }

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.slot_firstChainTest
#print axioms ProofFile.Honest.K12.Sim2.slot_atSimulatorJob
#print axioms ProofFile.Honest.K12.Sim2.good_atSimulatorJob
