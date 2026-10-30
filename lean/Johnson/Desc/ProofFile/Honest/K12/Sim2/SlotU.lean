-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the slot at the test on G_u of the shared chain.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/SlotU.lean: as SlotL.lean, at the proximity test on G_u: fits,
exact, fresh at the side that testSide seats, under the head, at every job at that place where the
fresh table came earlier. The public premises are paid (rest_exact_head_U's road). Here no wiping is
needed: the state on entry of the job at that place reads the stored columns, so exact stands at the
library's onFreeT. One premise on the book. exact is conditional on onFreeT, which OnFreeTAtHeadU.lean
brings down to two premises on values at a run; the simulators' job that is typed there is given the
stored table's columns opened at "LOC"'s positions. No property of the
protocol is claimed.

  slot_testOnU   the statement
  good_testOnU   Good as one term at A := False
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.FreshAny
import Johnson.Desc.ProofFile.Honest.K12.Sim.RestExactAtHeadU

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof
open ProofFile.Honest.Small (ExactMember FreshMember noneSpent)
open Johnson.G (codesFull2)

/-- **The slot.** -/
theorem slot_testOnU {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) {V W X Pb : Type} (J : TestJob W X) (Js : SimJob Pb)
    (chain : ℕ) (hJ : J.p = (fourOf Np).U) (hfr : J.fresh.isNone = false)
    (hs : Js.p = (fourOf Np).U) (ho : Js.own = false)
    (hop : Js.opens = (fourOf Np).U.nums.first.map fun x =>
      ((srcOf chain x.2).1, (srcOf chain x.2).2, x.1.a))
    (φ : Face V W Pb) (firstTree : ℕ)
    (fs : List (Fall (P5J.F0T o Zp Np cF).S₂))
    (σ : Side (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl V W X Pb)
    (hσ : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js fs = some σ)
    (Bk : ProverCoinCounts) (ord : List Place)
    (hB : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    σ.fits = true ∧
      (∀ u ∈ σ.members, ExactMember φ σ chain firstTree
        (onFreeT φ J Js codesFull2 chain (fourOf Np).U.nums.first) (budOpened J.p.nums.stages) u) ∧
      ∀ u ∈ σ.members, FreshMember φ σ Bk ord (budOpened J.p.nums.stages) u := by
  obtain ⟨-, -, -, hall⟩ := rest_exact_head_U (V := V) h J Js chain hJ hfr hs ho hop
  obtain ⟨hfit, -, hex⟩ := hall fs σ hσ
  exact ⟨hfit, fun u hu => hex φ firstTree u hu,
    fun u hu => fresh_member φ σ Bk ord _ u (hB u hu)⟩

/-- **Good as one term, at A := False**: plays and acc hold there for nothing. -/
theorem good_testOnU {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) {V W X Pb : Type} (J : TestJob W X) (Js : SimJob Pb)
    (chain : ℕ) (hJ : J.p = (fourOf Np).U) (hfr : J.fresh.isNone = false)
    (hs : Js.p = (fourOf Np).U) (ho : Js.own = false)
    (hop : Js.opens = (fourOf Np).U.nums.first.map fun x =>
      ((srcOf chain x.2).1, (srcOf chain x.2).2, x.1.a))
    (φ : Face V W Pb) (firstTree : ℕ)
    (fs : List (Fall (P5J.F0T o Zp Np cF).S₂))
    (σ : Side (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl V W X Pb)
    (hσ : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js fs = some σ)
    (Bk : ProverCoinCounts) (ord : List Place)
    (hB : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true)
    (B : Coins Bk → (P5J.F0T o Zp Np cF).S₂ → ProofFile.Honest.Mid W X → Env → Prop)
    (pre : List (ℕ × ℕ × List Fmt.DeclaredRound)) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) B
      (onFreeT φ J Js codesFull2 chain (fourOf Np).U.nums.first) (budOpened J.p.nums.stages) :=
  have a := slot_testOnU h J Js chain hJ hfr hs ho hop φ firstTree fs σ hσ Bk ord hB
  { fits := a.1
    plays := fun _ _ _ _ _ hA => hA.elim
    acc := fun _ _ _ _ _ hA => hA.elim
    exact := fun u hu ca m front ds asks hOn hs' _ hf hb hh hst =>
      a.2.1 u hu ca m front ds asks hOn hs' hf hb hh hst
    fresh := fun u hu => a.2.2 u hu }

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.slot_testOnU
#print axioms ProofFile.Honest.K12.Sim2.good_testOnU
