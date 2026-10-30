-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the row of the first chain's last test, on one list.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/KeystoneL.lean: the rows of simulatorLot (SlotValueL.lean) laid
as a list: Good at that list (good_atSimulatorJob), and what that list is by make, which is what
onAtRun_paid (ListPaid.lean) asks of a list. That theorem is not applied here: its other premises
stay the caller's.

  mem_rowsOfLot     a row of the value is the row of the job that proxLotAt lays
  kind_p12OfMade    the test's place is of the kind K12
  row_good          Good at the list's own side, its On, its bud, at a book that spends nothing of K12
  row_facts         the list's place, row, On and bud, and the simulators' job: each premise of
                    onAtRun_paid and of a rule's clause on a list that this list meets by make

No property of the protocol is claimed. Conditional on On.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.SlotValueL
import Johnson.Desc.ProofFile.Honest.K12.Sim2.StandL

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open ProofFile.Honest.Small (noneSpent)
open H2K.Member (codesFull)

variable {W₀ X : Type}

/-- **A row of the value is the row of the job that the lot lays.** -/
theorem mem_rowsOfLot (I : WiderIn W₀) (S' : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground)
    (r : Unlettered (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X Inst)
    (hr : r ∈ rowsOfLot I S' Z G) :
    ∃ pl, finishAt Z G = some pl ∧ fitsL (H2U.p12OfMade Z.made) pl = true ∧
      r = rowOfJob Z (jobOfLot I S' Z G pl) := by
  unfold rowsOfLot at hr
  split at hr
  · split at hr
    · obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hr
      have hJ' := Option.mem_toList.1 hJ
      obtain ⟨pl, hf, hj⟩ := Option.bind_eq_some_iff.1 hJ'
      split at hj
      · rename_i hfit
        exact ⟨pl, hf, hfit, by rw [Option.some.inj hj]⟩
      · cases hj
    · cases hr
  · cases hr

/-- The place of the first chain's last test is of the kind K12. -/
theorem kind_p12OfMade (Zp : ProofFile.Pub) : (H2U.p12OfMade Zp.made).place.kind = .K12 := by
  unfold H2U.p12OfMade
  dsimp only
  split
  · unfold H2U.proximityTestParametersAt
    split
    · rfl
    · split <;> rfl
  · rfl

/-- **Good at the list's own side**, at a book that spends nothing of a proximity test's parts. -/
theorem row_good {Z' : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} (h : P5J.AtMg OnBytes.secondHashFunction Z' D₀ r₀ Zp Np cF)
    (I : WiderIn W₀) (S' : OnBytes.HonestTrace.Sz) (G : Ground) (pl : K2.SwitchPlace) (Bk : ProverCoinCounts)
    (T : Local W₀ IndexCommitterCoins Inst Cells → Thread Bk S ProofFile.Cl (Local W₀ IndexCommitterCoins Inst Cells)
      (Local W₀ IndexCommitterCoins Inst Cells) X Inst)
    (Sd : Local W₀ IndexCommitterCoins Inst Cells → ℕ → Coins Bk → Mid (Local W₀ IndexCommitterCoins Inst Cells) X → Prop)
    (bs : List (Block S ProofFile.Cl)) (fs : List (Fall S))
    (σ : Side S ProofFile.Cl (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X Inst)
    (hσ : ((rowOfJob Zp (jobOfLot I S' Zp G pl)).lay T Sd bs).side cF.blocksInOrder fs = some σ)
    (ord : List Place) (hB : ∀ o : Addr, o.place.kind = .K12 → noneSpent Bk o = true)
    (firstTree : ℕ) (B : Coins Bk → S → Mid (Local W₀ IndexCommitterCoins Inst Cells) X → Env → Prop)
    (pre : List (ℕ × ℕ × List Fmt.DeclaredRound)) :
    Good pre Face.own σ Bk ord 0 firstTree (fun _ _ _ _ => False) B
      ((rowOfJob Zp (jobOfLot I S' Zp G pl)).lay T Sd bs).On
      ((rowOfJob Zp (jobOfLot I S' Zp G pl)).lay T Sd bs).bud := by
  have hq := numbersL_at_head h
  have hpl : σ.block.place = (H2U.p12OfMade Zp.made).place := side_place hσ
  exact good_atSimulatorJob h (jobOfLot I S' Zp G pl) hq rfl (H2U.p12OfMade Zp.made) hq _ rfl
    Face.own firstTree fs σ hσ Bk ord
    (fun u _ => hB _ (by show σ.block.place.kind = _; rw [hpl]; exact kind_p12OfMade _)) B pre

/-- **What the list is, by make**: each of these is a premise of onAtRun_paid. -/
theorem row_facts (Zp : ProofFile.Pub) (J : TestJob (Local W₀ IndexCommitterCoins Inst Cells) X) {Bk : ProverCoinCounts}
    (T : Local W₀ IndexCommitterCoins Inst Cells → Thread Bk S ProofFile.Cl (Local W₀ IndexCommitterCoins Inst Cells)
      (Local W₀ IndexCommitterCoins Inst Cells) X Inst)
    (Sd : Local W₀ IndexCommitterCoins Inst Cells → ℕ → Coins Bk → Mid (Local W₀ IndexCommitterCoins Inst Cells) X → Prop)
    (bs : List (Block S ProofFile.Cl)) :
    ((rowOfJob Zp J).lay T Sd bs).place = J.p.place ∧
      ((rowOfJob Zp J).lay T Sd bs).row = testPairs J (simulatorJobOfLot Zp) ∧
      ((rowOfJob Zp J).lay T Sd bs).On =
        OnEntry Face.own J (simulatorJobOfLot Zp) codesFull 0 osL ∧
      ((rowOfJob Zp J).lay T Sd bs).bud = budBoth (simulatorJobOfLot Zp) ∧
      (simulatorJobOfLot Zp).rec₀ = stateAtFirstChainTest Zp ∧
      (simulatorJobOfLot Zp).p = H2U.p12OfMade Zp.made ∧ (simulatorJobOfLot Zp).own = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The first trees that the list names are the seated place's. -/
theorem osL_at_head {Z' : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z' D₀ r₀ Zp Np cF) : osL = (H2U.p12OfMade Zp.made).nums.first := by
  rw [numbersL_at_head h, nums_head_L h]
  rfl

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.mem_rowsOfLot
#print axioms ProofFile.Honest.K12.Sim2.kind_p12OfMade
#print axioms ProofFile.Honest.K12.Sim2.row_good
#print axioms ProofFile.Honest.K12.Sim2.row_facts
#print axioms ProofFile.Honest.K12.Sim2.osL_at_head
