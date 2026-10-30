-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- the rows of lotU and lotW pay their shares of BudDebts.
/-
Johnson/M1/SlotsSeat.lean: under the library's head: the jobs that halfU and halfW make stand at the seated places with the fresh table earlier; simAtU and
simAtW are at these places; so every row of lotU and lotW (Johnson/M1/SlotsUW.lean) pays the body of the fields bud₂ and bud₃ of BudDebts, at every due list
of challenges. So the statements of BudU.lean and BudGuard.lean have members wherever such a row exists. No property of the protocol is claimed.

-/
import Johnson.M1.SlotsUW
import Johnson.M1.BudU
import Johnson.M1.BudGuard
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block Chain)
open OnBytes (TableKey)
open Desc.K14 (St blocks)

variable {W₀ X : Type} {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- Under the head the plan has its eight blocks. -/
theorem eight_head (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) :
    ∃ b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit,
      blocks (VerifiableInference.Desc.K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8] := by
  obtain ⟨_, _, hw⟩ := facts_at_head h
  unfold blocks
  rw [hw]
  exact ⟨_, _, _, _, _, _, _, _, rfl⟩

/-- **simAtU under the head.** -/
theorem simAtU_head (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) :
    (simAtU Zp).p = (fourOf Np).U ∧ (simAtU Zp).own = false ∧
      (simAtU Zp).opens = (fourOf Np).U.nums.first.map fun x =>
        ((srcOf 1 x.2).1, (srcOf 1 x.2).2, x.1.a) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ := eight_head h
  unfold simAtU
  rw [h.laid.places]
  show (match blocks (VerifiableInference.Desc.K1.qAt Zp Np) with
    | some bs => simHeadU Zp Np bs
    | none => _).p = _ ∧ _ ∧ _
  simp only [hb]
  exact ⟨rfl, rfl, rfl⟩

/-- **The job at G_u under the head.** -/
theorem realU_ties (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) (wt : W₀ → Weights)
    (enc : W₀ → IndexCommitterCoins → ℕ → ℕ → Option (List Cb.Gl.F)) {J : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit}
    (hJ : realU wt enc Zp = some J) : J.p = (fourOf Np).U ∧ J.fresh.isNone = false := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ := eight_head h
  rw [realU_at_head h b1 b2 b3 b4 b5 b6 b7 b8 hb wt enc] at hJ
  obtain rfl := Option.some.inj hJ
  exact ⟨rfl, rfl⟩

/-- **Every row of lotU pays the body of bud₂.** -/
theorem rowU_owes (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF)
    (φ : Face Empty (Common W₀ IndexCommitterCoins TableKey) TableKey) (wt : Pub → W₀ → Weights)
    (enc : Pub → W₀ → IndexCommitterCoins → ℕ → ℕ → Option (List Cb.Gl.F)) (G : Ground)
    (r : Unlettered Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey) (hr : r ∈ (lotU φ wt enc).rows Zp G)
    {Bk : ProverCoinCounts}
    (L : Lettered Bk (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₂ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl Empty
      (Common W₀ IndexCommitterCoins TableKey) Unit TableKey)
    (hpl : L.place = r.place) (hrow : L.row = r.row) (hbud : L.bud = r.bud) :
    ∀ σ, L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws,
      ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true →
      L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
        (asksFrom (treeAsks (P5J.F0T OnBytes.secondHashFunction Zp Np cF) ρ 1) (u.rounds.map (·.2.length))
          (((rowsOfChain (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).take n).map (·.2.length)).sum) := by
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hr
  have hJ' : realU (wt Zp) (enc Zp) Zp = some J := by
    cases e : realU (wt Zp) (enc Zp) Zp with
    | none => rw [e] at hJ; cases hJ
    | some J' =>
      rw [e] at hJ
      exact congrArg some (List.mem_singleton.1 hJ).symm
  obtain ⟨hp, hf⟩ := realU_ties h _ _ hJ'
  obtain ⟨hs, ho, -⟩ := simAtU_head h
  refine Johnson.M1.BudW.budOwed₂_at_U h L J hp hf (simAtU Zp) hs ho hpl hrow fun n ds asks hb => ?_
  rw [hbud]
  show budOpened J.p.nums.stages n ds asks
  rw [hp, ← hs]
  exact hb.2

/-- **The job at the own test under the head.** -/
theorem realW_ties {Xi Rc Tr : Type} (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) (S : OnBytes.HonestTrace.Sz)
    (Fd : VerifiableInference.Desc.FileDescription Xi) (enter : Fd.S₃ → Except String VerifiableInference.Desc.K12.T12)
    (pile : Pub → Ground → K13.PileOf Xi) (no : VerifiableInference.Desc.Place → Nat)
    (readers : Local W₀ Rc Xi Tr → Readers) (weights : Local W₀ Rc Xi Tr → Weights)
    (rand : Desc.K14.P14 → Local W₀ Rc Xi Tr → TableRand) (G : Ground)
    {J : TestJob (Local W₀ Rc Xi Tr) X}
    (hJ : realW S Fd enter pile no readers weights rand Zp G = some J) :
    J.p = (fourOf Np).W ∧ J.fresh.isNone = false := by
  unfold realW jobRealW at hJ
  rw [(stages_at_head h).1] at hJ
  simp only [Option.bind_some] at hJ
  cases hA : sendPub Zp with
  | none => rw [hA] at hJ; cases hJ
  | some A =>
    rw [hA] at hJ
    simp only [Option.bind_some] at hJ
    cases hm : OnBytes.linMessageW Zp.first.lin with
    | none => rw [hm] at hJ; cases hJ
    | some m =>
      rw [hm] at hJ
      obtain rfl := Option.some.inj hJ
      exact ⟨rfl, rfl⟩

/-- **Every row of lotW pays the body of bud₃.** -/
theorem rowW_owes (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF)
    (φ : Face (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Inst) (I : WiderIn W₀) (o' : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (G : Ground)
    (r : Unlettered (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X Inst)
    (hr : r ∈ (lotW φ I o' S O).rows Zp G) {Bk : ProverCoinCounts}
    (L : Lettered Bk (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl
      (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X Inst)
    (hpl : L.place = r.place) (hrow : L.row = r.row) (hbud : L.bud = r.bud) :
    ∀ σ, L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws,
      ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true →
      L.bud u.number ((ρ.second.drop n).take u.rounds.length)
        (asksFrom (treeAsks (P5J.F0T OnBytes.secondHashFunction Zp Np cF) ρ 2) (u.rounds.map (·.2.length))
          (((rowsOfChain (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder).take n).map (·.2.length)).sum) := by
  have hr' : r ∈ rowsW φ I o' S O Zp G := hr
  unfold rowsW at hr'
  have hP := h.laid.places
  split at hr'
  · rename_i s N c h1 h2 h3
    have eN : N = Np := Except.ok.inj (h2.symm.trans hP)
    subst eN
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hr'
    have hJ' : realW S (P5J.F0T o' Zp N c) VerifiableInference.Desc.K12.Seat.enterOwn O.pile (K1.lotNo o' Zp)
        (fun w => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩) (fun w => I.weights Zp w.w₀)
        (fun P w => randAt P w.rc) Zp G = some J := by
      cases e : realW S (P5J.F0T o' Zp N c) VerifiableInference.Desc.K12.Seat.enterOwn O.pile (K1.lotNo o' Zp)
        (fun w => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩) (fun w => I.weights Zp w.w₀)
        (fun P w => randAt P w.rc) Zp G with
      | none => rw [e] at hJ; cases hJ
      | some J' =>
        rw [e] at hJ
        exact congrArg some (List.mem_singleton.1 hJ).symm
    obtain ⟨hp, hf⟩ := realW_ties h S _ _ _ _ _ _ _ G hJ'
    exact Johnson.M1.BudW.budOwed₃_guarded h L J hp hf (simAtW o' Zp N c) rfl rfl hpl hrow
      fun n ds asks hb => by rw [hbud]; exact hb
  · cases hr'

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.simAtU_head
#print axioms ProofFile.Honest.K12.Sim2.realU_ties
#print axioms ProofFile.Honest.K12.Sim2.rowU_owes
#print axioms ProofFile.Honest.K12.Sim2.realW_ties
#print axioms ProofFile.Honest.K12.Sim2.rowW_owes
