-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at the proximity test on G_omega: the condition at a run, from the seated side.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/OnAtSide.lean: `onOmega_at_maker` (SimO/OnAtMaker.lean) at the side that `Side.seated` gives for the guarded row in the description's shared chain: the stand, the blocks in front and the side's own rounds are paid.

  `side_omega`        what a seated side is
  `onOmega_at_side`   **the statement**

What is left. The clause `asks`. On the run: hR, hrun, hc. On the filling: hg, hgO, hα. On the plan's letters: hb. That the maker returns a book: hB. On the challenges: hdue.

Limits. A conditional. Of the walk (`runC`). No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.SimO.OnAtMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (TableKey)
open VerifiableInference.Desc (Block FileDescription K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St blocks)
open H2K.Pub (sgOf)
open H2K.Member (piOFull)
open ProofFile.Honest.K12.AtProof (fourOf simulatorJobAtOmega jobOmegaReal)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Common StandsAt ready runC midSharedAtW
  Placed Member Part Fall Mid)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **What a seated side is.** -/
theorem side_omega {V W X Pb : Type} {pO : P12} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (hO : (fourOf Np).O = some pO) (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (omega? : Option (W → Front X → ℕ → OnBytes.E)) (Js : SimJob Pb)
    (hJ : Js.p = pO) (ho : Js.own = true) (fs : List (Fall St)) (σ : Side St ProofFile.Cl V W X Pb)
    (hσ : Side.seated (P5J.F0T o Zp Np cF).shared.blocksInOrder pO.place
      (omegaRow (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js) fs = some σ) :
    σ.fits = true ∧
      σ.members = [(firstMember (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js).guarded,
        (restMember (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js).guarded] ∧
      σ.row = omegaRow (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js ∧
      σ.block ∈ (P5J.F0T o Zp Np cF).shared.blocksInOrder ∧ σ.block.place = pO.place ∧
      σ.block.rounds = (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).rounds ∧
      σ.block.oracles = (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).oracles := by
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hσ
  have hbare : testSide (V := V) (P5J.F0T o Zp Np cF).shared.blocksInOrder
      (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js fs =
      some (⟨b, testPairs (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js,
        ProofFile.Honest.fallOf fs pO.place⟩ : Side St ProofFile.Cl V W X Pb) := by
    unfold testSide Side.seated
    show Option.map _ ((P5J.F0T o Zp Np cF).shared.blocksInOrder.find? fun b => b.place == pO.place) = _
    rw [hb]
    rfl
  obtain ⟨hfit, hmem, -⟩ := seated_head_O h hO door weights rand omega? Js fs hJ ho _ hbare
  obtain ⟨b', hf, hp, hr, hor⟩ := find_gomega h hO
  have hbb : b' = b := Option.some.inj (hf.symm.trans hb)
  subst hbb
  refine ⟨?_, ?_, rfl, List.mem_of_find?_eq_some hf, hp, hr, hor⟩
  · show (⟨b', guardRow _, _⟩ : Side St ProofFile.Cl V W X Pb).fits = true
    rw [fits_guardRow]
    exact hfit
  · show membersOf (guardRow _) 0 _ = _
    rw [membersOf_guardRow]
    exact congrArg (List.map Member.guarded) hmem

/-- **The condition at a run, from the seated side.** -/
theorem onOmega_at_side {W₀ Tr Y : Type} {pO : P12} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (hO : (fourOf Np).O = some pO) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    (hB : ProofFile.Honest.bookWhole (P5J.F0T o Zp Np cF) Johnson.G.proofSendsFull.1 Johnson.G.proofSendsFull.2.1
      Johnson.G.proofSendsFull.2.2 (ProofFile.Honest.mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    {P : Prover W₀ ProofFile.Honest.IndexCommitterCoins ProofFile.Inst TableKey Tr Unit Y} (hα : ∀ x, P.key x = x.pub.key) {w₀ : W₀}
    {rc : ProofFile.Honest.IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ ProofFile.Honest.IndexCommitterCoins ProofFile.Inst TableKey Tr Unit Y} {r : RunC (P5J.F0T o Zp Np cF)}
    (wt : W₀ → Weights)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (fs : List (Fall St)) (σ : Side St ProofFile.Cl Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit TableKey)
    (hσ : Side.seated (P5J.F0T o Zp Np cF).shared.blocksInOrder pO.place (omegaRow (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8])) fs = some σ)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (hg : (P.shared.find? fun g => g.place == σ.block.place) =
      some (proverSideOfProximityTest (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) : Placed Empty _ _).needsField)
    (hgO : (P.shared.find? fun g => g.place == ProofFile.Honest.K14.sendPlace 5) = some ⟨ProofFile.Honest.K14.sendPlace 5,
            [(ProofFile.Honest.K14.liftSend (askOf ⟨K1.qAt Zp Np, 0⟩ (fun w : Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey => wt w.w₀)
                      (fun w => ProofFile.Honest.K12.AtProof.randAt (K1.qAt Zp Np) w.rc))
                (ProofFile.Honest.K14.sendingPart (ProofFile.Honest.K14.jobOmega ⟨K1.qAt Zp Np, 0⟩)) :
              ProofFile.Honest.Part Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit)]⟩)
    (hdue : drawsFit (P5J.F0T o Zp Np cF).roundsDeclaredByBlocks.2.1 ρ.shared = true) :
    ∃ (c : ProofFile.Honest.RowCoins
        [(firstPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) : ProofFile.Honest.Part Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit).needsField,
        (restPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) : ProofFile.Honest.Part Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit).needsField])
      (m : ProofFile.Honest.Mid (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit),
      midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) ∧
      ProofFile.Honest.carriedAt Bk k 1 ⟨σ.block.place, 1⟩
        (restPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) : ProofFile.Honest.Part Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit).needsField = .ok c.2.1.2.2 ∧
      m.st.input = ⟨w₀, rc, P.key x⟩ ∧
      drawsFit (((H2K.JointK.laidOf (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p).take (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages)).map (·.1))
        (m.st.lately (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages)) = true ∧
      ((∃ (Dp : H2K.First.Plain) (cc : ℕ → ℕ → List UInt64) (Rw : ProofFile.Honest.K12.PlainRows),
          Dp.ts.length = firstListAtOmega.length ∧
          ProofFile.Honest.K12.Own.ShapeAsksO (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) m.st.input (restFront (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) m)
            (carriedCoins (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) (ProofFile.Honest.K12.stretches _ c.2.1.2.2)) (heardIn (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) m) H2K.Member.codesFull Dp ∧
          DataAsks (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) m.st.input (restFront (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) m)
            (carriedCoins (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) (ProofFile.Honest.K12.stretches _ c.2.1.2.2)) (heardIn (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) m) Dp cc Rw) →
        OnOmega ProofFile.Honest.Face.shared (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) 1 firstListAtOmega
          (restMember (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) : Member Empty _ _ _).guarded c.2.1.2.2 m
          (r.run.beforeAt (ProofFile.Honest.storedShown (P.storedWords w₀ rc) r.run.storedAsked) ⟨σ.block.place, 1⟩)) := by
  obtain ⟨hfit, hmem, hrow, hblk, hpl, hr, hor⟩ := side_omega h hO _ _ _ none (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) rfl rfl fs σ hσ
  have hk := planOk_head_O h hO
  have hlaid : σ.block.rounds.zip σ.block.oracles = (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).laid := by
    rw [hr, hor]
    exact zip_laid pO hk
  have hsh := planOk_shaped h.laid.planOk σ.block hblk
  unfold VerifiableInference.Desc.Block.shaped at hsh
  rw [Bool.and_eq_true] at hsh
  have hlen : σ.block.rounds.length ≤ σ.block.oracles.length := Nat.le_of_eq (beq_iff_eq.1 hsh.1).symm
  have hn := nums_head_O h hO
  obtain ⟨s, next, rest, hlit⟩ : ∃ s next rest, piOFull.nums.stages = s :: next :: rest := ⟨_, _, _, rfl⟩
  have hst : (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages = s :: next :: rest := by
    show pO.nums.stages = _
    rw [hn, hlit]
  have l1 : (firstPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) : ProofFile.Honest.Part Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit).moves.length =
      firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages :=
    (congrArg List.length (first_moves (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO))).trans (len_movesFrom (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) _ _ _)
  have l2 : (restPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) : ProofFile.Honest.Part Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit).moves.length =
      restLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages :=
    (congrArg List.length (rest_moves (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) s next rest hst)).trans (len_movesFrom (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) _ _ _)
  have hpos : ((restMember (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) : Member Empty _ _ _).guarded).part.moves.length ≠ 0 := by
    show ((restPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) : ProofFile.Honest.Part Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit).moves.map _).length ≠ 0
    rw [List.length_map, l2]
    intro h0
    have Q : PublicTiesOwn (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) H2K.Member.codesFull 3 := publicTiesOwn_head h hO _ _ _ none _ rfl rfl
    have q' := Q.rounds
    omega
  have hu : (restMember (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) : Member Empty _ _ _).guarded ∈ σ.members := by
    rw [hmem]
    exact List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)
  obtain ⟨pre, t, S⟩ := stands_member h.laid.planOk hR σ hblk hfit _ hu hpos _ hg (by rw [hrow]; rfl)
  have e : ((σ.row.take ((restMember (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) : Member Empty _ _ _).guarded).number).map (·.1.moves.length)).sum =
      firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages := by
    rw [hrow]
    have q : ((firstPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) : ProofFile.Honest.Part Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit).needsField).moves.length =
        firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages := by
      show (List.map _ _).length = _
      rw [List.length_map]
      exact l1
    exact (Nat.add_zero _).trans q
  rw [e] at S
  obtain ⟨nO, h1, rfl⟩ := omega_of_four hO
  have hnd := (ProofFile.Honest.places_nodup (((P5J.F0T o Zp Np cF).planOk_ok).1 h.laid.planOk).places).2.1
  have h10 := pre_at_omega (o := o) (Zp := Zp) (Np := Np) (cF := cF)
    b1 b2 b3 b4 b5 b6 b7 b8 hb hnd nO h1 pre t σ.block S.cut
    (hpl.trans (H2K.JointK.place_of_p12At _ _))
  exact onOmega_at_maker h hO b1 b2 b3 b4 b5 b6 b7 b8 hb hB hα wt hR σ hpl pre t S h10 hrun hc hg hlaid hlen hgO hdue

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.side_omega
#print axioms ProofFile.Honest.K12.Light.onOmega_at_side
