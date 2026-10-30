-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at the proximity test on G_omega: the condition at a run, at the maker's book.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/OnAtMaker.lean: `onOmega_at_head` (SimO/OnAtHead.lean) with the book's ties and the premises on the first part's challenges paid: at whatever book the maker returns, at challenges that the description's rounds can draw.

  `firstTies_at_run`     `FirstTies` and the fit of the first part's challenges, from the fit of the shared chain's challenges
  `onOmega_at_maker`     **the statement**

What is left. The clause `asks`. On the run: hR, hrun, hc, S, h10. On the filling: hg, hgO, hlaid, hα. On the plan's letters: hb. That the maker returns a book: hB. On the challenges: hdue.

Limits. A conditional. Of the walk (`runC`). No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.SimO.OnAtHead
import Johnson.Desc.ProofFile.Honest.K12.SimO.BookO
import Johnson.Desc.ProofFile.Honest.K3.Law.StageFacts
import Johnson.Desc.ProofFile.Honest.K12.OnFreeTAtHeadU

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (TableKey)
open VerifiableInference.Desc (Block FileDescription K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12)
open Desc.K14 (St blocks)
open H2K.Pub (sgOf)
open H2K.Member (piOFull)
open ProofFile.Honest.K12.AtProof (fourOf simulatorJobAtOmega jobOmegaReal)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Common StandsAt ready runC midSharedAtW
  Placed Member)

/-- **`FirstTies` at a run.** -/
theorem firstTies_at_run {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hR : ready F Bk P w₀ rc x k = .ok R)
    (J : TestJob (Common W₀ Rc Ky) X₀) (Js : SimJob Pb)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc Ky) X₀ Pb) (u : Member V (Common W₀ Rc Ky) X₀ Pb)
    (pre t : List (Block F.S₂ F.Cl)) (i : ℕ) (S : StandsAt F.shared.blocksInOrder R.shared σ u pre t i)
    (hi : firstLen J.p.nums.stages ≤ σ.block.rounds.length)
    (hor : σ.block.rounds.length ≤ σ.block.oracles.length)
    (hlaid : σ.block.rounds.zip σ.block.oracles = J.laid)
    (F₁ : FirstPubOwn J Js) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: next :: rest)
    (hdue : drawsFit F.roundsDeclaredByBlocks.2.1 ρ.shared = true) :
    drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
        ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) = true ∧
      FirstTies J s next rest
        (byNo ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)))
        ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) := by
  have hD := ProofFile.Honest.K3.Law.drawsFit_take _ _ (firstLen J.p.nums.stages)
    (ProofFile.Honest.K3.Law.drawsFit_drop _ _ (pre.flatMap (·.rounds)).length hdue)
  have e1 : ((F.roundsDeclaredByBlocks.2.1).drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages) =
      ((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1) := by
    show ((F.shared.blocksInOrder.flatMap (·.rounds)).drop _).take _ = _
    rw [S.cut, List.flatMap_append, List.flatMap_cons, List.drop_left, List.take_append_of_le_length hi]
    have e2 : (H2K.JointK.laidOf J.p).map (·.1) = σ.block.rounds := by
      have e3 : H2K.JointK.laidOf J.p = J.laid := rfl
      rw [e3, ← hlaid]
      exact List.map_fst_zip hor
    rw [List.map_take, e2]
  rw [e1] at hD
  have FP := formPub_of_B J.p s next rest hst F₁.form
  refine ⟨hD, hst, F₁.enough, FP.sorts, F₁.tables, ?_, fun n h => (List.getD_eq_getElem _ _ h).symm⟩
  have h := drawsFit_length _ _ hD
  rw [h, List.length_map, List.length_take]
  exact Nat.min_eq_left F₁.enough

/-- **The condition at a run, at whatever book the maker returns.** -/
theorem onOmega_at_maker {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {W₀ Tr Y : Type} {pO : P12} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (hO : (fourOf Np).O = some pO) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    (hB : ProofFile.Honest.bookWhole (P5J.F0T o Zp Np cF) Johnson.G.proofSendsFull.1 Johnson.G.proofSendsFull.2.1
      Johnson.G.proofSendsFull.2.2 (ProofFile.Honest.mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    {P : Prover W₀ ProofFile.Honest.IndexCommitterCoins ProofFile.Inst TableKey Tr Unit Y} (hα : ∀ x, P.key x = x.pub.key) {w₀ : W₀}
    {rc : ProofFile.Honest.IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ ProofFile.Honest.IndexCommitterCoins ProofFile.Inst TableKey Tr Unit Y} {r : RunC (P5J.F0T o Zp Np cF)}
    (wt : W₀ → Weights)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side St ProofFile.Cl Empty (Common W₀ ProofFile.Honest.IndexCommitterCoins TableKey) Unit TableKey) (hσ : σ.block.place = pO.place)
    (pre t : List (Block St ProofFile.Cl))
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ
      (restMember (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) : Member Empty _ _ _).guarded pre t (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages))
    (h10 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 10)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (hg : (P.shared.find? fun g => g.place == σ.block.place) =
      some (proverSideOfProximityTest (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) : Placed Empty _ _).needsField)
    (hlaid : σ.block.rounds.zip σ.block.oracles = (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).laid)
    (hor : σ.block.rounds.length ≤ σ.block.oracles.length)
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
  have hn := nums_head_O h hO
  obtain ⟨s, next, rest, hlit⟩ : ∃ s next rest, piOFull.nums.stages = s :: next :: rest := ⟨_, _, _, rfl⟩
  have hst : (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages = s :: next :: rest := by
    show pO.nums.stages = _
    rw [hn, hlit]
  have F₁ : FirstPubOwn (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) :=
    firstPubOwn_head h hO _ _ _ none _ rfl rfl
  have hle := S.le
  have hi : firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages ≤ σ.block.rounds.length := by omega
  obtain ⟨hfit, T⟩ := firstTies_at_run hR (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) σ _ pre t _ S hi hor hlaid F₁ s next rest hst hdue
  have FP := formPub_of_B (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p s next rest hst F₁.form
  have hk' : s.k = (sgOf s).h + (sgOf s).g := by
    have := FP.hk
    show s.k = s.h + (s.k - s.h)
    omega
  have hpl : pO.place = ⟨2, none, 10, .K12⟩ := by
    obtain ⟨nO, -, rfl⟩ := omega_of_four hO
    exact H2K.JointK.place_of_p12At _ _
  have hT := tiesO_head h hB
  have hT' : ProofFile.Honest.K12.Own.tiesOB Bk (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.place (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).members.length = true := by
    show ProofFile.Honest.K12.Own.tiesOB Bk pO.place 2 = true
    rw [hpl]
    exact hT
  unfold ProofFile.Honest.K12.Own.tiesOB at hT'
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hT'
  obtain ⟨⟨t2, t3⟩, t4⟩ := hT'
  obtain ⟨e₂, he₂, k2⟩ := Option.map_eq_some_iff.1 t2
  refine onOmega_at_head h hO b1 b2 b3 b4 b5 b6 b7 b8 hb hα wt hR σ hσ pre t S h10 hrun hc hg hlaid hgO
    (bookCutsOmega_head h hB pO hpl) e₂ he₂ (congrArg (·.1) k2) (congrArg (·.2) k2) (fun t' ht => ?_)
    s next rest _ T FP.hk hk' (fun w fr mem mem' hh => rowsMu_many _ s w fr mem mem' hh) hfit
  have e := congrArg (·[t']?) t4
  simp only [List.getElem?_map, List.getElem?_take, if_pos ht] at e
  obtain ⟨a, ha⟩ : ∃ a, (ProofFile.Honest.carryE Bk ⟨(jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.place, 0⟩)[t']? = some a :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  rw [ha, Option.map_some] at e
  obtain ⟨a', ha', k3⟩ := Option.map_eq_some_iff.1 e.symm
  exact ⟨a, a', ha, ha', (congrArg (·.1) k3).symm, (congrArg (·.2.1) k3).symm,
    (congrArg (·.2.2) k3).symm⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.firstTies_at_run
#print axioms ProofFile.Honest.K12.Light.onOmega_at_maker
