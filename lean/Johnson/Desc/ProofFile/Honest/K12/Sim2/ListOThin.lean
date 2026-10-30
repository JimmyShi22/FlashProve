-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the list of the test on G_omega at a run, what is left thinned to SaysAt.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/ListOThin.lean: CONDITIONAL.

Can the hypotheses be met together at a real run? NOT KNOWN, as at Sim2/ListO.lean's head.

What is here. `onAtRun_O` (Sim2/ListO.lean) with hleft cut to SaysAt: ShapeAsksO has no premise on values at a
run, and DataAsks follows from SaysAt: `onAsks_head_O` (SimO/AsksOmega.lean), at the heard challenges padded by
the block's own stretch of the due list.

  `cut_mid`, `tail_at_stand`, `asks_of_says`   private; copied from
      AtFullSide/K12/Sim/OmegaSays.lean [not in this library] (namespace ProofFile.Honest.Term), which
      imports the term's files.
  `LeftSaysO`   hleft: SaysAt at every called stand of the second part, under all the rule's hypotheses.
  `onAtRun_O_thin`   **the statement**.

SaysAt at a run: Sim2/SaysAtRunO.lean. Limits: those of Sim2/ListO.lean. «True of the fall-back too if SaysAt
holds there» (SimO/AsksOmega.lean's head); at a called part the door's own fold returned:
`door_of_called_at_O`. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListO
import Johnson.Desc.ProofFile.Honest.K12.SimO.AsksOmega

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Chain K1.qAt foldBlocks)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St blocks)
open H2K.Member (codesFull)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof

private theorem cut_mid {α : Type} (A B C : List α) (f : ℕ) (hf : f ≤ B.length) :
    ((A ++ (B ++ C)).drop (A.length + f)).take (B.length - f) = B.drop f := by
  induction A with
  | nil =>
    rw [List.nil_append, List.length_nil, Nat.zero_add, List.drop_append_of_le_length hf]
    exact List.take_left' (by rw [List.length_drop])
  | cons a A ih =>
    rw [List.cons_append, List.length_cons, show A.length + 1 + f = (A.length + f) + 1 by omega, List.drop_succ_cons]
    exact ih


/-- **Challenges that fit the second part's rounds, at a stand.** Copied from ProofFile.Honest.Term. -/
private theorem tail_at_stand {Xi : Type} (F : VerifiableInference.Desc.FileDescription Xi) (ρ : Draws)
    (pre t : List (Block F.S₂ F.Cl)) (b : Block F.S₂ F.Cl) (hcut : F.shared.blocksInOrder = pre ++ b :: t)
    (hdue : drawsFit F.roundsDeclaredByBlocks.2.1 ρ.shared = true) (f : ℕ) (hf : f ≤ b.rounds.length) :
    ∃ tl, drawsFit (b.rounds.drop f) tl = true := by
  have hD := ProofFile.Honest.K3.Law.drawsFit_take _ _ (b.rounds.length - f)
    (ProofFile.Honest.K3.Law.drawsFit_drop _ _ ((pre.flatMap (·.rounds)).length + f) hdue)
  have e : ((F.roundsDeclaredByBlocks.2.1).drop ((pre.flatMap (·.rounds)).length + f)).take (b.rounds.length - f) = b.rounds.drop f := by
    show ((F.shared.blocksInOrder.flatMap (·.rounds)).drop _).take _ = _
    rw [hcut, List.flatMap_append, List.flatMap_cons]
    exact cut_mid _ _ _ f hf
  rw [e] at hD
  exact ⟨_, hD⟩


/-- **The clause at the heard challenges.** Copied from ProofFile.Honest.Term. -/
private theorem asks_of_says {W₀ : Type} {o : ProofFile.SecondHashFunctionArgument} {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} (h : P5J.AtMg o files D r₀ Zp Np cF) {pO : P12}
    (hO : (fourOf Np).O = some pO) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) (wt : W₀ → Weights)
    (m : Mid (Common W₀ IndexCommitterCoins TableKey) Unit) (fr : Front Unit) (C : TestCoins)
    (hfit : drawsFit (((H2K.JointK.laidOf (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p).take (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages)).map (·.1))
      (m.st.lately (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages)) = true)
    (tl : List Fmt.Drawn)
    (htl : drawsFit (((H2K.JointK.laidOf (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p).drop (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages)).map (·.1)) tl = true)
    :
    ∃ Dp : H2K.First.Plain, Dp.ts.length = firstListAtOmega.length ∧
      ProofFile.Honest.K12.Own.ShapeAsksO (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) m.st.input fr C (heardIn (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) m) H2K.Member.codesFull Dp ∧
      (SaysAt (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO (doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) [b1, b2, b3, b4, b5, b6, b7, b8] (fourOf Np).U (fun w : Common W₀ IndexCommitterCoins TableKey => w.key) colsOpened) (fun w => wt w.w₀) (fun w => ProofFile.Honest.K12.AtProof.randAt (K1.qAt Zp Np) w.rc) none) m.st.input fr C → ∃ (cc : ℕ → ℕ → List UInt64) (Rw : ProofFile.Honest.K12.PlainRows),
        DataAsks (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) m.st.input fr C (heardIn (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) m) Dp cc Rw) := by
  obtain ⟨s, next, nx', rest', hlit⟩ : ∃ s next nx' rest', H2K.Member.piOFull.nums.stages = s :: next :: nx' :: rest' :=
    ⟨_, _, _, _, rfl⟩
  have hst : (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages = s :: next :: nx' :: rest' := by
    show pO.nums.stages = _
    rw [ProofFile.Honest.K12.Light.nums_head_O h hO, hlit]
  have F₁ : FirstPubOwn (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) :=
    firstPubOwn_head h hO _ _ _ none _ rfl rfl
  have hall : drawsFit ((H2K.JointK.laidOf (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p).map (·.1)) (m.st.lately (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages) ++ tl) = true := by
    have e : (H2K.JointK.laidOf (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p).map (·.1) = ((H2K.JointK.laidOf (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p).take (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages)).map (·.1) ++
        ((H2K.JointK.laidOf (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p).drop (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages)).map (·.1) := by
      rw [← List.map_append, List.take_append_drop]
    rw [e]
    exact ProofFile.Honest.K12.drawsFit_append _ _ _ _ hfit htl
  have hd : drawsFit (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).rounds (m.st.lately (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages) ++ tl) = true := by
    rw [← ProofFile.Honest.K12.AtFile.laid_head_O h hO]
    exact hall
  obtain ⟨Dp, hts, Sh, hDt⟩ := ProofFile.Honest.K12.AtFile.onAsks_head_O h hO [b1, b2, b3, b4, b5, b6, b7, b8] hb
    (fun w : Common W₀ IndexCommitterCoins TableKey => w.key) colsOpened (fun w => wt w.w₀)
    (fun w => ProofFile.Honest.K12.AtProof.randAt (K1.qAt Zp Np) w.rc) none m.st.input fr C _ hd
  have hlat : (m.st.lately (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages)).length = firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages := by
    have h1 := drawsFit_length _ _ hfit
    rw [h1, List.length_map, List.length_take]
    exact Nat.min_eq_left F₁.enough
  have FP := formPub_of_B (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p s next (nx' :: rest') hst F₁.form
  have hk : s.k = (H2K.Pub.sgOf s).h + (H2K.Pub.sgOf s).g := by
    have := FP.hk
    show s.k = s.h + (s.k - s.h)
    omega
  have hA : stA (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p = s := by
    unfold stA
    rw [hst]
    rfl
  have hn : firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages = 2 + s.k := by
    rw [hst]
    rfl
  have hfront : ∀ n, n < 1 + (1 + ((H2K.Pub.sgOf (stA (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p)).h + (H2K.Pub.sgOf (stA (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p)).g)) →
      byNo (m.st.lately (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages) ++ tl) n = heardIn (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) m n := by
    intro n hn'
    rw [hA] at hn'
    unfold byNo heardIn
    rw [List.getD_append _ _ _ _ (by rw [hlat, hn, hk]; omega)]
    rfl
  refine ⟨Dp, hts, ?_, fun hs => ?_⟩
  · rw [ProofFile.Honest.K12.Light.codes_two]
    exact shapeAsksO_congr (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) _ _ _ _ _ hfront Sh
  · obtain ⟨cc, Rw, Dt⟩ := hDt hs
    exact ⟨cc, Rw, dataAsks_congr (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) _ _ _ _ _ hfront Dt⟩


/-- **hleft, thin**: SaysAt at every called stand of the second part, under all the rule's hypotheses. -/
def LeftSaysO {o : ProofFile.SecondHashFunctionArgument} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {W₀ Tr Y : Type} {Bk : ProverCoinCounts} {H : Prover W₀ IndexCommitterCoins ProofFile.Inst TableKey Tr Unit Y}
    {G : Sides (P5J.F0T o Zp Np cF) Bk W₀ IndexCommitterCoins TableKey Tr Unit Y} {w₀ : W₀} {rc : IndexCommitterCoins}
    {x : ProofFile.Inst} {k : Coins Bk} {R : Ready W₀ IndexCommitterCoins ProofFile.Inst TableKey Tr Unit Y}
    (T : ThreadsP (P5J.F0T o Zp Np cF) Bk (G.prover H) w₀ rc x k R) (ρ : Draws)
    (r : RunC (P5J.F0T o Zp Np cF))
    (L : Lettered Bk St ProofFile.Cl Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey)
    (A : ManyJob (Common W₀ IndexCommitterCoins TableKey) Unit) (J : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit) : Prop :=
  ∀ (m : Mid (Common W₀ IndexCommitterCoins TableKey) Unit)
      (ca : CsAll (restPart J :
        Part Empty (Common W₀ IndexCommitterCoins TableKey) Unit).needsField.carries)
      (σ : Side St ProofFile.Cl Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey)
      (pre' t' : List (Block St ProofFile.Cl)), L.side (P5J.F0T o Zp Np cF).shared.blocksInOrder = some σ →
      (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre' ++ σ.block :: t' →
      InsideOf .shared Bk 1 (G.prover H).shared σ.block (T.I₂ pre'.length) (σ.roundsTo 1) k m
        (envOf (H.storedWords w₀ rc) (fun _ _ => none)
          (r.run.played.2.1.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1))) →
      m.seen = roundsOf (r.run.played.2.1.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1)) →
      r.called ⟨L.place, 1⟩ = true →
      carriedAt Bk k 1 ⟨L.place, 1⟩
        (restPart J :
          Part Empty (Common W₀ IndexCommitterCoins TableKey) Unit).needsField = .ok ca →
      midSharedAtW (P5J.F0T o Zp Np cF) Bk (G.prover H) w₀ rc x k ρ ⟨L.place, 1⟩ = .ok (some m) →
      (laidOf (P5J.F0T o Zp Np cF) ρ []
          (r.run.played.2.1.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1)) []).front 1
          (storedShown (H.storedWords w₀ rc) (storedAsks (P5J.F0T o Zp Np cF) ρ)) =
        r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨L.place, 1⟩ →
      SaysAt A m.st.input (restFront J m) (carriedCoins J (stretches _ ca))


/-- CONDITIONAL. **THE CLAUSE OF THE RULE AT THE LIST OF THE TEST ON G_omega, FROM SaysAt ALONE.** -/
theorem onAtRun_O_thin {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {pO : P12}
    (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) (hO : (fourOf Np).O = some pO)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) Johnson.G.proofSendsFull.1 Johnson.G.proofSendsFull.2.1
      Johnson.G.proofSendsFull.2.2 (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    {W₀ Tr Y : Type} {H : Prover W₀ IndexCommitterCoins ProofFile.Inst TableKey Tr Unit Y}
    {G : Sides (P5J.F0T o Zp Np cF) Bk W₀ IndexCommitterCoins TableKey Tr Unit Y}
    (hα : ∀ x, (G.prover H).key x = x.pub.key) {w₀ : W₀} {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ IndexCommitterCoins ProofFile.Inst TableKey Tr Unit Y}
    {r : RunC (P5J.F0T o Zp Np cF)}
    (T : ThreadsP (P5J.F0T o Zp Np cF) Bk (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (P5J.F0T o Zp Np cF) = true)
    (hR : ready (P5J.F0T o Zp Np cF) Bk (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk (G.prover H) w₀ rc x k ρ = .ok r)
    (wt : W₀ → Weights)
    (L : Lettered Bk St ProofFile.Cl Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey)
    (hL : IsListAtO L (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO)
      (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO
        [b1, b2, b3, b4, b5, b6, b7, b8]))
    (hg : ((G.prover H).shared.find? fun g => g.place == pO.place) =
      some (proverSideOfProximityTest (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) :
        Placed Empty _ _).needsField)
    (hgO : ((G.prover H).shared.find? fun g => g.place == K14.sendPlace 5) =
      some ⟨K14.sendPlace 5,
      [(K14.liftSend (askOf ⟨K1.qAt Zp Np, 0⟩ (fun w : Common W₀ IndexCommitterCoins TableKey => wt w.w₀)
          (fun w => randAt (K1.qAt Zp Np) w.rc))
          (K14.sendingPart (K14.jobOmega ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ IndexCommitterCoins TableKey) Unit)]⟩)
    (hleft : LeftSaysO T ρ r L (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO
      (doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) [b1, b2, b3, b4, b5, b6, b7, b8] (fourOf Np).U
        (fun w : Common W₀ IndexCommitterCoins TableKey => w.key) colsOpened) (fun w => wt w.w₀)
      (fun w => randAt (K1.qAt Zp Np) w.rc) none) (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO)) :
    OnAtRun₂ T ρ r L := by
  refine onAtRun_O h hO b1 b2 b3 b4 b5 b6 b7 b8 hb hB hα T hρ hR hrun wt L hL hg hgO ?_
  intro m ca σ pre' t' hσ hcut hin hs hc hca hmid hfr
  have hpl : σ.block.place = L.place := side_place hσ
  have hσ' : Side.seated (P5J.F0T o Zp Np cF).shared.blocksInOrder pO.place
      (omegaRow (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8])) [] = some σ := by
    have e := hσ
    unfold Lettered.side at e
    rw [hL.place, hL.row] at e
    exact e
  obtain ⟨-, -, -, -, hp, hr, -⟩ := side_omega h hO _ _ _ none _ rfl rfl [] σ hσ'
  have hpO : σ.block.place = pO.place := hp
  have hdue : drawsFit (P5J.F0T o Zp Np cF).roundsDeclaredByBlocks.2.1 ρ.shared = true := (fits_of hρ).2.1
  have hg' : ((G.prover H).shared.find? fun g => g.place == σ.block.place) =
      some (proverSideOfProximityTest (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) : Placed Empty _ _).needsField := by
    rw [hpO]
    exact hg
  have hc' : r.called ⟨σ.block.place, 1⟩ = true := by
    rw [hpl]
    exact hc
  obtain ⟨c, m₁, g1, g2, g3, hf3, g4⟩ := onOmega_at_side h hO b1 b2 b3 b4 b5 b6 b7 b8 hb hB hα wt hR []
    σ hσ' hrun hc' hg' hgO hdue
  have hmid' : midSharedAtW (P5J.F0T o Zp Np cF) Bk (G.prover H) w₀ rc x k ρ ⟨σ.block.place, 1⟩ =
      .ok (some m) := by
    rw [hpl]
    exact hmid
  obtain rfl : m₁ = m := Option.some.inj (Except.ok.inj (g1.symm.trans hmid'))
  have hlaidR : (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).rounds = (H2K.JointK.laidOf pO).map (·.1) :=
    (ProofFile.Honest.K12.AtFile.laid_head_O h hO).symm
  have F₁ : FirstPubOwn (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) (simulatorJobAtOmega Zp.p.chains (K1.qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) := firstPubOwn_head h hO _ _ _ none _ rfl rfl
  have hlenF : firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages ≤ σ.block.rounds.length := by
    rw [hr, hlaidR, List.length_map]
    exact F₁.enough
  obtain ⟨tl, htl⟩ := tail_at_stand (P5J.F0T o Zp Np cF) ρ pre' t' σ.block hcut hdue _ hlenF
  have htl' : drawsFit (((H2K.JointK.laidOf (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p).drop
      (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p.nums.stages)).map (·.1)) tl = true := by
    rw [List.map_drop]
    have e3 : (H2K.JointK.laidOf (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO).p).map (·.1) = σ.block.rounds := by
      rw [hr, hlaidR]
      rfl
    rw [e3]
    exact htl
  obtain ⟨Dp, hts, Sh, hD⟩ := asks_of_says h hO b1 b2 b3 b4 b5 b6 b7 b8 hb wt m₁
    (restFront (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) m₁) (carriedCoins (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] wt pO) (stretches _ ca)) hf3 tl htl'
  obtain ⟨cc, Rw, Dt⟩ := hD (hleft m₁ ca σ pre' t' hσ hcut hin hs hc hca hmid hfr)
  exact ⟨Dp, cc, Rw, hts, Sh, Dt⟩

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.onAtRun_O_thin
