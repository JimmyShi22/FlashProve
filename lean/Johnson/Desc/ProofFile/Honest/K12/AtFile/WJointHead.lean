-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WJointHead.lean: the public facts of Omega's member
(OmegaAtW, WJointTaken.lean) at the job at the last chain's proximity test, from the closed test of
WJointFit.lean, and under the head.

  clear_of             a test that two blocks do not overlap, read
  omegaFits_plan, omegaFits_head   the test reads the codes and the shape alone; under the head it
                       accepts at the shared chain's own plan
  omegaAtW_of_test     OmegaAtW at jobW, at the written sendings and stages
  omegaAtW_head        OmegaAtW at the job that jobRealW returns, under the head at its ground

By what. omegaFitsW (WJointFit.lean); stages_at_head, written_at_head, qAt_written; msg_w_head,
parW_written, eG_atAll.

Limits. At the head's ground. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WJointTaken
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WJointFit
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfW
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsAtW
import Johnson.Desc.ProofFile.Honest.K12.StagesAtHead
import Johnson.Desc.ProofFile.Honest.K12.FitAtHead
import Johnson.Desc.ProofFile.Honest.K14.AtFilling

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Chain Block FileDescription)
open VerifiableInference.Desc.K1 (parGF parWF)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open ProofFile.Honest.K12.Light (OmegaAtW ManyJob Mem)
open ProofFile.Honest.K14 (SendPub jobOmega)
open H2K.Member (piWFull)
open Johnson.G (codesFull2)


/-- What clearB says. -/
theorem clear_of (a b : ProofFile.Honest.K12.Light.MemShape) (h : clearB a b = true) :
    ∀ r < b.mainRows, ¬ (a.mainFirst ≤ b.mainFirst + r ∧
      b.mainFirst + r < a.mainFirst + a.mainRows) := by
  intro r hr ⟨h1, h2⟩
  unfold clearB at h
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  omega

/-- The test reads the codes and the shape alone. -/
theorem omegaFits_plan (A : SendPub) :
    omegaFitsB A = omegaFitsB (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S) := rfl

section
variable {W X : Type}

/-- **OmegaAtW at jobW.** -/
theorem omegaAtW_of_test {Xi : Type} (q : VerifiableInference.Desc.K12.P12)
    (door : W → Front X → VerifiableInference.Desc.K12.T12) (JI : K1.SendJob Readers X)
    (JW : K1.SendJob (K1.PlaceIn Xi) X) (A : SendPub) (readers : W → Readers)
    (wit : W → K1.PlaceIn Xi) (ask : W → ProofFile.Honest.K14.Ask) (n₁ : ℕ)
    (hPI : JI.P = parGF) (hPW : JW.P = parWF) (hst : q.nums.stages = piWFull.nums.stages)
    (hd : ProofFile.Honest.K12.Light.depthOf q 2 = 22) (k : omegaFitsB A = true) :
    ∃ mA mB fs, OmegaAtW (jobW q door JI JW A readers wit ask n₁) mA mB A (n₁ + A.atPoint) fs ask := by
  obtain ⟨PI, f₁, r₁, d₁⟩ := JI
  obtain ⟨PW, f₂, r₂, d₂⟩ := JW
  obtain rfl : PI = parGF := hPI
  obtain rfl : PW = parWF := hPW
  have es : (jobW q door ⟨parGF, f₁, r₁, d₁⟩ ⟨parWF, f₂, r₂, d₂⟩ A readers wit ask n₁).s₀ =
      piWFull.nums.stages.headD default := by
    show q.nums.stages.headD default = _
    rw [hst]
  unfold omegaFitsB at k
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at k
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩ := k
  refine ⟨_, _, _, ⟨rfl, ?_, ?_, ?_, a3, ?_, clear_of _ _ a5, clear_of _ _ a6, a7, a8, a9⟩⟩
  · show (some (ProofFile.Honest.K12.Light.depthOf q 2, [ProofFile.Honest.K12.Light.Piece.main 2]) :
      Option (ℕ × List ProofFile.Honest.K12.Light.Piece)) = _
    rw [hd]
  · rw [es]
    exact a1
  · rw [es]
    exact a2
  · rw [es]
    exact a4

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The test accepts at the shared chain's own plan, under the head.** -/
theorem omegaFits_head (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) (a : ℕ) :
    omegaFitsB ⟨VerifiableInference.Desc.K1.qAt Zp Np, a⟩ = true := by
  obtain ⟨y, hy, Wr⟩ := ProofFile.Honest.K12.Light.written_at_head h
  have k := omegaFitsW
  rw [hy] at k
  have k' : omegaFitsB (ProofFile.Honest.K12.Light.planOf codesFull2 y.shape) = true := k
  rw [omegaFits_plan, ProofFile.Honest.K12.Light.qAt_written Wr Np]
  exact k'

variable (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x) {Bs : ProofFile.PureBase}
  {base : List (Block P5J.TS ProofFile.Cl)}
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
    (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
include h O

/-- **OmegaAtW at the job that jobRealW returns at the head's ground.** -/
theorem omegaAtW_head {W₀ Rc Xi Tr X : Type} (S : OnBytes.HonestTrace.Sz) (Fd : FileDescription Xi)
    (enter : Fd.S₃ → Except String VerifiableInference.Desc.K12.T12)
    (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf Xi) (no : VerifiableInference.Desc.Place → ℕ)
    (readers : ProofFile.Honest.Local W₀ Rc Xi Tr → Readers)
    (weights : ProofFile.Honest.Local W₀ Rc Xi Tr → ProofFile.Honest.Weights)
    (rand : Desc.K14.P14 → ProofFile.Honest.Local W₀ Rc Xi Tr → ProofFile.Honest.TableRand)
    {M : ManyJob (ProofFile.Honest.Local W₀ Rc Xi Tr) X}
    (hM : jobRealW S Fd enter pile no readers weights rand Zp Bs.G₀ = some M) :
    ∃ mA mB An fs, sendPub Zp = some An ∧ An.P = VerifiableInference.Desc.K1.qAt Zp Np ∧
      OmegaAtW M mA mB An
      ((Fd.first.blocksInOrder.flatMap (·.rounds)).length + An.atPoint) fs
      (ProofFile.Honest.K12.Light.askOf An weights (rand An.P)) := by
  unfold jobRealW at hM
  obtain ⟨F, hF, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨A, hA, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨msg, hmsg, rfl⟩ := Option.map_eq_some_iff.1 hM
  obtain ⟨hf, -, -, hW, -⟩ := ProofFile.Honest.K12.Light.stages_at_head h.toAtMg
  obtain rfl : F = fourOf Np := Option.some.inj (hF.symm.trans hf)
  obtain rfl : msg = wMsgFull := Option.some.inj (hmsg.symm.trans (ProofFile.Honest.K1.msg_w_head h O))
  have eA : A.P = VerifiableInference.Desc.K1.qAt Zp Np := by
    have hA' := hA
    unfold sendPub at hA'
    rw [(ProofFile.Honest.K14.readers_at Zp Np h.laid.places).1] at hA'
    change Option.map _ _ = some A at hA'
    obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.1 hA'
    rfl
  have hd : ProofFile.Honest.K12.Light.depthOf (fourOf Np).W 2 = 22 := by
    unfold ProofFile.Honest.K12.Light.depthOf
    rw [ProofFile.Honest.K12.Light.nums_head_W h.toAtMg]
    rfl
  have k : omegaFitsB A = true := by
    have e := omegaFits_head h.toAtMg A.atPoint
    rw [← eA] at e
    exact e
  obtain ⟨mA, mB, fs, P⟩ := omegaAtW_of_test (fourOf Np).W
    (ProofFile.Honest.K12.Light.doorW Fd (·.x) enter placeW idleT12)
    (K1.firstJob S Zp Bs.G₀)
    (K1.wJobAt Zp.first (K1.wGp Zp) 4 wMsgFull (no ⟨1, none, 4, .K1⟩) (K13.wDataAt pile Zp Bs.G₀))
    A readers (inOf readers)
    (ProofFile.Honest.K12.Light.askOf A weights (rand A.P)) (Fd.first.blocksInOrder.flatMap (·.rounds)).length
    (VerifiableInference.Desc.K1.eG_atAll h O (VerifiableInference.Desc.K1.pin1_atAll h))
    (ProofFile.Honest.K1.parW_written h O) hW hd k
  exact ⟨mA, mB, A, fs, hA, eA, P⟩

end

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.clear_of
#print axioms ProofFile.Honest.K12.AtProof.omegaFits_plan
#print axioms ProofFile.Honest.K12.AtProof.omegaAtW_of_test
#print axioms ProofFile.Honest.K12.AtProof.omegaFits_head
#print axioms ProofFile.Honest.K12.AtProof.omegaAtW_head
