-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the request's own test: what the filling's job is, and its public numbers.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/ListWNumbers.lean: CONDITIONAL on the head. Statements with
their
proofs; no definition.

What is here. Under the head, of the job that `jobRealW` (K12/AtProof/HalfW.lean) makes for the
request's own proximity test: what it is, to the letter, at the written plans; its three members'
public shapes; the public numbers of Omega's sending. For Sim2/ListWTreesNumbers.lean.

  `plan_of_sendPub`   the shared sendings' plan off the public part is the head's, at the written
  codes
      and shape.
  `real_job_written`   M = `jobW` at the place's numbers, `doorW`, the first sending's job, W's job
  AT THE
      WRITTEN PLAN AND RIDE, the sendings' public data, the readers. No letter under "there is" but
      the two that the public part fixes (hA, hmsg).
  `first_plan_written`, `first_ride_written`   the first sending's plan and ride are the written
  ones.
  `own_stage_written`   the job's first stage is the written place's.
  `member_shapes_written`   the three members' shapes.
  `omega_numbers_written`   six public facts on Omega's sending.

By. Index privacy's `like_head`, `firstPar_head`, `parW_head`, `wFold_head` (Sim2/JobsAtW.lean) and
`ownP_shapes`, `ownP_O_full` (Sim2/PublicAtW.lean): closed facts by Lean's kernel. The library's
`written_at_head`, `qAt_written` (K12/FitAtHead.lean), `p14At_at_head` (K12/AtProof/AtHandU.lean),
`firstFold_shape` (K1/Law/FitsWritten.lean), `reads_head_W` (K12/Sim/FirstAnyAtHeadW.lean).

Limits. Numbers and terms alone: nothing on a run. The full size and the format's second hash function
alone.
Nothing on completeness, soundness or hiding.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListWAtLot
import Johnson.Desc.ProofFile.Honest.K12.Sim2.JobsAtW
import Johnson.Desc.ProofFile.Honest.K12.AtProof.AtHandU
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.K1 (qFull realSized likeFull_qFull)
open H2K.Member (codesFull piWFull)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open ProofFile.Honest.K14 (jobOmega sendingsFit)
open Johnson.Prover.Send (shapeAt)
open Johnson.G (codesFull2)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- CONDITIONAL on the head and hA. **The shared sendings' plan.** -/
theorem plan_of_sendPub (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {A : K14.SendPub}
    (hA : sendPub Zp = some A) :
    ∃ x, realSized = some (x, codesFull2) ∧ A.P.codes = codesFull2 ∧ A.P.S = x.shape := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  unfold sendPub at hA
  rw [p14At_at_head h] at hA
  obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.1 hA
  refine ⟨x, hx, ?_, ?_⟩
  · show (VerifiableInference.Desc.K1.qAt Zp Np).codes = _
    rw [qAt_written Wr Np]
  · show (VerifiableInference.Desc.K1.qAt Zp Np).S = _
    rw [qAt_written Wr Np]

/-- CONDITIONAL on the head and hGf. The first sending's plan. -/
theorem first_plan_written (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Gr : ProofFile.Ground}
    (hGf : Gr.first = Zp.first) (S' : OnBytes.HonestTrace.Sz) :
    (K1.firstJob (X := Unit) S' Zp Gr).P = PIw := firstPar_head h hGf

/-- CONDITIONAL on the head and hGf. The first sending's fold. -/
theorem first_fold_written (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Gr : ProofFile.Ground}
    (hGf : Gr.first = Zp.first) : K1.firstFold Gr.first = K1.firstFold qFull :=
  K1.firstFold_shape (by rw [hGf]; exact (like_head h).1.shape.trans likeFull_qFull.shape.symm)

/-- CONDITIONAL on the head and hGf. The first sending's ride. -/
theorem first_ride_written (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Gr : ProofFile.Ground}
    (hGf : Gr.first = Zp.first) (S' : OnBytes.HonestTrace.Sz) :
    (K1.firstJob (X := Unit) S' Zp Gr).ride = rideIw := by
  show K1.firstRide Gr.first = _
  rw [K1.firstRide_eq, first_fold_written h hGf]

/-- CONDITIONAL on the head, hM, hA and hmsg. **WHAT THE FILLING's JOB IS**, W's job at the written
plan and ride. -/
theorem real_job_written (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF)
    (S' : OnBytes.HonestTrace.Sz) (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf ProofFile.Inst)
    (no : Place → ℕ) (readers : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Readers) (weights : Local W₀ IndexCommitterCoins
              ProofFile.Inst Cells → Weights)
    (rand : Desc.K14.P14 → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TableRand) (Gr : ProofFile.Ground)
    {M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit}
    (hM : jobRealW S' (P5J.F0T OnBytes.secondHashFunction Zp Np cF) enterOwn pile no readers weights rand Zp Gr
        = some M)
    {A : K14.SendPub} (hA : sendPub Zp = some A) {msg : Array OnBytes.OracleNotice}
    (hmsg : OnBytes.linMessageW Zp.first.lin = some msg) :
    M = jobW (fourOf Np).W (doorW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (·.x) enterOwn placeW idleT12)
        (K1.firstJob S' Zp Gr)
      (K1.placeJob PWw (no ⟨1, none, 4, .K1⟩) (K1.wFold qFull.lin) (K13.wDataAt pile Zp Gr)) A
      readers (inOf readers) (askOf A weights (rand A.P))
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.flatMap (·.rounds)).length := by
  unfold jobRealW at hM
  rw [four_at_head h, hA, hmsg] at hM
  have e := (Option.some.inj hM).symm
  rw [e]
  show jobW _ _ _ (K1.placeJob (VerifiableInference.Desc.K1.parW Zp.first (K1.wGp Zp) 4 msg) _
    (K1.wFold Zp.first.lin) _) _ _ _ _ _ = _
  rw [(parW_head h hmsg).2, wFold_head h]

/-- CONDITIONAL on the head and hp. The job's first stage. -/
theorem own_stage_written (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {W X : Type}
    (M : ManyJob W X) (hp : M.p = (fourOf Np).W) : M.s₀ = ownS := by
  show M.p.nums.stages.headD default = _
  rw [hp, (reads_head_W h).1]

/-- CONDITIONAL on the head, hGf and hA. **The three members' shapes**, at the blocks' first rows
that
`jobW` lays. n: where "LIN point" stands: not read. -/
theorem member_shapes_written (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {A : K14.SendPub}
    (hA : sendPub Zp = some A) (n : ℕ) :
    (shapesW PIw PWw ((jobOmega ⟨A.P, n⟩).Q.sent.getD 0 default).shape).zipIdx.map (fun x =>
      memShape x.1 ((firstsOf (shapesW PIw PWw
        ((jobOmega ⟨A.P, n⟩).Q.sent.getD 0 default).shape)).getD x.2 (none, none))) =
      [⟨0, 0, 0, 1, true⟩, ⟨16, 1, 1, 1, false⟩, ⟨0, 12, 0, 0, false⟩] := by
  obtain ⟨x, hx, hc, hS⟩ := plan_of_sendPub h hA
  have k := ownP_shapes
  rw [hx] at k
  have e : ((jobOmega ⟨A.P, n⟩).Q.sent.getD 0 default).shape =
      ((jobOmega (ProofFile.Honest.K12.Light.planOf codesFull2 x.shape)).Q.sent.getD 0 default).shape :=
          by
    show ((jobOmega (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S)).Q.sent.getD 0 default).shape = _
    rw [hc, hS]
  rw [e]
  have k' : ((shapesW PIw PWw ((jobOmega (ProofFile.Honest.K12.Light.planOf codesFull2
      x.shape)).Q.sent.getD 0 default).shape).zipIdx.map (fun y =>
      memShape y.1 ((firstsOf (shapesW PIw PWw ((jobOmega (ProofFile.Honest.K12.Light.planOf codesFull2
        x.shape)).Q.sent.getD 0 default).shape)).getD y.2 (none, none))) ==
      [⟨0, 0, 0, 1, true⟩, ⟨16, 1, 1, 1, false⟩, ⟨0, 12, 0, 0, false⟩]) = true := k
  exact eq_of_beq k'

/-- CONDITIONAL on the head and hA. **Six public facts on Omega's sending.** -/
theorem omega_numbers_written (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {A : K14.SendPub}
    (hA : sendPub Zp = some A) (n : ℕ) :
    sendingsFit A.P = true ∧ widthFits (jobOmega ⟨A.P, n⟩) 0 = true ∧
      sameCode ((jobOmega ⟨A.P, n⟩).Q.codes.base.getD
        (Light.shapeAt (jobOmega ⟨A.P, n⟩) 0).code default) ownS.C = true ∧
      mineOf (jobOmega ⟨A.P, n⟩) 0 = [0] ∧ (Light.shapeAt (jobOmega ⟨A.P, n⟩) 0).maskRows = 0 ∧
      0 < (K14.takesOf (jobOmega ⟨A.P, n⟩).Q.codes (jobOmega ⟨A.P, n⟩).Q.sent
          (jobOmega ⟨A.P, n⟩).sort).f +
        (K14.takesOf (jobOmega ⟨A.P, n⟩).Q.codes (jobOmega ⟨A.P, n⟩).Q.sent
          (jobOmega ⟨A.P, n⟩).sort).e := by
  obtain ⟨x, hx, hc, hS⟩ := plan_of_sendPub h hA
  have k := ownP_O_full
  rw [hx] at k
  have k' : (sendingsFit (ProofFile.Honest.K12.Light.planOf codesFull2 x.shape).P &&
      widthFits (jobOmega (ProofFile.Honest.K12.Light.planOf codesFull2 x.shape)) 0 &&
      sameCode ((jobOmega (ProofFile.Honest.K12.Light.planOf codesFull2 x.shape)).Q.codes.base.getD
        (Light.shapeAt (jobOmega (ProofFile.Honest.K12.Light.planOf codesFull2 x.shape)) 0).code default)
            ownS.C &&
      (mineOf (jobOmega (ProofFile.Honest.K12.Light.planOf codesFull2 x.shape)) 0 == [0]) &&
      ((Light.shapeAt (jobOmega (ProofFile.Honest.K12.Light.planOf codesFull2 x.shape)) 0).maskRows == 0)
          &&
      decide (0 < (K14.takesOf (jobOmega (ProofFile.Honest.K12.Light.planOf codesFull2 x.shape)).Q.codes
          (jobOmega (ProofFile.Honest.K12.Light.planOf codesFull2 x.shape)).Q.sent
          (jobOmega (ProofFile.Honest.K12.Light.planOf codesFull2 x.shape)).sort).f +
        (K14.takesOf (jobOmega (ProofFile.Honest.K12.Light.planOf codesFull2 x.shape)).Q.codes
          (jobOmega (ProofFile.Honest.K12.Light.planOf codesFull2 x.shape)).Q.sent
          (jobOmega (ProofFile.Honest.K12.Light.planOf codesFull2 x.shape)).sort).e)) = true := k
  rw [← hc, ← hS] at k'
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at k'
  obtain ⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩ := k'
  exact ⟨k1, k2, k3, k4, k5, k6⟩

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.plan_of_sendPub
#print axioms ProofFile.Honest.K12.Sim2.first_plan_written
#print axioms ProofFile.Honest.K12.Sim2.first_ride_written
#print axioms ProofFile.Honest.K12.Sim2.real_job_written
#print axioms ProofFile.Honest.K12.Sim2.own_stage_written
#print axioms ProofFile.Honest.K12.Sim2.member_shapes_written
#print axioms ProofFile.Honest.K12.Sim2.omega_numbers_written
