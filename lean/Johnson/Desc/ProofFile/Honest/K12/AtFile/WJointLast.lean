-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WJointLast.lean: NOT IN FRONT OF A LAW OVER COINS. The clause
taken of StandRest (WTable.lean) under the head, at the job that jobRealW returns at the head's ground.

  taken_at_job         at any thread of the chain whose table at .taken 1 1 is the sending's
  taken_at_lastAt      at lastAt

Premises left, each named. FirstArms: the first chain's house. hO, hf, hask: the shared thread's table,
the count that fixes it, and that the job's rows are the thread's witness's.

By what. taken_of_arms (WJointArms.lean), omegaAtW_head (WJointHead.lean), omega_due_head,
omega_cover_head, omega_depth_head (WJointBook.lean), omega_row_at_head
(AtFullSide/K12/LettersAtHead.lean), job_facts (WFilling.lean).

Limits. At the head's ground. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WJointArms
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WJointHead
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WJointBook
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.AtProof (fourOf placeW senderO sendPub jobRealW p12At_place)
open VerifiableInference.Desc (Block Chain Place FileDescription)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.Third (S₃)
open ProofFile.Honest.K12.Light (ManyJob askOf)
open ProofFile.Honest.K14 (jobOmega sendTable Ask)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open P5J (F0T AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block P5J.TS ProofFile.Cl)} {Bk : ProverCoinCounts}

/-- **The clause taken, at any thread of the chain**, under the head. -/
theorem taken_at_job {S Cl V Pb W₀ Rc Xi Tr X W₂ : Type}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk)
    (Sz : OnBytes.HonestTrace.Sz) (Fd : FileDescription Xi) (enter : Fd.S₃ → Except String T12)
    (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf Xi) (no : Place → ℕ)
    (readers : Local W₀ Rc Xi Tr → Readers) (weights : Local W₀ Rc Xi Tr → Weights)
    (rand : Desc.K14.P14 → Local W₀ Rc Xi Tr → TableRand) {M : ManyJob (Local W₀ Rc Xi Tr) X}
    (hM : jobRealW Sz Fd enter pile no readers weights rand Zp Bs.G₀ = some M)
    (T : Thread Bk S Cl V (Local W₀ Rc Xi Tr) X Pb)
    (Said : ℕ → Coins Bk → ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) X → Prop)
    (first : FirstArms T Said M) (witO : W₂ → Ask) (toCommon : Local W₀ Rc Xi Tr → W₂) (r₁ f : ℕ)
    (hch : T.chain = 2) (hr₁ : r₁ = (Fd.first.blocksInOrder.flatMap (·.rounds)).length)
    (hO : ∀ An, sendPub Zp = some An → T.table (.taken 1 1) = fun k w d =>
      sendTable (jobOmega An) witO senderO.place 1 0 k (toCommon w) (d.drop r₁))
    (hfix : T.fixed (.taken 1 1) = r₁ + f)
    (hf : ∀ An, sendPub Zp = some An → An.atPoint + 1 ≤ f)
    (hask : ∀ An, sendPub Zp = some An → ∀ w,
      (askOf An weights (rand An.P) w).rows = (witO (toCommon w)).rows) :
    ∀ k st m E (c : RowCoins [(firstPart M.toRun.toTest : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X), restPart M.toRun.toTest]),
      ThrS T Said 2 k st m E →
      lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) M.p.place
        [(firstPart M.toRun.toTest : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X), restPart M.toRun.toTest] 0 = .ok c →
      ∀ i (hi : i < takenLast.length), TakenIs T k m
        (M.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins M.toRun.toTest c.2.1).mem
          (M.toRun.toTest.first m.st.input (frontOf m) (restCoins M.toRun.toTest c.2.1)))
        i takenLast[i] := by
  obtain ⟨mA, mB, An, fs, hAn, hP, Pu⟩ :=
    ProofFile.Honest.K12.AtProof.omegaAtW_head h O Sz Fd enter pile no readers weights rand hM
  have hpl : M.p.place = placeW := by
    rw [(job_facts h.toAtMg Sz Fd enter pile no readers weights rand Bs.G₀ hM).1]
    exact p12At_place _ _
  subst hr₁
  exact taken_of_arms hB T M mA mB An _ _ f fs _ witO toCommon Pu rfl hch hpl
    (AtFullSide.K12.omega_row_at_head h hAn _) (hO An hAn) hfix (hf An hAn) (hask An hAn)
    (omega_due_head h.toAtMg hP) (omega_cover_head h.toAtMg hB hP)
    (omega_depth_head h.toAtMg hB hP witO) Said first

section
variable {W₀ Rc Tr X₀ X Wt W₂ : Type}
  (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : VerifiableInference.Desc.Shared.NumbersS)
  (Mg : Local W₀ Rc ProofFile.Inst Tr →
    VerifiableInference.Desc.Shared.MeaningS Desc.K14.St (ProofFile.InstPub × P5J.TS) Wt)
  (ML : VerifiableInference.Desc.Last.MeaningL S₃ Wt)
  (PL : VerifiableInference.Desc.Last.PromMeaningL Desc.K14.St S₃ (ProofFile.InstPub × P5J.TS))
  (order : S₃ → Prop)
  (ends : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
    (ProofFile.InstPub × P5J.TS) × Desc.K14.St)
  (wit : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Wt)
  (r₁ n₀ : ℕ) (toCommon : Local W₀ Rc ProofFile.Inst Tr → W₂)
  (tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Place × Table)
  (tb₂ : Fmt.TreeSource → Coins Bk → W₂ → List Fmt.Drawn → Place × Table)
  (fx₁ fx₂ : Fmt.TreeSource → ℕ)
  (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) X) (own₀ : X)
  (item n₁ n₂ : ℕ) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : ℕ → Local W₀ Rc ProofFile.Inst Tr → S₃ → Prop) (Kp : Place → S₃ → S₃ → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The clause taken at lastAt.** -/
theorem taken_at_lastAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk)
    (Sz : OnBytes.HonestTrace.Sz) (Fd : FileDescription ProofFile.Inst) (enter : Fd.S₃ → Except String T12)
    (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf ProofFile.Inst) (no : Place → ℕ)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (weights : Local W₀ Rc ProofFile.Inst Tr → Weights)
    (rand : Desc.K14.P14 → Local W₀ Rc ProofFile.Inst Tr → TableRand)
    {M : ManyJob (Local W₀ Rc ProofFile.Inst Tr) X}
    (hM : jobRealW Sz Fd enter pile no readers weights rand Zp Bs.G₀ = some M)
    (Said : ℕ → Coins Bk → ProofFile.Honest.Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (first : FirstArms (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀
      toCommon tb₁ tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w) Said M)
    (witO : W₂ → Ask) (hr₁ : r₁ = (Fd.first.blocksInOrder.flatMap (·.rounds)).length)
    (hO : ∀ An, sendPub Zp = some An →
      tb₂ (.own 1) = sendTable (jobOmega An) witO senderO.place 1 0)
    (hf : ∀ An, sendPub Zp = some An → An.atPoint + 1 ≤ fx₂ (.own 1))
    (hask : ∀ An, sendPub Zp = some An → ∀ v,
      (askOf An weights (rand An.P) v).rows = (witO (toCommon v)).rows) :
    ∀ k st m E (c : RowCoins [(firstPart M.toRun.toTest : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X), restPart M.toRun.toTest]),
      ThrS (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀ toCommon tb₁
        tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w) Said 2 k st m E →
      lendRow Bk (Bk.rowsOf (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁
          n₀ toCommon tb₁ tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w).chain)
        (k.look (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀ toCommon
          tb₁ tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w).chain) M.p.place
        [(firstPart M.toRun.toTest : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X), restPart M.toRun.toTest] 0 = .ok c →
      ∀ i (hi : i < takenLast.length), TakenIs (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL
          order ends wit r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w) k m
        (M.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins M.toRun.toTest c.2.1).mem
          (M.toRun.toTest.first m.st.input (frontOf m) (restCoins M.toRun.toTest c.2.1)))
        i takenLast[i] :=
  taken_at_job h O hB Sz Fd enter pile no readers weights rand hM _ Said first witO toCommon r₁
    (fx₂ (.own 1)) rfl hr₁
    (fun An hAn => by
      show (fun (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst Tr) (d : List Fmt.Drawn) =>
        tb₂ (.own 1) k (toCommon v) (d.drop r₁)) = _
      rw [hO An hAn]) rfl hf hask

end

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.taken_at_job
#print axioms ProofFile.Honest.K12.AtFile.taken_at_lastAt
