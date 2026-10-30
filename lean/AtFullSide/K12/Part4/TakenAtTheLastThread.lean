-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/Part4/TakenAtTheLastThread.lean: THE LAST CHAIN's PROXIMITY TEST (the kind K12, the
place W): AT THE LAST CHAIN's THREAD AS ITS AUTHORS LAY IT OVER THE TWO EARLIER THREADS' TABLES
(lastAt, K12/AtFile/WTable.lean), UNDER THE LIBRARY's HYPOTHESIS ON THE FIRST CHAIN AND AT THE
MAKER's WRITTEN BOOK: FirstArms; AND SO THE CLAUSE "taken" OF WHAT A STAND OF THE TEST OWES, AT ALL
THREE TREES, WITH NO PREMISE LEFT ON THE FIRST CHAIN's TWO TREES BUT WHAT THE FIRST THREAD's TABLES
ARE.

WHAT IT IS NOT.
  * IT IS CONDITIONAL ON THE TWO EARLIER THREADS' TABLES. tableIndex, tableW, fixedW: the first
    thread's tables of its own trees 1 and 82 are the tables of the first opening's job and of W's
    sending's job, and the second is fixed by the rounds in front of member number 356 (another
    author's arm_two and arm_w, AtFullSide/K12/FirstArmsTables.lean, have these at the first chain's
    Script; they are not called here). In takenAtLastAt also the premises of another author's
    taken_at_lastAt on the shared thread's table (tableOmega, fixedOmega, rowsOmega, rounds).
  * hB, the hypothesis, its opening O and "jobRealW returns a job" at the opening's ground are
    premises.
  * One clause of the four that a stand of this test still owes at the tables (StandRest: field,
    taken, ends, saysAt). It does not say that a stand is reached, that a part plays or that a
    verifier accepts. No count moves by it.
  * In the side library.
  * Nothing on completeness, soundness or what a proof hides.

WHAT IT IS. No definition; two theorems.

  firstArmsAtLastAt   FirstArms at lastAt
  takenAtLastAt       **the clause taken at lastAt**, at the three trees

CALLED. firstArmsUnderTheHead (FirstArmsUnderTheHead.lean). Of another author: taken_at_lastAt
(K12/AtFile/WJointLast.lean).
-/
import AtFullSide.K12.Part4.FirstArmsUnderTheHead
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WJointLast

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12.Part4
open ProofFile.Honest ProofFile.Honest.K12
open VerifiableInference.Desc (Chain Block FileDescription Place)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open ProofFile.Honest.K12.Light (ManyJob askOf)
open ProofFile.Honest.K12.AtProof (jobRealW inOf senderO sendPub)
open ProofFile.Honest.K12.AtFile (FirstArms TakenIs lastAt takenLast taken_at_lastAt)
open ProofFile.Honest.K14 (jobOmega sendTable Ask)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open P5J (TS)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)} {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X Wt W₂ : Type}
  (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : VerifiableInference.Desc.Shared.NumbersS)
  (Mg : Local W₀ Rc ProofFile.Inst Tr →
    VerifiableInference.Desc.Shared.MeaningS Desc.K14.St (ProofFile.InstPub × TS) Wt)
  (ML : VerifiableInference.Desc.Last.MeaningL S₃ Wt)
  (PL : VerifiableInference.Desc.Last.PromMeaningL Desc.K14.St S₃ (ProofFile.InstPub × TS))
  (order : S₃ → Prop)
  (ends : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
    (ProofFile.InstPub × TS) × Desc.K14.St)
  (wit : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Wt)
  (r₁ n₀ : ℕ) (toCommon : Local W₀ Rc ProofFile.Inst Tr → W₂)
  (tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Place × Table)
  (tb₂ : Fmt.TreeSource → Coins Bk → W₂ → List Fmt.Drawn → Place × Table)
  (fx₁ fx₂ : Fmt.TreeSource → ℕ)
  (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) X) (own₀ : X)
  (item n₁ n₂ : ℕ) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : ℕ → Local W₀ Rc ProofFile.Inst Tr → S₃ → Prop) (Kp : Place → S₃ → S₃ → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **FirstArms at the last chain's thread**, from what the first thread's tables of its own trees 1
and 82 are. sentOwn: what the two sendings' jobs are handed as "own" in the first thread's tables.
-/
theorem firstArmsAtLastAt (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk) (S : OnBytes.HonestTrace.Sz)
    (Fd : FileDescription ProofFile.Inst) (enter : Fd.S₃ → Except String T12)
    (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf ProofFile.Inst) (no : Place → ℕ)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (weights : Local W₀ Rc ProofFile.Inst Tr → Weights)
    (rand : Desc.K14.P14 → Local W₀ Rc ProofFile.Inst Tr → TableRand)
    {M : ManyJob (Local W₀ Rc ProofFile.Inst Tr) X}
    (made : jobRealW S Fd enter pile no readers weights rand Zp Bs.G₀ = some M)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (numberI numberW : ℕ)
    (sentOwn : X)
    (tableIndex : ∀ k v hd, tb₁ (.own 1) k v hd =
      K1.treeTbl 0 (inOf readers)
        (K1.placeJob (X := X) (VerifiableInference.Desc.K1.firstPar Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp)) numberI (K1.firstFold Bs.G₀.first)
          (K1.lotData S Zp Bs.G₀)) sentOwn 1 k v hd)
    (tableW : ∀ k v hd, tb₁ (.own 82) k v hd =
      K1.treeTbl 0 (inOf readers)
        (K1.wJobAt (X := X) Zp.first (K1.wGp Zp) 4 wMsgFull numberW (K13.wDataAt pile Zp Bs.G₀))
        sentOwn 0 k v hd)
    (fixedW : fx₁ (.own 82) = roundsTo cF.blocksInOrder 356) :
    FirstArms (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀ toCommon
      tb₁ tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w) Said M :=
  firstArmsUnderTheHead h O hB S Fd enter pile no readers weights rand made _ Said rfl numberI
    numberW sentOwn tableIndex tableW fixedW

/-- **The clause taken at the last chain's thread, at the three trees.** The last four premises are
those of taken_at_lastAt on the shared thread's table. -/
theorem takenAtLastAt (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk) (S : OnBytes.HonestTrace.Sz)
    (Fd : FileDescription ProofFile.Inst) (enter : Fd.S₃ → Except String T12)
    (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf ProofFile.Inst) (no : Place → ℕ)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (weights : Local W₀ Rc ProofFile.Inst Tr → Weights)
    (rand : Desc.K14.P14 → Local W₀ Rc ProofFile.Inst Tr → TableRand)
    {M : ManyJob (Local W₀ Rc ProofFile.Inst Tr) X}
    (made : jobRealW S Fd enter pile no readers weights rand Zp Bs.G₀ = some M)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (numberI numberW : ℕ)
    (sentOwn : X)
    (tableIndex : ∀ k v hd, tb₁ (.own 1) k v hd =
      K1.treeTbl 0 (inOf readers)
        (K1.placeJob (X := X) (VerifiableInference.Desc.K1.firstPar Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp)) numberI (K1.firstFold Bs.G₀.first)
          (K1.lotData S Zp Bs.G₀)) sentOwn 1 k v hd)
    (tableW : ∀ k v hd, tb₁ (.own 82) k v hd =
      K1.treeTbl 0 (inOf readers)
        (K1.wJobAt (X := X) Zp.first (K1.wGp Zp) 4 wMsgFull numberW (K13.wDataAt pile Zp Bs.G₀))
        sentOwn 0 k v hd)
    (fixedW : fx₁ (.own 82) = roundsTo cF.blocksInOrder 356) (witnessOmega : W₂ → Ask)
    (rounds : r₁ = (Fd.first.blocksInOrder.flatMap (·.rounds)).length)
    (tableOmega : ∀ An, sendPub Zp = some An →
      tb₂ (.own 1) = sendTable (jobOmega An) witnessOmega senderO.place 1 0)
    (fixedOmega : ∀ An, sendPub Zp = some An → An.atPoint + 1 ≤ fx₂ (.own 1))
    (rowsOmega : ∀ An, sendPub Zp = some An → ∀ v,
      (askOf An weights (rand An.P) v).rows = (witnessOmega (toCommon v)).rows) :
    ∀ k st m E (c : RowCoins [(firstPart M.toRun.toTest :
        Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X), restPart M.toRun.toTest]),
      ThrS (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀ toCommon tb₁
        tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w) Said 2 k st m E →
      lendRow Bk (Bk.rowsOf (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁
          n₀ toCommon tb₁ tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w).chain)
        (k.look (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀ toCommon
          tb₁ tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w).chain) M.p.place
        [(firstPart M.toRun.toTest :
          Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X), restPart M.toRun.toTest]
        0 = .ok c →
      ∀ i (hi : i < takenLast.length), TakenIs (lastAt (Zp := Zp) (Np := Np) (cF := cF) H N Mg ML PL
          order ends wit r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd Kp w) k m
        (M.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins M.toRun.toTest c.2.1).mem
          (M.toRun.toTest.first m.st.input (frontOf m) (restCoins M.toRun.toTest c.2.1)))
        i takenLast[i] :=
  taken_at_lastAt H N Mg ML PL order ends wit r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ J own₀ item n₁ n₂ Vd Rd
    Kp w h O hB S Fd enter pile no readers weights rand made Said
    (firstArmsAtLastAt H N Mg ML PL order ends wit r₁ n₀ toCommon tb₁ tb₂ fx₁ fx₂ J own₀ item n₁ n₂
      Vd Rd Kp w h O hB S Fd enter pile no readers weights rand made Said numberI numberW sentOwn
      tableIndex tableW fixedW)
    witnessOmega rounds tableOmega fixedOmega rowsOmega

end AtFullSide.K12.Part4

#print axioms AtFullSide.K12.Part4.firstArmsAtLastAt
#print axioms AtFullSide.K12.Part4.takenAtLastAt
