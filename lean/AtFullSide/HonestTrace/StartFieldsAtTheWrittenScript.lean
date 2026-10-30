-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/StartFieldsAtTheWrittenScript.lean

Nothing on hiding. No property of the protocol is claimed. Theorems alone; joinings by calls.

WHERE "ready" RETURNED AND "okStart" ACCEPTS AT THE BASE RETURN: THE FACTS OF WHICH THE FIRST THREAD's START IS MADE, AT THE WRITTEN FIRST SCRIPT, WITH THE SWITCHES AND THE SIZES PAID: IN A FILE BENEATH WHICH NEITHER "KindPays" (Honest/Law/ReadyOfSides.lean) NOR AtFullSide/K12/Pays* LIES.
* "start_fields_at_the_written_script": okStart ∧ the request's bytes are read back ∧ ∃ i s, i serves s ∧ the written Script is tied to them: the texts of the fields startFit, requestParses, served of the threads' debts.
* "served_request_is_the_runs_own": ∃ i s: THE RUN's OWN MATRIX HOLDS i ∧ THE RUN's OWN BYTES ARE READ AS s ∧ i serves s ∧ the written Script is tied to them.
* "enters_at_the_written_script": Enters₁ at the first thread of the written Script.
* "first_test_accepts_a_tied_instance": the first test accepts an instance that "TiedYes" ties: from one accept ("okStart_of_one") and the tie's first clause; "in scope" is the head's own field.

Limits. THAT "ready" RETURNED IS A PREMISE OF THE FIRST THREE; so is "okStart". Border 0 of the FIRST of three threads alone.
What lies beneath through Honest/K3/Term/PlaneNumbersInScope.lean goes with
"planes_sizes_under_the_head" (Joint/EntersSymbolsPlanesSizesPaid.lean): that K3/Term file imports
Johnson.HonestTrace.PlaneLookNumbersInScope: by that door nothing of the executable model's folder
Johnson/HonestTrace/Run comes beneath.
Closed facts by Lean's kernel lie beneath the three laws on the switches (ClosingW0 to ClosingW4). AT A RETURN OF THE BASE FILLING, NOT AT THE ONLINE PROVER. The hash
"OnBytes.secondHashFunction" alone.
Closed facts by Lean's kernel lie beneath (among them ClosingW0 to ClosingW4; "theLive_zFull"):
replayed by no independent checker.
-/
import AtFullSide.HonestTrace.EntersAtTheWrittenScript
import AtFullSide.K1.LaysAtSwitchesPaid
import Johnson.HonestTrace.Joint.EntersSymbolsPlanesSizesPaid
import E2E.BridgeJoinAtFiles
import E2E.StartInScope
import E2E.BaseMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace HonestTraceRun.StartFields

open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles WZ TiedYes descZ)
open OnBytes (TableKey)
open OnBytes.HonestTrace (Sz ServesAt ScriptTies)
open Inst.Model (Instance ppref)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open VerifiableInference.Desc (Chain)
open P5J (TS)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (firstParts)
open ProofFile.Honest.Term (matrixInput baseMaker)
open LPFD.Full (XF instanceAsPlainRecord)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **The texts of startFit, requestParses and served**, where "ready" returned and "okStart" accepts at the base return. -/
theorem start_fields_at_the_written_script (made : baseMaker files = .ok A)
    (H : HeadAtReturn files A) (numbers : FallNumbers) {w₀ : FullSizeMatrix} {rc : IndexCommitterCoins} {ξ : ProofFile.Inst}
    {k : Coins A.B} {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    (returns : ready H.description A.B A.H w₀ rc ξ k = .ok R)
    (accepts : H.description.okStart ξ = true) :
    H.description.okStart ξ = true ∧
      (_root_.Meaning.backReq (H.head.𝔇.reqB ξ.pub)).isSome = true ∧
      ∃ (i : Cm.Idx) (s : Instance ppref), ServesAt (P5J.At.X A.Z) i s ∧
        ScriptTies files A.Z H.firstChain
          (firstParts matrixInput Sz.ref openHonest A H.firstChain numbers).script k R.own i s :=
  HonestTraceRun.Meets.three_thread_debts_at_the_written_script made H numbers returns accepts
    (ProofFile.Honest.K1.lent_at_return H.head made) (ProofFile.Honest.K1.closing_at_return H.head made)
    (fun p atPlace _ ready => ProofFile.Honest.K1.public_at_return H.head made ready.1 p atPlace)
    (OnBytes.HonestTrace.planes_sizes_under_the_head H.head)

/-- **The served request is the run's own**, and the written Script is tied to it. -/
theorem served_request_is_the_runs_own (made : baseMaker files = .ok A) (H : HeadAtReturn files A)
    (numbers : FallNumbers) {w₀ : FullSizeMatrix} {rc : IndexCommitterCoins} {ξ : ProofFile.Inst} {k : Coins A.B}
    {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    (returns : ready H.description A.B A.H w₀ rc ξ k = .ok R)
    (accepts : H.description.okStart ξ = true) :
    ∃ (i : Cm.Idx) (s : Instance ppref), Holds R.own.w₀ i ∧ ProofFile.instOf R.own.x = some s ∧
      ServesAt (P5J.At.X A.Z) i s ∧
      ScriptTies files A.Z H.firstChain
        (firstParts matrixInput Sz.ref openHonest A H.firstChain numbers).script k R.own i s :=
  HonestTraceRun.Meets.served_and_tied_of_ready HonestTraceRun.Meets.baseFilling_trace made H
    (firstParts matrixInput Sz.ref openHonest A H.firstChain numbers) returns accepts
    (HonestTraceRun.Meets.written_script_reads_the_input made H
      (ProofFile.Honest.K1.lent_at_return H.head made) (ProofFile.Honest.K1.closing_at_return H.head made)
      (fun p atPlace _ ready => ProofFile.Honest.K1.public_at_return H.head made ready.1 p atPlace)
      (OnBytes.HonestTrace.planes_sizes_under_the_head H.head) k
      (readyInput_of_ready returns accepts))

/-- **The first thread at the written Script holds at the start that "ready" gives.** -/
theorem enters_at_the_written_script (made : baseMaker files = .ok A) (H : HeadAtReturn files A)
    (numbers : FallNumbers) {w₀ : FullSizeMatrix} {rc : IndexCommitterCoins} {ξ : ProofFile.Inst} {k : Coins A.B}
    {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    (returns : ready H.description A.B A.H w₀ rc ξ k = .ok R)
    (accepts : H.description.okStart ξ = true) :
    Enters₁ H.description A.H
      (firstThread H (firstParts matrixInput Sz.ref openHonest A H.firstChain numbers) R.own) w₀ rc
      ξ k R :=
  HonestTraceRun.Meets.enters_first_chain_at_the_written_script made H numbers returns accepts
    (ProofFile.Honest.K1.lent_at_return H.head made) (ProofFile.Honest.K1.closing_at_return H.head made)
    (fun p atPlace _ ready => ProofFile.Honest.K1.public_at_return H.head made ready.1 p atPlace)
    (OnBytes.HonestTrace.planes_sizes_under_the_head H.head)

/-- **The first test accepts a tied instance**, from one accept. -/
theorem first_test_accepts_a_tied_instance {R₂ R₃ : Type} [Inhabited R₃] {run₂ : R₂ → ByteArray}
    {run₃ : R₃ → ByteArray} {Tr X₀ X' : Type} {B : ProverCoinCounts} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : Chain TS ProofFile.Cl} {G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey Tr X₀ X'}
    {Hp : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst TableKey Tr X₀ X'} {Yes : FullSizeMatrix → XF → Prop} {n : ℕ}
    {w : WZ files} {x : ProofFile.Inst} (H : HeadAtReturn files A)
    (oneAccept : ∃ z₀, H.description.okStart (instanceAsPlainRecord z₀) = true)
    (tied : TiedYes files Zp Np cF run₂ run₃ B G Hp Yes n w x) :
    H.description.okStart x = true := by
  obtain ⟨z₀, accepts₀⟩ := oneAccept
  obtain ⟨x', -, rfl⟩ := tied.1
  exact AtPublicFiles.Start.okStart_of_one H.head.scope H.head.laid accepts₀ _

end HonestTraceRun.StartFields

#print axioms HonestTraceRun.StartFields.start_fields_at_the_written_script
#print axioms HonestTraceRun.StartFields.served_request_is_the_runs_own
#print axioms HonestTraceRun.StartFields.enters_at_the_written_script
#print axioms HonestTraceRun.StartFields.first_test_accepts_a_tied_instance
