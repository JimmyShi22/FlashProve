-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/Part4/TakenUnderTheTwo.lean: THE LAST CHAIN's PROXIMITY TEST (the kind K12, the place
W): UNDER THE LIBRARY's HYPOTHESIS ON THE FIRST CHAIN AND "THE MAKER RETURNS A AT THE WIDER
FILLING", THESE TWO ALONE: THE FILLING's JOB IS MADE, AND AT IT FirstArms HOLDS AT THE LAST CHAIN's
THREAD LAID OVER THE FIRST CHAIN's THREAD's TABLES AT THE FIRST CHAIN's SCRIPT; AND THE CLAUSE
"taken" AT ALL THREE TREES, UNDER FOUR NAMED PREMISES ON THE SHARED THREAD's TABLE.

WHAT IT IS NOT.
  * The hypothesis (P5J.AtMgA: the full size and the format's second hash function alone) and hA are
    premises.
  * In takenUnderTheTwo four premises on the shared thread's table are left, each by name: rounds,
    tableOmega, fixedOmega, rowsOmega: those of another author's taken_at_lastAt.
  * At lastAt (K12/AtFile/WTable.lean) over these tables: that another author's last thread is that
    thread is not said here.
  * One clause of the four that a stand of this test still owes at the tables (StandRest: field,
    taken, ends, saysAt). It does not say that a stand is reached, that a part plays or that a
    verifier accepts. No count moves by it.
  * In the side library.
  * Nothing on completeness, soundness or what a proof hides.

WHAT IT IS. No definition; two theorems.

  firstArmsUnderTheTwo   **the job is made, and FirstArms holds at it**, at every Said
  takenUnderTheTwo       **the job is made, and the clause taken holds at it, at the three trees**,
                         under the four

CALLED. firstArmsAtTheBaseProver, takenAtTheBaseProver (TakenAtTheBaseProver.lean). Of another
author: job_at_filling (AtFullSide/K12/LettersAtHead.lean).
-/
import AtFullSide.K12.Part4.TakenAtTheBaseProver

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12.Part4
open ProofFile.Honest ProofFile.Honest.K12
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.Third (S₃)
open ProofFile.Honest.K12.Light (ManyJob askOf)
open ProofFile.Honest.K12.AtProof (senderO sendPub randAt)
open ProofFile.Honest.K12.AtFile (FirstArms TakenIs lastAt takenLast)
open ProofFile.Honest.K1 (LocB firstScriptAt)
open ProofFile.Honest.K14 (jobOmega sendTable Ask)
open ProofFile.Honest.FirstThread (lettersHead WtF)
open P5J (TS)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {X₀ Wt W₂ : Type}
  (H : Prover W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells X₀ Unit)
  (N : VerifiableInference.Desc.Shared.NumbersS)
  (Mg : LocB W₀ → VerifiableInference.Desc.Shared.MeaningS Desc.K14.St (ProofFile.InstPub × TS) Wt)
  (ML : VerifiableInference.Desc.Last.MeaningL S₃ Wt)
  (PL : VerifiableInference.Desc.Last.PromMeaningL Desc.K14.St S₃ (ProofFile.InstPub × TS))
  (order : S₃ → Prop)
  (ends : Coins A.B → LocB W₀ → List Fmt.Drawn → (ProofFile.InstPub × TS) × Desc.K14.St)
  (wit : Coins A.B → LocB W₀ → List Fmt.Drawn → Wt)
  (r₁ n₀ : ℕ) (toCommon : LocB W₀ → W₂)
  (tb₂ : Fmt.TreeSource → Coins A.B → W₂ → List Fmt.Drawn → Place × Table)
  (fx₂ : Fmt.TreeSource → ℕ) (J : TestJob (LocB W₀) Unit)
  (itemL t₁ t₂ : ℕ) (VdL : LocB W₀ → Prop) (RdL : ℕ → LocB W₀ → S₃ → Prop)
  (KpL : Place → S₃ → S₃ → Prop) (wL : LocB W₀)

/-- **Under the two alone: the filling's job is made, and FirstArms holds at it.** The letters of
the two threads are free. -/
theorem firstArmsUnderTheTwo (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (test : ℕ → TS → Option String) (carryX : ℕ → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : ℕ) (Vd : LocB W₀ → Prop) (Rd : ℕ → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀) :
    ∃ M, jobAtFill A.Z Np cF I S Op A.G = some M ∧
      ∀ Said : ℕ → Coins A.B → Mid (LocB W₀) Unit → Prop,
        FirstArms (lastAt (Zp := A.Z) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀
          toCommon
          (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
            w).thread.table tb₂
          (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
            w).thread.fixed fx₂ J () itemL t₁ t₂ VdL RdL KpL wL) Said M := by
  obtain ⟨M, made, -⟩ := job_at_filling h I S Op hA
  exact ⟨M, made, fun Said => firstArmsAtTheBaseProver H N Mg ML PL order ends wit r₁ n₀ toCommon
    tb₂ fx₂ J itemL t₁ t₂ VdL RdL KpL wL h hA test carryX item n₁ n₂ b₀ Vd Rd Kp w made Said⟩

/-- **Under the two and the four: the filling's job is made, and the clause taken holds at it, at
the three trees.** -/
theorem takenUnderTheTwo (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (test : ℕ → TS → Option String) (carryX : ℕ → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : ℕ) (Vd : LocB W₀ → Prop) (Rd : ℕ → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀) (witnessOmega : W₂ → Ask)
    (rounds : r₁ = ((P5J.F0T OnBytes.secondHashFunction A.Z Np cF).first.blocksInOrder.flatMap (·.rounds)).length)
    (tableOmega : ∀ An, sendPub A.Z = some An →
      tb₂ (.own 1) = sendTable (jobOmega An) witnessOmega senderO.place 1 0)
    (fixedOmega : ∀ An, sendPub A.Z = some An → An.atPoint + 1 ≤ fx₂ (.own 1))
    (rowsOmega : ∀ An, sendPub A.Z = some An → ∀ v,
      (askOf An (fun v => I.weights A.Z v.w₀) (fun v => randAt An.P v.rc) v).rows =
        (witnessOmega (toCommon v)).rows) :
    ∃ M, jobAtFill A.Z Np cF I S Op A.G = some M ∧
      ∀ (Said : ℕ → Coins A.B → Mid (LocB W₀) Unit → Prop) k st m E
        (c : RowCoins [(firstPart M.toRun.toTest : Part (LocB W₀) (LocB W₀) Unit),
          restPart M.toRun.toTest]),
        ThrS (lastAt (Zp := A.Z) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀ toCommon
          (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
            w).thread.table tb₂
          (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
            w).thread.fixed fx₂ J () itemL t₁ t₂ VdL RdL KpL wL) Said 2 k st m E →
        lendRow A.B (A.B.rowsOf 2) (k.look 2) M.p.place
          [(firstPart M.toRun.toTest : Part (LocB W₀) (LocB W₀) Unit), restPart M.toRun.toTest]
          0 = .ok c →
        ∀ i (hi : i < takenLast.length), TakenIs (lastAt (Zp := A.Z) (Np := Np) (cF := cF) H N Mg
            ML PL order ends wit r₁ n₀ toCommon
            (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
              w).thread.table tb₂
            (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
              w).thread.fixed fx₂ J () itemL t₁ t₂ VdL RdL KpL wL) k m
          (M.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins M.toRun.toTest c.2.1).mem
            (M.toRun.toTest.first m.st.input (frontOf m) (restCoins M.toRun.toTest c.2.1)))
          i takenLast[i] := by
  obtain ⟨M, made, -⟩ := job_at_filling h I S Op hA
  exact ⟨M, made, fun Said => takenAtTheBaseProver H N Mg ML PL order ends wit r₁ n₀ toCommon tb₂
    fx₂ J itemL t₁ t₂ VdL RdL KpL wL h hA test carryX item n₁ n₂ b₀ Vd Rd Kp w made Said
    witnessOmega rounds tableOmega fixedOmega rowsOmega⟩

end AtFullSide.K12.Part4

#print axioms AtFullSide.K12.Part4.firstArmsUnderTheTwo
#print axioms AtFullSide.K12.Part4.takenUnderTheTwo
