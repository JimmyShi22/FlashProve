-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/Part4/TakenAtTheBaseProver.lean: THE LAST CHAIN's PROXIMITY TEST (the kind K12, the
place W): UNDER THE LIBRARY's HYPOTHESIS ON THE FIRST CHAIN AND "THE MAKER RETURNS A AT THE WIDER
FILLING" ALONE, AT THE FILLING's OWN JOB (jobAtFill) AND AT THE LAST CHAIN's THREAD LAID OVER THE
FIRST CHAIN's THREAD's TABLES AT THE FIRST CHAIN's SCRIPT: FirstArms; AND THE CLAUSE "taken" AT ALL
THREE TREES, UNDER FOUR NAMED PREMISES ON THE SHARED THREAD's TABLE.

WHAT IT IS NOT.
  * The hypothesis (P5J.AtMgA: the full size and the format's second hash function alone) and hA are
    premises. made, that jobAtFill returns a job, is a premise here; another author's
    job_at_filling (AtFullSide/K12/LettersAtHead.lean) has it under the same two.
  * In takenAtTheBaseProver four premises on the shared thread's table are left, each by name:
    rounds, tableOmega, fixedOmega, rowsOmega: those of another author's taken_at_lastAt. tb₂ and
    fx₂ are letters there.
  * At lastAt (K12/AtFile/WTable.lean) over these tables: that another author's last thread is that
    thread is not said here.
  * One clause of the four that a stand of this test still owes at the tables (StandRest: field,
    taken, ends, saysAt). It does not say that a stand is reached, that a part plays or that a
    verifier accepts. No count moves by it.
  * In the side library.
  * Nothing on completeness, soundness or what a proof hides.

WHAT IT IS. No definition; three theorems.

  bookOfTheReturn          under the hypothesis, what the maker returns has the book made of the
                           written description
  firstArmsAtTheBaseProver **FirstArms**, under h, hA and made alone
  takenAtTheBaseProver     **the clause taken, at the three trees**, under these and the four

CALLED. firstArmsAtTheFirstScript, armsAtTheFirstScript (ArmsAtTheFirstScript.lean); takenAtLastAt
(TakenAtTheLastThread.lean). Of other authors: makers_book_one (AtFullSide/K14/MakersBookOne.lean);
atPure_at_laid_ground (Honest/AtHeadGround.lean); the hypothesis's own field laid.opened.
-/
import AtFullSide.K12.Part4.ArmsAtTheFirstScript
import AtFullSide.K14.MakersBookOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12.Part4
open ProofFile.Honest ProofFile.Honest.K12
open VerifiableInference.Desc (Chain Block FileDescription Place Strs)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.Third (S₃)
open ProofFile.Honest.K12.Light (ManyJob askOf)
open ProofFile.Honest.K12.AtProof (senderO sendPub randAt)
open ProofFile.Honest.K12.AtFile (FirstArms TakenIs lastAt takenLast)
open ProofFile.Honest.K1 (LocB readersB firstScriptAt)
open ProofFile.Honest.K14 (jobOmega sendTable Ask)
open ProofFile.Honest.FirstThread (lettersHead WtF)
open AtFullSide.K14 (makers_book_one)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open P5J (TS)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the hypothesis, what the maker returns has the book made of the written description.**
-/
theorem bookOfTheReturn (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) =
      .ok A) :
    bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok A.B := by
  obtain ⟨B, written, -, -, -, atEveryReturn⟩ := makers_book_one h
  obtain ⟨same, -⟩ := atEveryReturn _ _ _ _ _ _ A hA
  rw [same]
  exact written

variable {X₀ Wt W₂ : Type}
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

/-- **FirstArms at the filling's own job, under the hypothesis and the maker's return alone.** The
letters of the two threads are free. -/
theorem firstArmsAtTheBaseProver (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (test : ℕ → TS → Option String) (carryX : ℕ → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : ℕ) (Vd : LocB W₀ → Prop) (Rd : ℕ → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀) {M : ManyJob (LocB W₀) Unit}
    (made : jobAtFill A.Z Np cF I S Op A.G = some M)
    (Said : ℕ → Coins A.B → Mid (LocB W₀) Unit → Prop) :
    FirstArms (lastAt (Zp := A.Z) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀ toCommon
      (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread.table tb₂
      (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread.fixed fx₂ J () itemL t₁ t₂ VdL RdL KpL wL) Said M := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, ground, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  rw [ground] at made
  exact firstArmsAtTheFirstScript H N Mg ML PL order ends wit r₁ n₀ toCommon tb₂ fx₂ J itemL t₁ t₂
    VdL RdL KpL wL h O hA (bookOfTheReturn h hA) test carryX item n₁ n₂ b₀ Vd Rd Kp w _ _ _ _ _ made
    Said

/-- **The clause taken at the filling's own job, at the three trees.** The last four premises are
those of taken_at_lastAt on the shared thread's table. -/
theorem takenAtTheBaseProver (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (test : ℕ → TS → Option String) (carryX : ℕ → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : ℕ) (Vd : LocB W₀ → Prop) (Rd : ℕ → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀) {M : ManyJob (LocB W₀) Unit}
    (made : jobAtFill A.Z Np cF I S Op A.G = some M)
    (Said : ℕ → Coins A.B → Mid (LocB W₀) Unit → Prop) (witnessOmega : W₂ → Ask)
    (rounds : r₁ = ((P5J.F0T OnBytes.secondHashFunction A.Z Np cF).first.blocksInOrder.flatMap (·.rounds)).length)
    (tableOmega : ∀ An, sendPub A.Z = some An →
      tb₂ (.own 1) = sendTable (jobOmega An) witnessOmega senderO.place 1 0)
    (fixedOmega : ∀ An, sendPub A.Z = some An → An.atPoint + 1 ≤ fx₂ (.own 1))
    (rowsOmega : ∀ An, sendPub A.Z = some An → ∀ v,
      (askOf An (fun v => I.weights A.Z v.w₀) (fun v => randAt An.P v.rc) v).rows =
        (witnessOmega (toCommon v)).rows) :
    ∀ k st m E (c : RowCoins [(firstPart M.toRun.toTest : Part (LocB W₀) (LocB W₀) Unit),
        restPart M.toRun.toTest]),
      ThrS (lastAt (Zp := A.Z) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀ toCommon
        (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
          w).thread.table tb₂
        (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
          w).thread.fixed fx₂ J () itemL t₁ t₂ VdL RdL KpL wL) Said 2 k st m E →
      lendRow A.B (A.B.rowsOf 2) (k.look 2) M.p.place
        [(firstPart M.toRun.toTest : Part (LocB W₀) (LocB W₀) Unit), restPart M.toRun.toTest]
        0 = .ok c →
      ∀ i (hi : i < takenLast.length), TakenIs (lastAt (Zp := A.Z) (Np := Np) (cF := cF) H N Mg ML
          PL order ends wit r₁ n₀ toCommon
          (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
            w).thread.table tb₂
          (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
            w).thread.fixed fx₂ J () itemL t₁ t₂ VdL RdL KpL wL) k m
        (M.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins M.toRun.toTest c.2.1).mem
          (M.toRun.toTest.first m.st.input (frontOf m) (restCoins M.toRun.toTest c.2.1)))
        i takenLast[i] := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, ground, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  rw [ground] at made
  obtain ⟨tableIndex, tableW, fixedW⟩ :=
    armsAtTheFirstScript h O hA test carryX item n₁ n₂ b₀ Vd Rd Kp w
  exact takenAtLastAt H N Mg ML PL order ends wit r₁ n₀ toCommon _ tb₂ _ fx₂ J () itemL t₁ t₂ VdL
    RdL KpL wL h O (bookOfTheReturn h hA) S _ _ Op.pile _ (readersB I A.Z) _ _ made Said _ _ ()
    tableIndex tableW fixedW witnessOmega rounds tableOmega fixedOmega rowsOmega

end AtFullSide.K12.Part4

#print axioms AtFullSide.K12.Part4.bookOfTheReturn
#print axioms AtFullSide.K12.Part4.firstArmsAtTheBaseProver
#print axioms AtFullSide.K12.Part4.takenAtTheBaseProver
