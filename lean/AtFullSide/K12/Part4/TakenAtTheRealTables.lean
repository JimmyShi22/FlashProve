-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/Part4/TakenAtTheRealTables.lean: THE LAST CHAIN's PROXIMITY TEST (the kind K12, the
place W): UNDER THE LIBRARY's HYPOTHESIS ON THE FIRST CHAIN AND "THE MAKER RETURNS A AT THE WIDER
FILLING", AND WHERE THE THREAD's MAP TO THE SHARED CHAIN's INPUT KEEPS THE INDEX AND THE COMMITTER's
VALUES: THE FILLING's JOB IS MADE, AND AT IT THE CLAUSE "taken" HOLDS AT ALL THREE TREES, AT THE
LAST CHAIN's THREAD LAID OVER THE FIRST CHAIN's THREAD's TABLES AT THE FIRST CHAIN's SCRIPT AND OVER
THE SHARED CHAIN's TABLES (tableShared, fixedShared).

WHAT IT IS NOT.
  * NOT IN FRONT OF A LAW OVER COINS: the label that the files beneath bear (WJointLast.lean,
    WJointArms.lean, WTable.lean); the rule is at its home, the head of
    Johnson/Bind/ForProver/FiveFieldsAt.lean.
  * AT THE FILLING, NOT READ THROUGH: at the base prover's filling's return, at its own type of
    random values; not at the online prover, whose filling reads this one through the coins' map.
  * Beneath it lie files that their authors call trials (AtFullSide/K12/FirstArmsTables.lean,
    FirstArmsK1.lean). The wide filling is defined in Honest/K1/Law/WSideAtFill.lean.
    Here it is called the wider filling, and the base prover's filling.
  * The hypothesis (P5J.AtMgA: the full size and the format's second hash function alone) and hA are
    premises. Two more are on a letter of the thread: sameIndex, sameRandomness: the map toCommon
    from the last chain's input to the shared chain's keeps the index and the committer's values.
  * At lastAt (K12/AtFile/WTable.lean) over these tables: that another author's last thread is that
    thread is not said here. The two tests' jobs in tableShared (testOnU, testOnOmega) are letters:
    the table at the source that is read here, own 1, does not read them.
  * ONE clause, "taken", of those that a stand of this test still owes at the tables (the structure
    StandRest, K12/AtFile/WTable.lean). No line lays it into that structure, and the value of the
    last thread's letters with these tables is laid by nobody here. It does not say that a stand is
    reached, that a part plays or that a verifier accepts. No count moves by it.
  * In the side library.
  * Nothing on completeness, soundness or what a proof hides.

WHAT IT IS. No definition; two theorems.

  theTwoReadersOfTheCommittersValuesAreOne   K14's randNow, by which another author's laid shared
                         table reads the index committer's values, is randAt, by which the job's
                         rows are read here
  takenAtTheRealTables   **the statement**

KIN. The four premises on the shared thread's table, which takenUnderTheTwo takes under "sendPub
returns", are paid here, so nothing hangs on that clause; that sendPub does return under the
hypothesis is `sendPub_at_head` (Johnson/Desc/ProofFile/Honest/K12/AtProof/HalfAtPure.lean), its
premise on the blocks paid, at a head at the return (`HeadAtReturn`), by `eight_blocks_at_the_head`
(AtFullSide/LaterThreads/PublicFactsAtTheHead.lean).

CALLED. takenUnderTheTwo (TakenUnderTheTwo.lean). Of other authors: four_on_omega
(K12/AtFile/WJointFour.lean); facts_at_head (K12/NearAtHead.lean); blocks_eight
(Johnson/Desc/K14/Law/BlocksEight.lean).
-/
import AtFullSide.K12.Part4.TakenUnderTheTwo
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WJointFour
import Johnson.Desc.ProofFile.Honest.K12.NearAtHead
import Johnson.Desc.K14.Law.BlocksEight

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12.Part4
open ProofFile.Honest ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Chain Place Strs K1.qAt)
open VerifiableInference.Desc.Third (S₃)
open ProofFile.Honest.K12.Light (ManyJob)
open ProofFile.Honest.K12.AtProof (randAt)
open ProofFile.Honest.K12.AtFile (TakenIs lastAt takenLast tableShared fixedShared four_on_omega)
open ProofFile.Honest.K1 (LocB firstScriptAt)
open ProofFile.Honest.K14 (witOf)
open ProofFile.Honest.FirstThread (lettersHead WtF)
open P2Law.ProofPlan (declProofFull)
open P5J (TS)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {X₀ Wt : Type}
  (H : Prover W₀ IndexCommitterCoins ProofFile.Inst TableKey Cells X₀ Unit)
  (N : VerifiableInference.Desc.Shared.NumbersS)
  (Mg : LocB W₀ → VerifiableInference.Desc.Shared.MeaningS Desc.K14.St (ProofFile.InstPub × TS) Wt)
  (ML : VerifiableInference.Desc.Last.MeaningL S₃ Wt)
  (PL : VerifiableInference.Desc.Last.PromMeaningL Desc.K14.St S₃ (ProofFile.InstPub × TS))
  (order : S₃ → Prop)
  (ends : Coins A.B → LocB W₀ → List Fmt.Drawn → (ProofFile.InstPub × TS) × Desc.K14.St)
  (wit : Coins A.B → LocB W₀ → List Fmt.Drawn → Wt)
  (n₀ : ℕ) (toCommon : LocB W₀ → Common W₀ IndexCommitterCoins TableKey) (J : TestJob (LocB W₀) Unit)
  (itemL t₁ t₂ : ℕ) (VdL : LocB W₀ → Prop) (RdL : ℕ → LocB W₀ → S₃ → Prop)
  (KpL : Place → S₃ → S₃ → Prop) (wL : LocB W₀)

/-- **The two readers of the index committer's values are one.** -/
theorem theTwoReadersOfTheCommittersValuesAreOne : ProofFile.Honest.K14.randNow = randAt := rfl

/-- **The filling's job is made, and the clause taken holds at it, at the three trees, at the real
tables.** Four premises: the hypothesis, the maker's return, and that toCommon keeps the index and
the committer's values (sameIndex, sameRandomness). The other letters of the threads are free. -/
theorem takenAtTheRealTables (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (test : ℕ → TS → Option String) (carryX : ℕ → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : ℕ) (Vd : LocB W₀ → Prop) (Rd : ℕ → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀)
    (testOnU testOnOmega : TestJob (Common W₀ IndexCommitterCoins TableKey) X₀) (ownShared : X₀)
    (sameIndex : ∀ v, (toCommon v).w₀ = v.w₀) (sameRandomness : ∀ v, (toCommon v).rc = v.rc) :
    ∃ M, jobAtFill A.Z Np cF I S Op A.G = some M ∧
      ∀ (Said : ℕ → Coins A.B → Mid (LocB W₀) Unit → Prop) k st m E
        (c : RowCoins [(firstPart M.toRun.toTest : Part (LocB W₀) (LocB W₀) Unit),
          restPart M.toRun.toTest]),
        ThrS (lastAt (Zp := A.Z) (Np := Np) (cF := cF) H N Mg ML PL order ends wit
          ((P5J.F0T OnBytes.secondHashFunction A.Z Np cF).first.blocksInOrder.flatMap (·.rounds)).length n₀ toCommon
          (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
            w).thread.table
          (tableShared (K1.qAt A.Z Np) (I.weights A.Z) (randAt (K1.qAt A.Z Np)) testOnU testOnOmega
            ownShared)
          (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
            w).thread.fixed
          (fixedShared declProofFull.2.1) J () itemL t₁ t₂ VdL RdL KpL wL) Said 2 k st m E →
        lendRow A.B (A.B.rowsOf 2) (k.look 2) M.p.place
          [(firstPart M.toRun.toTest : Part (LocB W₀) (LocB W₀) Unit), restPart M.toRun.toTest]
          0 = .ok c →
        ∀ i (hi : i < takenLast.length), TakenIs (lastAt (Zp := A.Z) (Np := Np) (cF := cF) H N Mg
            ML PL order ends wit
            ((P5J.F0T OnBytes.secondHashFunction A.Z Np cF).first.blocksInOrder.flatMap (·.rounds)).length n₀ toCommon
            (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
              w).thread.table
            (tableShared (K1.qAt A.Z Np) (I.weights A.Z) (randAt (K1.qAt A.Z Np)) testOnU
              testOnOmega ownShared)
            (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
              w).thread.fixed
            (fixedShared declProofFull.2.1) J () itemL t₁ t₂ VdL RdL KpL wL) k m
          (M.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins M.toRun.toTest c.2.1).mem
            (M.toRun.toTest.first m.st.input (frontOf m) (restCoins M.toRun.toTest c.2.1)))
          i takenLast[i] := by
  obtain ⟨-, -, goes⟩ := ProofFile.Honest.K12.Light.facts_at_head h.toAtMg
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, eight⟩ :=
    _root_.Desc.K14.Law.blocks_eight (K1.qAt A.Z Np) _ goes
  obtain ⟨tableOmega, fixedOmega, rowsOmega⟩ := four_on_omega (Bk := A.B) h.toAtMg b1 b2 b3 b4 b5 b6
    b7 b8 eight (I.weights A.Z) randAt testOnU testOnOmega ownShared toCommon (·.w₀) (·.rc)
    sameIndex sameRandomness
  exact takenUnderTheTwo H N Mg ML PL order ends wit _ n₀ toCommon _ _ J itemL t₁ t₂ VdL RdL KpL wL
    h hA test carryX item n₁ n₂ b₀ Vd Rd Kp w
    (witOf (K1.qAt A.Z Np) (I.weights A.Z) (randAt (K1.qAt A.Z Np))) rfl tableOmega fixedOmega
    rowsOmega

end AtFullSide.K12.Part4

#print axioms AtFullSide.K12.Part4.theTwoReadersOfTheCommittersValuesAreOne
#print axioms AtFullSide.K12.Part4.takenAtTheRealTables
