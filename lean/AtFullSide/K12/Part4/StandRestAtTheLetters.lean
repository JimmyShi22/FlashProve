-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/Part4/StandRestAtTheLetters.lean

This file proves the structure StandRest (Johnson/Desc/ProofFile/Honest/K12/AtFile/WTable.lean) for
the proximity test of the second chain of the proof file's description (sub-protocol kind K12: the
proof file's proximity test at the place W). It is proved at the Thread thread₃, the predicate said₃
and the job P.ownMany of AtFullSide/Honest/TheLettersLast.lean.

Terms.
  * The proof file's description has three chains of sub-protocols: the first, the shared and the
    second chain (some Lean names call the second chain the last one). For each chain the library
    defines a Thread T and an invariant ThrS T Said b
    (Johnson/Desc/ProofFile/Honest/Thread/Said.lean) on the prover's coins, the description's state
    and the prover's state in front of sub-protocol number b.
  * StandRest T Said A has three fields, each an implication whose premise is ThrS T Said 2, the
    invariant in front of the proximity test. StandRest.field (FieldAtW) is about the columns opened
    so far and the state at which the chain began. StandRest.taken (TakenIs) says that each tree
    that the second chain takes over from a preceding chain has the depth and the columns of the
    corresponding tree of the job A. StandRest.saysAt (SaysLeft) is about what the rows of the test
    state.
  * O : TheLetters.OpenShared A and P : TheLetters.OpenLast h O are the two auxiliary parameters of
    the structures in AtFullSide/Honest/TheOneObject.lean (their fields open₂ and open₃). P contains
    propositions, so a value of P is itself a premise.
  * The base construction is onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling (the premise hA
    writes matrixFilling unfolded), and HeadAtReturn Z A collects the library's facts on a return A
    of it (see the header of AtFullSide/Honest/CompleteAtTheFiles.lean).

Main statements.
  * firstRoundsAreTheFlatRounds: firstRounds h equals the number of rounds that the sub-protocols of
    the first chain declare.
  * takenAtAnyCount: takenAtTheRealTables, restated with the number of the first chain's rounds as a
    variable r₁ under an equation, and at a job M that jobAtFill is known to return.
  * taken_at_letters: StandRest.taken at thread₃, said₃ and P.ownMany.
  * standRest_at_letters: the whole structure. StandRest.field is field_of_said_W, StandRest.taken
    is taken_at_letters, and StandRest.saysAt is saysAt_at_letters at publicFourteen_at_head and
    samples_at_W_at_letters, the last at the empty list of further draws.

Limits.
  * The files beneath bear the library's label "NOT IN FRONT OF A LAW OVER COINS", and so do the
    statements of this file. What the label bars, and what counts as a law over coins, is set out in
    one place: Johnson/Bind/ForProver/FiveFieldsAt.lean, under "A limit on the coins". A bound on
    the probability that an honest proof is rejected is not a law over coins in that sense.
  * The statements are about the return of the base construction (hA), with its own randomness, not
    about the return of onlineMaker.
  * Each field is an implication whose premise is that ThrS (thread₃ h P R) (said₃ h P R) holds at
    position 2. That this invariant holds at any position at any run is not said. Where it does not
    hold, nothing is said.
  * h, hA, O and P are hypotheses, and P contains propositions. taken_at_letters and
    standRest_at_letters also assume the two instances Inhabited P5J.TS and Inhabited Desc.K14.St.
  * The statements hold for the full-size layout and for the format's second hash function,
    OnBytes.secondHashFunction, alone.
  * Nothing on the acceptance of a run, on completeness, on soundness or on hiding.

Built on.
  * takenAtTheRealTables (TakenAtTheRealTables.lean of this folder).
  * field_of_said_W (Johnson/Desc/ProofFile/Honest/K12/AtFile/WField.lean).
  * saysAt_at_letters (AtFullSide/K12/WSaysAtLetters.lean) and publicFourteen_at_head
    (AtFullSide/K12/WPublicFourteen.lean).
  * samples_at_W_at_letters (AtFullSide/K14/FivesAtTheLetters.lean).
-/
import AtFullSide.K14.FivesAtTheLetters
import AtFullSide.K12.WSaysAtLetters
import AtFullSide.K12.WPublicFourteen
import AtFullSide.K12.Part4.TakenAtTheRealTables
import AtFullSide.Honest.TheLettersLast
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WField
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WLaid
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WTable

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K12.Part4
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput readsBase)
open AtFullSide.Honest
open AtFullSide.Honest.TheLetters
open OnBytes (TableKey)
open VerifiableInference.Desc (Chain Place Strs K1.qAt)
open VerifiableInference.Desc.Third (S₃)
open ProofFile.Honest.K12.Light (ManyJob)
open ProofFile.Honest.K12.AtProof (randAt fourOf)
open ProofFile.Honest.K12.AtFile (TakenIs lastAt takenLast tableShared fixedShared StandRest
  field_of_said_W jobDoorU jobDoorO)
open ProofFile.Honest.K1 (LocB firstScriptAt)
open P2Law.ProofPlan (declProofFull)
open P5J (TS)

section AnyCount

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
  (r₁ n₀ : ℕ) (toCommon : LocB W₀ → Common W₀ IndexCommitterCoins TableKey) (J : TestJob (LocB W₀) Unit)
  (itemL t₁ t₂ : ℕ) (VdL : LocB W₀ → Prop) (RdL : ℕ → LocB W₀ → S₃ → Prop)
  (KpL : Place → S₃ → S₃ → Prop) (wL : LocB W₀)

/-- StandRest.taken at the tables of the proof file's description, with the number of the first
chain's rounds as a variable r₁ under the equation count, at a job M that jobAtFill returns. -/
theorem takenAtAnyCount (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (test : ℕ → TS → Option String) (carryX : ℕ → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : ℕ) (Vd : LocB W₀ → Prop) (Rd : ℕ → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀)
    (testOnU testOnOmega : TestJob (Common W₀ IndexCommitterCoins TableKey) X₀) (ownShared : X₀)
    {M : ManyJob (LocB W₀) Unit} (isTheJob : jobAtFill A.Z Np cF I S Op A.G = some M)
    (count : r₁ = ((P5J.F0T OnBytes.secondHashFunction A.Z Np cF).first.blocksInOrder.flatMap (·.rounds)).length)
    (sameIndex : ∀ v, (toCommon v).w₀ = v.w₀) (sameRandomness : ∀ v, (toCommon v).rc = v.rc)
    (Said : ℕ → Coins A.B → Mid (LocB W₀) Unit → Prop) :
    ∀ k st m E
      (c : RowCoins [(firstPart M.toRun.toTest : Part (LocB W₀) (LocB W₀) Unit),
        restPart M.toRun.toTest]),
      ThrS (lastAt (Zp := A.Z) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀ toCommon
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
          ML PL order ends wit r₁ n₀ toCommon
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
  subst count
  obtain ⟨M', isTheJob', taken⟩ := takenAtTheRealTables H N Mg ML PL order ends wit n₀ toCommon J
    itemL t₁ t₂ VdL RdL KpL wL h hA test carryX item n₁ n₂ b₀ Vd Rd Kp w testOnU testOnOmega
    ownShared sameIndex sameRandomness
  obtain rfl : M' = M := Option.some.inj (isTheJob'.symm.trans isTheJob)
  exact taken Said

end AnyCount

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St] {Z : VerifierAndGoals.PublicFiles}
  {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- firstRounds h equals the number of rounds that the sub-protocols of the first chain declare. -/
theorem firstRoundsAreTheFlatRounds :
    firstRounds h = (h.description.first.blocksInOrder.flatMap (·.rounds)).length := by
  show (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length = _
  unfold declsTo
  rw [List.take_length]

/-- StandRest.taken at thread₃, said₃ and P.ownMany. -/
theorem taken_at_letters
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    {O : OpenShared A} (P : OpenLast h O)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) :
    ∀ k st m E (c : RowCoins [(firstPart P.ownMany.toRun.toTest :
        Part (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit),
        restPart P.ownMany.toRun.toTest]),
      ThrS (thread₃ h P R) (said₃ h P R) 2 k st m E →
      lendRow A.B (A.B.rowsOf 2) (k.look 2) P.ownMany.p.place
        [(firstPart P.ownMany.toRun.toTest :
          Part (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit),
          restPart P.ownMany.toRun.toTest] 0 = .ok c →
      ∀ i (hi : i < takenLast.length), TakenIs (thread₃ h P R) k m
        (P.ownMany.toRun.toTest.trees₀ m.st.input (frontOf m)
          (restCoins P.ownMany.toRun.toTest c.2.1).mem
          (P.ownMany.toRun.toTest.first m.st.input (frontOf m)
            (restCoins P.ownMany.toRun.toTest c.2.1)))
        i takenLast[i] :=
  takenAtAnyCount (Wt := WtF) (I := matrixInput) (S := OnBytes.HonestTrace.Sz.ref)
    (Op := openHonest) A.H _ _ _ _ (fun s => OnBytes.Means.InOrder s.st) _ _ (firstRounds h)
    (lastFront h) (toCommon (A := A)) P.ownMany.toRun.toTest _ _ _ _ _ _ _ h.head hA
    (fun _ _ => none) (fun _ _ _ _ => True) 0 0 0 0 (fun _ => True) (fun _ _ _ => True)
    (fun _ _ _ => True) R.own
    (jobDoorU (X₀ := Unit) A.Z h.places (sharedBlocks h) A.H.storedWords
      (readsBase h).weights (readsBase h).rand).toRun.toTest
    (jobDoorO (X₀ := Unit) A.Z h.places
      ((fourOf h.places).O.getD (fourOf h.places).U) (sharedBlocks h) (readsBase h).weights
      (readsBase h).rand).toRun.toTest
    () P.ownIsTheFilling (firstRoundsAreTheFlatRounds h) (fun _ => rfl) (fun _ => rfl)
    (said₃ h P R)

/-- StandRest at thread₃, said₃ and P.ownMany: the three implications from the invariant in front of
the second chain's proximity test. -/
theorem standRest_at_letters
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    {O : OpenShared A} (P : OpenLast h O)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) :
    StandRest (Zp := A.Z) (Np := h.places) (cF := h.firstChain) (thread₃ h P R) (said₃ h P R)
      P.ownMany := by
  obtain ⟨layO, Q⟩ := AtFullSide.K12.publicFourteen_at_head h matrixInput
    OnBytes.HonestTrace.Sz.ref openHonest hA P.ownIsTheFilling
  exact
    { field := field_of_said_W _ _ 2 (fun _ _ s => s.1)
      taken := taken_at_letters h hA P R
      saysAt := fun k st m E c u lent =>
        (AtFullSide.K12.saysAt_at_letters h hA P R
          (fun _ _ _ _ stand => AtFullSide.K14.samples_at_W_at_letters h P R stand [])
          Q.tenantsApart Q.place Q.plan Q.covers Q.countAtFive Q.dueShared Q.rowBase Q.rowExtension
          Q.firstTrees Q.tenantOmega Q.point Q.shapeAt199 Q.sharedShapeOmega Q.pointInFront
          k st m E c u lent).1 }

end AtFullSide.K12.Part4

#print axioms AtFullSide.K12.Part4.firstRoundsAreTheFlatRounds
#print axioms AtFullSide.K12.Part4.takenAtAnyCount
#print axioms AtFullSide.K12.Part4.taken_at_letters
#print axioms AtFullSide.K12.Part4.standRest_at_letters
