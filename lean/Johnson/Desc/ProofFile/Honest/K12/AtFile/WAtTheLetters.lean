-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WAtTheLetters.lean: the holes of `OpenLast` (AtFullSide/Honest/TheLettersLast.lean),
and the five statements at the last chain's proximity test at `thread₃` and `said₃`.

  `jobLast`        the filling's job: the one `jobAtFill` returns
  `openLast`       the value: the filling's job, the depths by `lastLetters_depths` and `depthsAtW`
  `rides_three`    no rider of the last chain speaks at border 3
  `five_at_thread₃`   `FiveAt` at number 2 at `thread₃`, `said₃`, from the clause `saysAt` alone

Limits.
- NOT IN FRONT OF A LAW OVER COINS: the thread's pair is a premise, the five its ends.
- AT THE FILLING, NOT READ THROUGH.
- That a stand is reached is not said; where none is, the five say nothing.
- Nothing on completeness of the whole chain, on soundness or on what is hidden.
-/
import AtFullSide.Honest.TheLettersLast
import AtFullSide.K12.Part4.DepthsAtW
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WAtRealTables
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WField
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open AtPublicFiles.AtFiles
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput readsBase)
open AtFullSide.Honest
open AtFullSide.Honest.TheLetters
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place K1.qAt)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Last (lastPlaces)
open ProofFile.Honest.K12.Light (ManyJob)
open ProofFile.Honest.K12.AtProof (fourOf)
open AtFullSide.K12 (jobAtFill job_at_filling)
open ToldDesc (ownAt)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St] {Z : VerifierAndGoals.PublicFiles}
  {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
    (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)

include hA in
/-- The filling returns its job. -/
theorem job_exists : ∃ M, jobAtFill A.Z h.places h.firstChain matrixInput OnBytes.HonestTrace.Sz.ref
    openHonest A.G = some M ∧ A.H.second =
      [(proverSideOfProximityTest M.toRun.toTest : Placed (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) _ Unit).needsField] :=
  job_at_filling h.head matrixInput OnBytes.HonestTrace.Sz.ref openHonest hA

/-- **The filling's job.** -/
def jobLast : ManyJob (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit := Classical.choose (job_exists h hA)

/-- **The value of `OpenLast`.** -/
def openLast (O : OpenShared A) : OpenLast h O where
  ownMany := jobLast h hA
  ownIsTheFilling := (Classical.choose_spec (job_exists h hA)).1
  depths := by
    obtain ⟨hM, hs⟩ := Classical.choose_spec (job_exists h hA)
    obtain ⟨hp, -, -, -, -⟩ := job_facts h.head.toAtMg _ _ _ _ _ _ _ _ _ hM
    exact lastLetters_depths h (firstRounds h) (lastFront h) (toCommon (A := A))
      (first h).script.table (later (h := h) O).table (jobLast h hA).toRun.toTest () hp
      (fun a ha => by
        have e : (jobLast h hA).toRun.toTest.p.nums.stages =
            H2K.Member.piWFull.nums.stages := by
          have hp' : (jobLast h hA).p = (fourOf h.places).W := hp
          show (jobLast h hA).p.nums.stages = _
          rw [hp']
          exact congrArg (·.stages) (ProofFile.Honest.K12.Light.nums_head_W h.head.toAtMg)
        rw [e] at ha
        exact of_decide_eq_true (List.all_eq_true.1 hk_W a ha))
      (rest_at_filling h.head matrixInput OnBytes.HonestTrace.Sz.ref openHonest hA hs hp)
      (AtFullSide.K12.Part4.depthsAtW h.head hA _ _ _ _ _ _ _)

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **No rider of the last chain speaks at border 3.** -/
theorem rides_three {W : Type} (p : VerifiableInference.Desc.Third.P₁₄) (places : H2U.Places4) (w : W)
    (s : S₃) : ridersOf (ProofFile.Honest.K14.doorRider W p :: lastRiders places []) 3 w s := by
  intro c hc _ hh
  simp only [lastRiders, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · have e : (3 : ℕ) ≤ 0 := hh
    omega
  · have e : (3 : ℕ) ≤ 0 := hh
    omega
  · have e : (3 : ℕ) ≤ 1 := hh
    omega

/-- The rounds of a list, two ways. -/
theorem firstRounds_eq : firstRounds h = (h.description.first.blocksInOrder.flatMap (·.rounds)).length := by
  show (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length = _
  unfold declsTo
  rw [List.take_length]

/-- **The five at `thread₃` and `said₃`.** What stays: the clause `saysAt`. -/
theorem five_at_thread₃ (O : OpenShared A) (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit)
    (hS : ∀ k st m E (c : RowCoins [(firstPart (jobLast h hA).toRun.toTest :
          Part (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit),
        restPart (jobLast h hA).toRun.toTest]),
      ThrS (thread₃ h (openLast h hA O) R) (said₃ h (openLast h hA O) R) 2 k st m E →
      lendRow A.B (A.B.rowsOf 2) (k.look 2) (jobLast h hA).p.place
        [(firstPart (jobLast h hA).toRun.toTest :
          Part (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit),
          restPart (jobLast h hA).toRun.toTest] 0 = .ok c →
      ∃ ws, SaysLeft (jobLast h hA) m.st.input (frontOf m)
        (restCoins (jobLast h hA).toRun.toTest c.2.1) st ws)
    (fl : ℕ → S₃ → List Fmt.Drawn → Option String) :
    FiveAt (thread₃ h (openLast h hA O) R) (said₃ h (openLast h hA O) R) fl 2 := by
  obtain ⟨M, hM, key⟩ := five_at_real_tables (Wt := WtF) (I := matrixInput)
    (S := OnBytes.HonestTrace.Sz.ref) (Op := openHonest) h.head hA
    (fun _ _ => none) (fun _ _ _ _ => True) 0 0 0 0 (fun _ => True) (fun _ _ _ => True)
    (fun _ _ _ => True) R.own
    (jobDoorU (X₀ := Unit) A.Z h.places (sharedBlocks h) A.H.storedWords
      (readsBase h).weights (readsBase h).rand).toRun.toTest
    (jobDoorO (X₀ := Unit) A.Z h.places
      ((fourOf h.places).O.getD (fourOf h.places).U) (sharedBlocks h) (readsBase h).weights
      (readsBase h).rand).toRun.toTest
  obtain rfl : M = jobLast h hA := Option.some.inj
    (hM.symm.trans (Classical.choose_spec (job_exists h hA)).1)
  refine key _ _ _ _ _ _ (firstRounds h) (lastFront h) (toCommon (A := A)) _ _ _ _ _ _ _
    (said₃ h (openLast h hA O) R) (firstRounds_eq h) (fun _ => rfl) (fun _ => rfl) (fillZ_is _ _) ?_ ?_
    ?_ ?_ fl
  · show _ = (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length ++
      declsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length).length
    rw [List.length_append]
  · exact field_of_said_W _ _ 2 fun k m g => g.1
  · exact hS
  · intro k s m E ds y cols s' _ _ _
    refine ⟨rides_three _ _ _ _, fun q hq => ?_⟩
    have e : lastPlaces[2]? = some ⟨3, none, 2, .K12⟩ := rfl
    obtain rfl := Option.some.inj (hq.symm.trans e)
    show (if (⟨3, none, 2, .K12⟩ : Place) = ⟨3, none, 0, .K14⟩ then _ else _)
    rw [if_neg (by decide)]
    refine ⟨fun hh => ?_, trivial⟩
    rcases hh with hh | hh <;> cases hh

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.firstRounds_eq
#print axioms ProofFile.Honest.K12.AtFile.five_at_thread₃
#print axioms ProofFile.Honest.K12.AtFile.job_exists
#print axioms ProofFile.Honest.K12.AtFile.jobLast
#print axioms ProofFile.Honest.K12.AtFile.openLast
#print axioms ProofFile.Honest.K12.AtFile.rides_three
