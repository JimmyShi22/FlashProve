-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/Live.lean: the family's test, and the plan of the branch that refuses. One
named part of `VerifierAndGoals.theDescription` (Description.lean), in a file of its own.
State: the true text, asked at whatever sits in the seats (Plan.lean, KeyFold.lean, ProofFold.lean).
`protocolDataWellFormedAt o`: the plan's seat and both files' seats give a value, and `dataWellFormedAtFullSizeDepth` at these: both data
stand at the frame's depth (`frS.P.T.a`: the frame reads the data at a depth of its own and tests
nothing); `sizeNumbersFitAtPlan` (Johnson/Flat/Dec/ClosedAtPlan.lean): the frame's whole test on numbers at the
data that are laid, with `theQueries` = 2^20; `listsFull`: none of the six lists of rounds is empty.
Each seat is asked once a call. `theLiveAt_made`, `theLiveAt_of`, `theLiveAt_fit`: what its yes
gives.
`protocolDataWellFormed`, `theDeadPlan`, `theListsFull`: these at the second hash function: the names of
which the laws speak. `theLive_made`, `theLive_depth`, `theLive_frame`, `theLive_full`: its yes
gives
each. `theLive_fit`: and the three tests that `tAt` asks. `theLive_no_of_plan`, `theLive_no_of_key`,
`theLive_no_of_proof`: where a seat refuses it says no. `theDeadPlanAt o`: the plan's values with
both
binding trees' depths 0. `deadD_eq`: the empty data here and in Johnson/Flat/Dec/DeadAtWritten.lean
are one text.
Why. Where a seat refuses the data fall back to empty lists, and the frame's test says yes at these.
Whether a public file in scope can make any of the added tests say no is not shown.
They can only make the verifier refuse more.
Limits. What it says at any files hangs on what sits in the seats: to be evaluated anew at each turn
of a seat. The entry file's decision (LinkDec.lean) is not asked whether it is the one that says no
to all: so a yes of this test is no sign that the verifier accepts anything. It is no test of
the scope: whether the three public files are the release's is asked by `VerifierAndGoals.InScope`, which the
verifier asks beside it, and not here.

-/
import Johnson.Goal.Tie.DescriptionOfData
import Johnson.Goal.Description.Plan
import Johnson.Goal.Description.KeyFold
import Johnson.Goal.Description.ProofFold
import Johnson.Flat.Dec.ClosedAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Run
open _root_.Iop (Dig)
open LPFD.Full (XF GF sBG sTG saltG KF FsAtR)
open PV.EntryFive (dsF xsF)

open FlashProve (roundsDataFit fit3_iff emptyRoundsData)

/-- The bound on the compiled verifier's typed queries. -/
def theQueries : ℕ := 2 ^ 20

/-- None of the six lists of rounds is empty. Where a seat refuses the data fall back to empty
  lists, and the frame's test says yes at these. Whether a public file in scope can make this test
  say no is not shown. -/
def listsFull (DK DP : WholeD) : Bool :=
  !([DK.ds₁.length, DK.ds₂.length, DK.ds₃.length, DP.ds₁.length, DP.ds₂.length, DP.ds₃.length].any
      (· == 0))

/-- The frame's whole test on numbers, and no list empty, as a function of the data. -/
def dataWellFormedApartFromDepth (G : FilesParameters XF RecFull) (DK DP : WholeD) : Bool := sizeNumbersFitAtPlan KF theQueries G DK DP &&
    listsFull DK DP

/-- Both data stand at the frame's depth, and `dataWellFormedApartFromDepth`. -/
def dataWellFormedAtFullSizeDepth (G : FilesParameters XF RecFull) (DK DP : WholeD) : Bool :=
  DK.a == frS.P.T.a && DP.a == frS.P.T.a && dataWellFormedApartFromDepth G DK DP

def protocolDataWellFormedAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : Bool :=
  match filesParametersOrRefusalAt o Zk with
  | .error _ => false
  | .ok G =>
    match keyDataAndDecisionOrRefusalAt o Zk with
    | .error _ => false
    | .ok K =>
      match proofDataAndDecisionOrRefusalAt o Zk with
      | .error _ => false
      | .ok P => dataWellFormedAtFullSizeDepth G K.1 P.1

/-- Where the plan's seat refuses it says no. -/
theorem theLiveAt_no_of_plan (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) (e : String)
    (h : filesParametersOrRefusalAt o Zk = .error e) : protocolDataWellFormedAt o Zk = false := by
  unfold protocolDataWellFormedAt
  rw [h]

/-- Where the key file's seat refuses it says no. -/
theorem theLiveAt_no_of_key (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) (e : String)
    (h : keyDataAndDecisionOrRefusalAt o Zk = .error e) : protocolDataWellFormedAt o Zk = false := by
  unfold protocolDataWellFormedAt
  rw [h]
  cases filesParametersOrRefusalAt o Zk <;> rfl

/-- Where the proof file's seat refuses it says no. -/
theorem theLiveAt_no_of_proof (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) (e : String)
    (h : proofDataAndDecisionOrRefusalAt o Zk = .error e) : protocolDataWellFormedAt o Zk = false := by
  unfold protocolDataWellFormedAt
  rw [h]
  cases filesParametersOrRefusalAt o Zk <;> cases keyDataAndDecisionOrRefusalAt o Zk <;> rfl

/-- Its yes gives that both seats give a value, and the test at the two data. -/
theorem theLiveAt_made (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) (h : protocolDataWellFormedAt o Zk = true) :
    ∃ K P, filesParametersOrRefusalAt o Zk = .ok (thePlanAt o Zk) ∧ keyDataAndDecisionOrRefusalAt o Zk = .ok K ∧
      proofDataAndDecisionOrRefusalAt o Zk = .ok P ∧ dataWellFormedAtFullSizeDepth (thePlanAt o Zk) K.1 P.1 = true := by
  unfold protocolDataWellFormedAt at h
  cases hG : filesParametersOrRefusalAt o Zk with
  | error e => rw [hG] at h; cases h
  | ok G =>
    rw [hG] at h
    rw [thePlanAt_ok hG]
    cases hK : keyDataAndDecisionOrRefusalAt o Zk with
    | error e => rw [hK] at h; cases h
    | ok K =>
      rw [hK] at h
      cases hP : proofDataAndDecisionOrRefusalAt o Zk with
      | error e => rw [hP] at h; cases h
      | ok P => rw [hP] at h; exact ⟨K, P, rfl, rfl, rfl, h⟩

/-- The test at the data that are laid. -/
theorem theLiveAt_of (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) (h : protocolDataWellFormedAt o Zk = true) :
    dataWellFormedAtFullSizeDepth (thePlanAt o Zk) (theKeyDataAt o Zk) (theProofDataAt o Zk) = true := by
  obtain ⟨K, P, _, hK, hP, hl⟩ := theLiveAt_made o Zk h
  rw [theKeyDataAt_ok hK, theProofDataAt_ok hP]
  exact hl

/-- Its yes gives the frame's test's yes. -/
theorem theLiveAt_frame (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) (h : protocolDataWellFormedAt o Zk = true) :
    sizeNumbersFitAtPlan KF theQueries (thePlanAt o Zk) (theKeyDataAt o Zk) (theProofDataAt o Zk) = true := by
  have hl := theLiveAt_of o Zk h
  simp only [dataWellFormedAtFullSizeDepth, dataWellFormedApartFromDepth, Bool.and_eq_true] at hl
  exact hl.2.1

theorem theLiveAt_fit (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) (h : protocolDataWellFormedAt o Zk = true) :
    roundsDataFit (theKeyDataAt o Zk) (theProofDataAt o Zk) = true :=
  (fit3_iff _ _).2 (frameFitFullD_three (show sizeNumbersFitAtFullSize _ _ _ _ _ _ _ _ = true from
      theLiveAt_frame o Zk h) frS.P.T.a)

def theDeadPlanAt (o : VerifierAndGoals.SecondHashFunctionType) (Zk : OnBytes.K.Pub) : FilesParameters XF RecFull :=
  (thePlanAt o Zk).noDepth

/-! ## At the second hash function -/

def protocolDataWellFormed (Zk : OnBytes.K.Pub) : Bool := protocolDataWellFormedAt OnBytes.secondHashFunction Zk

def theListsFull (Zk : OnBytes.K.Pub) : Bool := listsFull (theKeyData Zk) (theProofData Zk)

def theDeadPlan (Zk : OnBytes.K.Pub) : FilesParameters XF RecFull := theDeadPlanAt OnBytes.secondHashFunction Zk

/-- Where the plan's seat refuses it says no. -/
theorem theLive_no_of_plan (Zk : OnBytes.K.Pub) (e : String) (h : thePlanLaid Zk = .error e) :
    protocolDataWellFormed Zk = false := theLiveAt_no_of_plan _ Zk e h

/-- Where the key file's seat refuses it says no. -/
theorem theLive_no_of_key (Zk : OnBytes.K.Pub) (e : String) (h : theKeyLaid Zk = .error e) :
    protocolDataWellFormed Zk = false := theLiveAt_no_of_key _ Zk e h

/-- Where the proof file's seat refuses it says no. -/
theorem theLive_no_of_proof (Zk : OnBytes.K.Pub) (e : String) (h : theProofLaid Zk = .error e) :
    protocolDataWellFormed Zk = false := theLiveAt_no_of_proof _ Zk e h

/-- Its yes gives that both seats give a value, and the test at the two data. -/
theorem theLive_made (Zk : OnBytes.K.Pub) (h : protocolDataWellFormed Zk = true) :
    ∃ K P, thePlanLaid Zk = .ok (thePlan Zk) ∧ theKeyLaid Zk = .ok K ∧ theProofLaid Zk = .ok P ∧
      dataWellFormedAtFullSizeDepth (thePlan Zk) K.1 P.1 = true := theLiveAt_made _ Zk h

/-- The test at the data that are laid. -/
theorem theLive_of (Zk : OnBytes.K.Pub) (h : protocolDataWellFormed Zk = true) :
    dataWellFormedAtFullSizeDepth (thePlan Zk) (theKeyData Zk) (theProofData Zk) = true := theLiveAt_of _ Zk h

/-- Its yes gives that both files' data stand at the frame's depth. -/
theorem theLive_depth (Zk : OnBytes.K.Pub) (h : protocolDataWellFormed Zk = true) :
    (theKeyData Zk).a = frS.P.T.a ∧ (theProofData Zk).a = frS.P.T.a := by
  have hl := theLive_of Zk h
  simp only [dataWellFormedAtFullSizeDepth, Bool.and_eq_true, beq_iff_eq] at hl
  exact hl.1

/-- Its yes gives the frame's test's yes. -/
theorem theLive_frame (Zk : OnBytes.K.Pub) (h : protocolDataWellFormed Zk = true) :
    sizeNumbersFitAtPlan KF theQueries (thePlan Zk) (theKeyData Zk) (theProofData Zk) = true :=
  theLiveAt_frame _ Zk h

/-- And that no list is empty. -/
theorem theLive_full (Zk : OnBytes.K.Pub) (h : protocolDataWellFormed Zk = true) : theListsFull Zk = true := by
  have hl := theLive_of Zk h
  simp only [dataWellFormedAtFullSizeDepth, dataWellFormedApartFromDepth, Bool.and_eq_true] at hl
  exact hl.2.2

theorem theLive_fit (Zk : OnBytes.K.Pub) (h : protocolDataWellFormed Zk = true) : roundsDataFit (theKeyData Zk)
    (theProofData Zk) = true := theLiveAt_fit _ Zk h

/-- The empty data here and in Johnson/Flat/Dec/DeadAtWritten.lean are one text. -/
theorem deadD_eq : emptyRoundsData = deadW := rfl

end FlashProve
