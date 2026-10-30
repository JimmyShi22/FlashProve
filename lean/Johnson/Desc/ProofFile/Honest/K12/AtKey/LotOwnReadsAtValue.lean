-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnReadsAtValue.lean: THE PREMISES ON THE PARTS OF THE KEY FILE's OWN TEST, AT THE SENDERS THAT
THE OFFLINE PROVER's VALUE LAYS: `withStoredColumnsAndPlan` over `withSendingsAndLookups` (E2E/KeyArgumentsAt.lean, E2E/KeyFifteen.lean), in scope:
`SendersReadInFront` (LotOwnWords.lean), `SendersPlansAlike` (LotOwnAlike.lean) and the two sendings' places.

  `writtenLookups`, `writtenFace`, `writtenBase`   the two lookups' faces and the rounds in front of them, at the written sizes
  `face_in_scope`, `base_in_scope`                in scope the value's `faceAt`, `baseAt` are these
  `written_key_points_read`                       the last key points of both lookups read rounds below 18,848. By the kernel
  `written_key_points_read_not_sooner`, `…_at_first`   controls: a lookup's do not lie below that lookup's own first round: so neither
                                                  face is without a level, and the line above is idle at neither
  `key_points_read_in_front`                      so `keyPoints` reads the first 18,848 challenges alone
  `batching_numbers_in_scope`                     `battAt` is 18,828, 18,829, 18,830
  `written_columns`, `written_columns_tight`      18,830 + the matrix's column variables ≤ 18,848; a control: not ≤ 18,847
  `weights_read_in_front_at_value`                `WeightsReadInFront` (LotOwnSamplesFirstReads.lean) at the value's letters
  `place_of_verifiers_index_masks_plan`, `place_of_verifiers_vector_w_plan`   the places of the verifier's own two plans
  `wJob_of_message`, `vector_w_job_at_value`      W's sending at the value is `wJob`'s job, not the stand-in
  `senders_read_in_front_at_value`                `SendersReadInFront`
  `plans_alike_at_value`                          `SendersPlansAlike`
  `place_of_index_masks_at_value`, `place_of_vector_w_at_value`   the two places

By what. `six_sourced` (E2E/KeyShapeFullSourced.lean), `start_named₁` (E2E/KeyPlacesNamed.lean), `public_samples`
(OwnSamplesAt.lean), `ownSenders_of_plans` (OwnSendersAt.lean), `key_point_of_front` (LotOwnKeyPointsRead.lean),
`wJob_reads_in_front` (LotOwnSamplesFirstReads.lean).

Limits.
- In scope, at the full size. General in the letters that the value leaves: K', f, inR, d, weights, coins.
- WHICH challenges are read, not WHAT is made of them: that `keyPoints` is the verifier's point is not said here.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnKeyPointsRead
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnSamplesFirstReads
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnSamplesFirstStand
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnSendersAt
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnSamplesAt
import E2E.KeyArgumentsAt
import E2E.KeyPlacesNamed
import E2E.KeyShapeFullSourced

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes.Params (OneTime)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K3 (faceOfLkp)
open VerifiableInference.Desc.Key (Source LaterPlaces Pieces pieces groupsTold rootsBefore rootsAt
  lastSendRound sendingPar)
open ProofFile.Honest.K1 (SendJob Ride)
open Lk6.AtPlan (keyX)
open AtPublicFiles.AtFiles (KeySourced SF)
open AtPublicFiles.AtFiles.HonestTerm (withStoredColumnsAndPlan)
open AtPublicFiles.Key (wJob BattAt)
open AtPublicFiles.KeyBook (fullFirst startIn lookPlace start_named₁ rideW)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.KeyValues (WitK withSendingsAndLookups indexMaskSending batchedRowsSending keyPoints battAt faceAt baseAt placeAt blocksOf oneOf
  matrixEntryOf firstW lookAt)

/-- The two lookups' public records at the written sizes. -/
def writtenLookups : List OnBytes.Lkp.Public := OnBytes.Wf.lookupsOf keyX (OnBytes.Wf.matrixOf SF)

/-- Lookup i's face at the written sizes. -/
def writtenFace (i : ℕ) : ProofFile.Honest.K3.LFace := faceOfLkp (writtenLookups.getD i default)

/-- The rounds of the first chain in front of lookup i, at the written sizes. -/
def writtenBase (i : ℕ) : ℕ := (startIn fullFirst (lookPlace i)).getD 0

/-- There are two. By the kernel. -/
theorem written_lookups_count : writtenLookups.length = 2 := by decide +kernel

/-- The face of the default record has no part. -/
theorem default_face_has_no_part : (faceOfLkp default).parts = [] := rfl

/-- **The last key points of both lookups read rounds below 18,848.** By the kernel. -/
theorem written_key_points_read :
    (List.range 2).all (fun i => keyPointsReadBelow (writtenFace i) (writtenBase i) 18848) = true := by
  decide +kernel

/-- Control: the second lookup's do not lie below that lookup's own first round. -/
theorem written_key_points_read_not_sooner :
    keyPointsReadBelow (writtenFace 1) (writtenBase 1) (writtenBase 1) = false := by
  decide +kernel

/-- Control: nor the first lookup's below its own. -/
theorem written_key_points_read_not_sooner_at_first :
    keyPointsReadBelow (writtenFace 0) (writtenBase 0) (writtenBase 0) = false := by
  decide +kernel

/-- At every number of a lookup: beyond the two the face has no part. -/
theorem written_key_points_read_at (i : ℕ) :
    keyPointsReadBelow (writtenFace i) (writtenBase i) 18848 = true := by
  by_cases hi : i < 2
  · exact List.all_eq_true.1 written_key_points_read i (List.mem_range.2 hi)
  · have e : writtenFace i = faceOfLkp default := by
      unfold writtenFace
      rw [List.getD_eq_default _ _ (by have := written_lookups_count; omega)]
    unfold keyPointsReadBelow
    rw [e, default_face_has_no_part]
    rfl

/-- Where the batching begins, at the written sizes. -/
theorem written_batching_start :
    startIn fullFirst (⟨1, none, pieces.batt, .K13⟩ : Place) = some 18828 := by decide +kernel

/-- The column variables' rounds end where W's sending begins. By the kernel. -/
theorem written_columns : 18830 + (OnBytes.Wf.matrixOf SF).kCol ≤ 18848 := by decide +kernel

/-- Control: not one round sooner. -/
theorem written_columns_tight : ¬ 18830 + (OnBytes.Wf.matrixOf SF).kCol ≤ 18847 := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}

/-- In scope the value's face of lookup i is the written one. -/
theorem face_in_scope (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) (i : ℕ) :
    faceAt Xs i = writtenFace i := by
  have h6 := AtPublicFiles.AtFiles.Full.six_sourced hs scope
  have hl : Xs.Y.k.oneTime.lin = SF := h6.lin
  have hr : Xs.Y.k.oneTime.ranges = keyX := h6.ranges
  unfold faceAt lookAt writtenFace writtenLookups VerifiableInference.Desc.Key.lookupsOf
  rw [hl, hr]

/-- In scope the value's count of rounds in front of lookup i is the written one. -/
theorem base_in_scope (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) (i : ℕ) :
    baseAt Xs Nr i = writtenBase i := by
  have g := start_named₁ scope hs.named (placeAt i)
  have g' : roundsInFront (blocksOf Xs Nr) (placeAt i) = startIn fullFirst (placeAt i) := g
  unfold baseAt writtenBase
  rw [g']
  rfl

/-- **`keyPoints` reads the first 18,848 challenges alone**, in scope. -/
theorem key_points_read_in_front (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    {h h' : List Fmt.Drawn} (e : h.take 18848 = h'.take 18848) :
    keyPoints Xs Nr h = keyPoints Xs Nr h' := by
  funext i p
  unfold keyPoints
  rw [face_in_scope hs scope i, base_in_scope hs scope i,
    key_point_of_front (written_key_points_read_at i) e p]

/-- **The batching's three numbers**, in scope. -/
theorem batching_numbers_in_scope (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) :
    battAt Xs Nr = ⟨18828, 18829, 18830⟩ := by
  have g := start_named₁ scope hs.named (⟨1, none, pieces.batt, .K13⟩ : Place)
  have g' : roundsInFront (blocksOf Xs Nr) (⟨1, none, pieces.batt, .K13⟩ : Place) = some 18828 :=
    g.trans written_batching_start
  unfold battAt
  rw [g']
  rfl

/-- **`WeightsReadInFront` at the value's letters**, at the 18,848 challenges in front of W's sending. -/
theorem weights_read_in_front_at_value (hs : KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) :
    WeightsReadInFront (oneOf Xs) (keyPoints Xs Nr) (battAt Xs Nr) 18848 := by
  have hl : (oneOf Xs).lin = SF := (AtPublicFiles.AtFiles.Full.six_sourced hs scope).lin
  rw [batching_numbers_in_scope hs scope]
  refine ⟨?_, ?_, ?_, fun h h' e => key_points_read_in_front hs scope e⟩
  · show (18828 : ℕ) < 18848
    omega
  · show (18829 : ℕ) < 18848
    omega
  · show 18830 + (OnBytes.Wf.matrixOf (oneOf Xs).lin).kCol ≤ 18848
    rw [hl]
    exact written_columns

/-- The place of the verifier's own plan of the index masks' sending. -/
theorem place_of_verifiers_index_masks_plan (Xs : Source) :
    (Johnson.RunOne.KeySendGood.parIdx Xs).place = ⟨1, none, 1, .K1⟩ := rfl

/-- The place of the verifier's own plan of W's sending. -/
theorem place_of_verifiers_vector_w_plan (Xs : Source) (msg : Array OnBytes.OracleNotice) :
    (Johnson.RunOne.KeySendGood.parW Xs msg).place = ⟨1, none, 14, .K1⟩ := rfl

/-- Where the shape has a message W, `wJob` returns a job with the sending's own plan and the given ride. -/
theorem wJob_of_message {W X : Type} (entry : W → ℕ → ℕ → OnBytes.Slice.GF) (one : OneTime)
    (N : Pieces) (groups : List (List ℕ)) (first : ℕ) (ride : ℕ → Option Ride)
    (points : List Fmt.Drawn → ℕ → ℕ → List OnBytes.E) (a : BattAt)
    {msg : Array OnBytes.OracleNotice} (hm : OnBytes.linMessageW one.lin = some msg) :
    ∃ J : SendJob W X, wJob entry one N groups first ride points a = some J ∧
      J.P = sendingPar one N.w "W and what rides with it" msg groups ∧ J.ride = ride := by
  unfold wJob
  rw [hm]
  exact ⟨_, rfl, rfl, rfl⟩

variable {W₀ Rc : Type}

/-- **W's sending at the value is `wJob`'s job**, in scope: not the stand-in. -/
theorem vector_w_job_at_value {X : Type} (f : W₀ → Weights)
    {msg : Array OnBytes.OracleNotice} (hm : OnBytes.linMessageW Xs.Y.k.oneTime.lin = some msg) :
    ∃ (J : SendJob (In1 W₀ Rc) X) (groups : List (List ℕ)),
      batchedRowsSending f Xs Nr = J ∧
      wJob (matrixEntryOf f) (oneOf Xs) pieces groups (firstW Xs) rideW (keyPoints Xs Nr) (battAt Xs Nr) =
        some J ∧
      J.P = Johnson.RunOne.KeySendGood.parW Xs msg ∧ J.ride = rideW := by
  obtain ⟨J, hJ, hP, hr⟩ := wJob_of_message (W := In1 W₀ Rc) (X := X) (matrixEntryOf f) (oneOf Xs) pieces
    (groupsTold Xs.Y.told.1 (rootsBefore Xs.Y.D.1 (lastSendRound Xs.Y.D.1))
      (rootsAt Xs.Y.D.1 (lastSendRound Xs.Y.D.1)))
    (firstW Xs) rideW (keyPoints Xs Nr) (battAt Xs Nr) hm
  refine ⟨J, _, ?_, hJ, ?_, hr⟩
  · unfold batchedRowsSending
    rw [hJ]
    rfl
  · rw [hP]
    rfl

section Value
variable (K' : KeyParts W₀ Rc Unit Unit WitK) (f : W₀ → Weights) (inR : W₀ → Bool) (d : W₀)
  (weights : W₀ → Weights) (coins : Rc → ℕ → TableRand)

/-- **`SendersReadInFront` at the offline value's senders**, at the full size's count in front of W's sending, in scope. It reads
no count of the whole first chain: that number is a letter. -/
theorem senders_read_in_front_at_value (hs : KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) (challengesOfFirstChain : ℕ) :
    SendersReadInFront (withStoredColumnsAndPlan Xs Pl (withSendingsAndLookups K' Xs Nr f inR d) weights coins)
      (numbersAtFullSize challengesBeforeVectorWAtFullSize challengesOfFirstChain) where
  indexMasks := fun _ _ _ _ => rfl
  vectorW := by
    obtain ⟨bw, msg, -, hm, -, -, -⟩ := public_samples hs scope
    obtain ⟨J, groups, hk, hJ, -, -⟩ := vector_w_job_at_value (Rc := Rc) (X := Unit) (Nr := Nr) f hm
    intro x fr fr' e
    show (batchedRowsSending f Xs Nr).data x fr = (batchedRowsSending f Xs Nr).data x fr'
    rw [hk]
    exact wJob_reads_in_front _ _ _ _ _ _ _ _ 18848 (weights_read_in_front_at_value hs scope) hJ x fr
      fr' e
  point := rfl

/-- **`SendersPlansAlike` at the offline value's senders**, in scope. -/
theorem plans_alike_at_value (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) :
    SendersPlansAlike (withStoredColumnsAndPlan Xs Pl (withSendingsAndLookups K' Xs Nr f inR d) weights coins) := by
  obtain ⟨bw, msg, -, hm, -, -, -⟩ := public_samples hs scope
  obtain ⟨J, groups, hk, -, hP, hr⟩ := vector_w_job_at_value (Rc := Rc) (X := Unit) (Nr := Nr) f hm
  refine plansAlike_of_ownSenders (ownSenders_of_plans hs scope hm rfl rfl ?_ ?_ rfl)
  · show (batchedRowsSending f Xs Nr).P = _
    rw [hk]
    exact hP
  · show (batchedRowsSending f Xs Nr).ride = _
    rw [hk]
    exact hr

/-- The place of the index masks' sending at the value. -/
theorem place_of_index_masks_at_value :
    (withStoredColumnsAndPlan Xs Pl (withSendingsAndLookups K' Xs Nr f inR d) weights coins).idx.P.place =
      ⟨1, none, 1, .K1⟩ := rfl

/-- The place of W's sending at the value, in scope. -/
theorem place_of_vector_w_at_value (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) :
    (withStoredColumnsAndPlan Xs Pl (withSendingsAndLookups K' Xs Nr f inR d) weights coins).w.P.place =
      ⟨1, none, 14, .K1⟩ := by
  obtain ⟨bw, msg, -, hm, -, -, -⟩ := public_samples hs scope
  obtain ⟨J, groups, hk, -, hP, -⟩ := vector_w_job_at_value (Rc := Rc) (X := Unit) (Nr := Nr) f hm
  show (batchedRowsSending f Xs Nr).P.place = _
  rw [hk, hP]
  rfl

end Value

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.writtenLookups
#print axioms ProofFile.Honest.K12.AtKey.writtenFace
#print axioms ProofFile.Honest.K12.AtKey.writtenBase
#print axioms ProofFile.Honest.K12.AtKey.written_lookups_count
#print axioms ProofFile.Honest.K12.AtKey.default_face_has_no_part
#print axioms ProofFile.Honest.K12.AtKey.written_key_points_read
#print axioms ProofFile.Honest.K12.AtKey.written_key_points_read_not_sooner
#print axioms ProofFile.Honest.K12.AtKey.written_key_points_read_not_sooner_at_first
#print axioms ProofFile.Honest.K12.AtKey.written_key_points_read_at
#print axioms ProofFile.Honest.K12.AtKey.written_batching_start
#print axioms ProofFile.Honest.K12.AtKey.written_columns
#print axioms ProofFile.Honest.K12.AtKey.written_columns_tight
#print axioms ProofFile.Honest.K12.AtKey.face_in_scope
#print axioms ProofFile.Honest.K12.AtKey.base_in_scope
#print axioms ProofFile.Honest.K12.AtKey.key_points_read_in_front
#print axioms ProofFile.Honest.K12.AtKey.batching_numbers_in_scope
#print axioms ProofFile.Honest.K12.AtKey.weights_read_in_front_at_value
#print axioms ProofFile.Honest.K12.AtKey.place_of_verifiers_index_masks_plan
#print axioms ProofFile.Honest.K12.AtKey.place_of_verifiers_vector_w_plan
#print axioms ProofFile.Honest.K12.AtKey.wJob_of_message
#print axioms ProofFile.Honest.K12.AtKey.vector_w_job_at_value
#print axioms ProofFile.Honest.K12.AtKey.senders_read_in_front_at_value
#print axioms ProofFile.Honest.K12.AtKey.plans_alike_at_value
#print axioms ProofFile.Honest.K12.AtKey.place_of_index_masks_at_value
#print axioms ProofFile.Honest.K12.AtKey.place_of_vector_w_at_value
