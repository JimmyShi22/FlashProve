-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyLayFits.lean: whether the makers of the proof file's two shared proximity tests (jobAtU,
jobAtOmega, Johnson/Desc/ProofFile/Honest/K12/JobShared.lean) also fit the key file's places. Three
texts written apart meet: the places made by a program off a print (piKUFull, piKOFull,
Johnson/Desc/K12/Law/PlacesKeyFull.lean), the kind K14's plan at the key's written sizes (atKey,
Johnson/Desc/K14/Shape/EndToy.lean), and the literals of jobFolded and jobOmega
(E2E/KeyTestSizes.lean). On no row: a test of the makers' shape.

What can say no. In nearK_U and nearK_O the clauses on each member's rows, on base and on the first
rows are true by make: both sides read the same notices of atKey.S. What can fail there is the
place's first stage against the plan: k, h and the two codes; and the number of members. In
membersK_U and membersK_O the makers' addresses, numbers and counts and the places' stages are held
against literals that were typed apart.

  AK, sentK      the public data at the key's written sizes; what goes out with o_u
  nearU, nearO   the part of a state that layFits reads, made of the plan (pubBehind, nearOf)
  nearK_U, nearK_O   layFitsNear is true at the public jobs at these places
  layFitsK_U, layFitsK_O   so at the makers, at every door, readers and vector
  membersK_U, membersK_O   the makers' members and word on the fresh table are the literals', and
      the places' stages are theirs
  factsK         three of the public facts at these sizes that the law on the door would ask; that
      law asks more: the eight are made, the fall-back's near part, and planOk at the test on G_u

Which plan. sharedPar c bp (Johnson/Desc/Key/Chains23.lean), the key file's own, is open in c, the
planner's chains. atKey is closed: the written sizes of a key of full size. Second.K14's SeatIsKey
(Johnson/Second/K14/RadiusAtSeatKey.lean) holds sharedPar's set, scope and shape to those of c's
sizes; that c's sizes are keyFull at the head is not called here. atKey's beforePoint is a
placeholder: no text read here reads it.

Limits.
- A test of shapes and public numbers: nothing of any value at the full size, no row, no door.
- That the state on entry has this near part (the like of near_doorUF, at the key) is not shown.
- A SendPub's atPoint is 0 here: no text read here reads it.
- The key's ranges and own tests are not here.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.K14.Shape.EndToy
import Johnson.Desc.K12.Law.PlacesKeyFull
import Johnson.Desc.ProofFile.Honest.K12.NearAtHead
import Johnson.Desc.ProofFile.Honest.K12.PubAtSmallDoor
import E2E.KeyTestSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLay
open OnBytes (OracleNotice)
open H2K.Member (piKUFull piKOFull)
open Desc.K14.Shape.EndToy (atKey)
open ProofFile.Honest.K14 (SendPub)
open ProofFile.Honest.K12 (TestJob)
open ProofFile.Honest.K12.Light (ManyJob Near Mem pubJob shapesAtU shapesAtOmega shapes_atU shapes_atOmega
  jobAtU jobAtOmega layFitsNear layFitsNear_congr nearOf pubBehind sentOf noState)
open ProofFile.Honest.K12.Light.SharedSmall (shapes_pubJob)

variable {W X : Type}

/-- The public data at the key's written sizes. -/
def AK : SendPub := ⟨atKey, 0⟩

/-- What goes out with o_u at these sizes. -/
def sentK : Array OracleNotice := sentOf atKey.S

/-- What layFits reads at the test on the folded row, made of the plan. -/
def nearU : Near := nearOf (pubBehind atKey sentK) 0

/-- The same at the test on Omega. -/
def nearO : Near := nearOf (pubBehind atKey sentK) 1

/-- The job of the test on the folded row at these places, at arguments that hold nothing. -/
def bareK_U : ManyJob Unit Unit :=
  jobAtU AK piKUFull (fun _ _ => noState) (fun _ => ⟨fun _ _ => 0⟩)
    (fun _ => ⟨fun _ _ => 0, fun _ _ => 0⟩) none

/-- The same at the test on Omega. -/
def bareK_O : ManyJob Unit Unit :=
  jobAtOmega AK piKOFull (fun _ _ => noState) (fun _ => ⟨fun _ _ => 0⟩)
    (fun _ => ⟨fun _ _ => 0, fun _ _ => 0⟩) none

-- what the two sides hold, as the evaluator read them
#guard (shapesAtU AK piKUFull).map (fun s =>
    (s.mainFirst, s.mainRows, s.maskFirst, s.maskRows, s.base)) ==
  [(0, 107, 0, 0, false), (0, 0, 0, 1, true)]
#guard (shapesAtOmega AK piKOFull).map (fun s =>
    (s.mainFirst, s.mainRows, s.maskFirst, s.maskRows, s.base)) ==
  [(0, 12, 0, 0, false), (0, 0, 0, 1, true)]
#guard nearU.2.map (fun x => (x.1.code, x.1.maskCode, x.1.members.toList, x.1.kept.toList,
    x.2.toList.map fun o => (o.mainRows, o.maskRows, o.mainDeg))) ==
  some (0, 0, [0, 3], [false, false], [(107, 0, 3), (0, 1, 1)])
#guard nearO.2.map (fun x => (x.1.code, x.1.maskCode, x.1.members.toList, x.1.kept.toList,
    x.2.toList.map fun o => (o.mainRows, o.maskRows, o.mainDeg))) ==
  some (5, 0, [2, 3], [false, false], [(12, 0, 3), (0, 1, 1)])
#guard bareK_U.mems.map (·.sent.2.2.e) == [10380, 210] &&
  bareK_O.mems.map (·.sent.2.2.e) == [1177, 210]

/-- **Three public facts at these sizes**: withU returns; the shape splits; masks go ahead. -/
theorem factsK : Desc.K14.withU atKey.S = some sentK ∧ atKey.S.sharedSplitNeeded = true ∧
    atKey.S.masksAhead = true := by
  decide +kernel

/-- **layFits's near test at the public job, at the test on the folded row.** -/
theorem nearK_U : layFitsNear (pubJob piKUFull (shapesAtU AK piKUFull)) nearU = true := by
  decide +kernel

/-- **The same at the test on Omega.** -/
theorem nearK_O : layFitsNear (pubJob piKOFull (shapesAtOmega AK piKOFull)) nearO = true := by
  decide +kernel

/-- **So at the maker, at every door, readers and vector.** -/
theorem layFitsK_U (door : W → ProofFile.Honest.Front X → VerifiableInference.Desc.K12.T12)
    (weights : W → ProofFile.Honest.Weights) (rand : W → ProofFile.Honest.TableRand)
    (u? : Option (W → ProofFile.Honest.Front X → ℕ → OnBytes.E)) :
    layFitsNear (jobAtU AK piKUFull door weights rand u?) nearU = true := by
  rw [layFitsNear_congr (jobAtU AK piKUFull door weights rand u?)
    (pubJob piKUFull (shapesAtU AK piKUFull)) rfl
    ((shapes_atU AK piKUFull _ weights rand u?).trans (shapes_pubJob _ _).symm)]
  exact nearK_U

/-- **The same at the test on Omega.** -/
theorem layFitsK_O (door : W → ProofFile.Honest.Front X → VerifiableInference.Desc.K12.T12)
    (weights : W → ProofFile.Honest.Weights) (rand : W → ProofFile.Honest.TableRand)
    (omega? : Option (W → ProofFile.Honest.Front X → ℕ → OnBytes.E)) :
    layFitsNear (jobAtOmega AK piKOFull door weights rand omega?) nearO = true := by
  rw [layFitsNear_congr (jobAtOmega AK piKOFull door weights rand omega?)
    (pubJob piKOFull (shapesAtOmega AK piKOFull)) rfl
    ((shapes_atOmega AK piKOFull _ weights rand omega?).trans (shapes_pubJob _ _).symm)]
  exact nearK_O

/-- **The maker's members and word on the fresh table are jobFolded's, and the place's stages.** -/
theorem membersK_U :
    bareK_U.mems.map (·.sent) = AtPublicFiles.KeyTest.jobFolded.members ∧
      bareK_U.fresh = AtPublicFiles.KeyTest.jobFolded.fresh ∧
      piKUFull.nums.stages = AtPublicFiles.KeyTest.stagesFolded := by
  decide +kernel

/-- **The same at the test on Omega: jobOmega's.** -/
theorem membersK_O :
    bareK_O.mems.map (·.sent) = AtPublicFiles.KeyTest.jobOmega.members ∧
      bareK_O.fresh = AtPublicFiles.KeyTest.jobOmega.fresh ∧
      piKOFull.nums.stages = AtPublicFiles.KeyTest.stagesOmega := by
  decide +kernel

end AtPublicFiles.KeyLay

#print axioms AtPublicFiles.KeyLay.factsK
#print axioms AtPublicFiles.KeyLay.nearK_U
#print axioms AtPublicFiles.KeyLay.nearK_O
#print axioms AtPublicFiles.KeyLay.layFitsK_U
#print axioms AtPublicFiles.KeyLay.layFitsK_O
#print axioms AtPublicFiles.KeyLay.membersK_U
#print axioms AtPublicFiles.KeyLay.membersK_O
