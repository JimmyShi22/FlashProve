-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyHalves.lean: the prover's sides of the key file's two shared proximity tests, for the
letters onU and onOmega of the key file's honest prover. They are the proof file's makers, at the
key's public data: HalfU.lean's job at the test on G_u, HalfO.lean's at the test on G_omega.

  jobKU, jobKO     the jobs, at public data A, the two places' numbers, the eight bs, and at the
                   readers: st, the stored columns (G_u alone); weights; rand
  proverSideOfTestOnU, proverSideOfTestOnOmega   their pairs of parts; the second behind the guard (K12/FieldGuard.lean)
  blocksK_made     the eight are made at the key's written sizes
  fitsK_U, fitsK_O, membersKU, membersKO   instances of KeyLayFits.lean's laws at these jobs, no new
      weight: what can say no is told in that file's head

Limits.
- Nothing is played here, and nothing says that a sub-protocol accepts what a pair sends. st,
  weights, rand and bs are letters: which readers of the key's prover they are, that they are one,
  and that bs is the list that blocksK_made says is there, are the caller's. The types fit
  KeyParts.onU and KeyParts.onOmega (E2E/KeyProver.lean) at X₀ := X; no term here names them.
  The caller turns K.stored into words, and reads K.weights at w.w₀ and K.rand at w.rc, as
  keyProver hands the sendings (randK14).
- jobKU's state on entry reads the stored table's columns at "LOC"'s positions, as jobLocU's;
  jobKO's reads the columns that the frame hands. Their laws stand at the proof file's description.
  The like at the key file's (sharedChain, Johnson/Desc/Key/Chains23.lean) is not typed here: for
  the test on G_omega it is `door_key_at_omega`
  (Johnson/Desc/ProofFile/Honest/K12/SimO/KeyRun.lean), and at `jobKO` `omega_door_at_run`
  (E2E/OfflineOmegaDoor.lean). (At the made-up record `keyAsProof c` the key's shared chain is
  `chainOf` and the two fronts' tests are one, without a premise: `sharedChain_eq_chainOf`,
  `front2_keyAsProof`, Johnson/Desc/Key/SharedChainIsChainOf.lean; not called here.)
- atKey stands for sharedPar c bp: KeyLayFits.lean's head.
- The limits of HalfU.lean and of HalfO.lean stand: the silent fall-back; the arm; the lending.
  Of jobKU, on a simulator: the words of Honest/AtPureWiderK12U.lean on the stored table's columns.
- On hiding (said of the text; no theorem); the like holds at the proof file's pair. The state on
  entry reads the key, the rounds shown, and ALL columns opened in front of this test, in the order
  of reading: the stored table's at "LOC"'s positions, computed from the index; and those that the
  test on G_u has read from trees that parts of the run have sent, computed from the index AND THE
  RUN's COINS. So whatever is said of a simulator at this place holds only «given the key, the
  rounds shown and all columns opened in front: "LOC"'s, and those that the test on G_u has read».
  The second kind cannot be handed to a simulator from outside: the simulators of the parts in front
  have to make them. That the field holds columns of the run's view is shown at a called part of the
  shared chain, at any description, at a stand of the member (`StandsAt`), where the plan is fit and
  `ready` and `runC` return: the field holds just the columns that the fold over the sub-protocols
  in front reads, filled from the stored words and from the trees of the run's own played rounds
  (`called_columns`), and the front that shows of the trees what stands at the positions `treeAsks`
  lists just these (`view_columns_shared`; both Johnson/Desc/ProofFile/Honest/K12/SimO/Door.lean).
  At the key file's test on G_omega the job's state on entry is the one that the simulators' job
  makes of the run's front, under that theorem's premises, among them that `runC` returns
  (`omega_door_at_run`, E2E/OfflineOmegaDoor.lean). Each read's position is among the positions read
  of its tree (`mem_treeAsks`, Johnson/Desc/ProofFile/Honest/Law/Rule/Words.lean). No one statement
  joins the two at this test, and that a run returns, calls a part or stands at the member is not
  shown in these files.
- Nothing on completeness, soundness or hiding.
-/
import E2E.KeyLayFits
import Johnson.Desc.ProofFile.Honest.K12.JobsLocU
import Johnson.Desc.ProofFile.Honest.K12.DoorOpened
import Johnson.Desc.ProofFile.Honest.K12.FieldGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLay
open OnBytes (TableKey)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St)
open H2K.Member (piKUFull piKOFull)
open Desc.K14.Shape.EndToy (atKey)
open ProofFile.Honest (Common Placed Weights TableRand)
open ProofFile.Honest.K14 (SendPub)
open ProofFile.Honest.K12 (proverSideOfProximityTest)
open ProofFile.Honest.K12.Light (ManyJob jobLocU jobAtOmega doorOmegaF colsOpened sentOf layFitsNear)

variable {W₀ Rc X : Type}

/-- **The job at the test on G_u.** -/
def jobKU (A : SendPub) (pU : P12) (bs : List (Block St Unit))
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand) :
    ManyJob (Common W₀ Rc TableKey) X :=
  jobLocU A pU (sentOf A.P.S) bs st weights rand none

/-- **The job at the test on G_omega.** pU: the numbers of the test on G_u, which the door folds
over; pO: this test's. -/
def jobKO (A : SendPub) (pU pO : P12) (bs : List (Block St Unit))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand) :
    ManyJob (Common W₀ Rc TableKey) X :=
  jobAtOmega A pO (doorOmegaF A.P (sentOf A.P.S) bs pU (fun w => w.key) colsOpened) weights rand
    none

/-- **The pair at the test on G_u.** No test on the shape stands around it (see `proverSideOfGuardedSending`'s
docstring, E2E/KeyProverSideOfOwnTest.lean), and its letters are free here: each has to be the sender's own.
`onUOf` (E2E/KeyPartsHalves.lean) lays it at a prover's own parts. -/
def proverSideOfTestOnU (A : SendPub) (pU : P12) (bs : List (Block St Unit))
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand) :
    Placed Empty (Common W₀ Rc TableKey) X :=
  proverSideOfProximityTest (jobKU A pU bs st weights rand).toRun.toTest

/-- **The pair at the test on G_omega, behind the guard.** No test on the shape stands around it
(see `proverSideOfGuardedSending`'s docstring, E2E/KeyProverSideOfOwnTest.lean), and its letters are free here: each has to be the
sender's own. `onOmegaOf` (E2E/KeyPartsHalves.lean) lays it at a prover's own parts. -/
def proverSideOfTestOnOmega (A : SendPub) (pU pO : P12) (bs : List (Block St Unit))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand) :
    Placed Empty (Common W₀ Rc TableKey) X :=
  (proverSideOfProximityTest (jobKO A pU pO bs weights rand).toRun.toTest :
    Placed Empty (Common W₀ Rc TableKey) X).needsField

/-- The eight are made at the key's written sizes. -/
theorem blocksK_made : (Desc.K14.blocks atKey).isSome = true := by
  decide +kernel

/-- **What layFits reads holds at the test on G_u, at the key's places.** -/
theorem fitsK_U (bs : List (Block St Unit)) (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand) :
    layFitsNear (jobKU (X := X) AK piKUFull bs st weights rand) nearU = true :=
  layFitsK_U _ _ _ _

/-- **The same at the test on G_omega.** -/
theorem fitsK_O (bs : List (Block St Unit))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand) :
    layFitsNear (jobKO (X := X) AK piKUFull piKOFull bs weights rand) nearO = true :=
  layFitsK_O _ _ _ _

/-- **The members and the word on the fresh table at the test on G_u are jobFolded's.** -/
theorem membersKU (bs : List (Block St Unit)) (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand) :
    (jobKU (X := X) AK piKUFull bs st weights rand).mems.map (·.sent) =
        AtPublicFiles.KeyTest.jobFolded.members ∧
      (jobKU (X := X) AK piKUFull bs st weights rand).fresh = AtPublicFiles.KeyTest.jobFolded.fresh :=
  ⟨membersK_U.1, membersK_U.2.1⟩

/-- **The same at the test on G_omega: jobOmega's.** -/
theorem membersKO (bs : List (Block St Unit))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand) :
    (jobKO (X := X) AK piKUFull piKOFull bs weights rand).mems.map (·.sent) =
        AtPublicFiles.KeyTest.jobOmega.members ∧
      (jobKO (X := X) AK piKUFull piKOFull bs weights rand).fresh = AtPublicFiles.KeyTest.jobOmega.fresh :=
  ⟨membersK_O.1, membersK_O.2.1⟩

end AtPublicFiles.KeyLay

#print axioms AtPublicFiles.KeyLay.jobKU
#print axioms AtPublicFiles.KeyLay.jobKO
#print axioms AtPublicFiles.KeyLay.proverSideOfTestOnU
#print axioms AtPublicFiles.KeyLay.proverSideOfTestOnOmega
#print axioms AtPublicFiles.KeyLay.blocksK_made
#print axioms AtPublicFiles.KeyLay.fitsK_U
#print axioms AtPublicFiles.KeyLay.fitsK_O
#print axioms AtPublicFiles.KeyLay.membersKU
#print axioms AtPublicFiles.KeyLay.membersKO
