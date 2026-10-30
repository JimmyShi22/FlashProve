-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/LaterJobs.lean: definitions alone: what the tests on G_u and G_omega lay at the shared
chain, beneath the law files of these tests.

  SeatU, keepsU    the test on G_u's block and what it keeps.
  tableShared, fixedShared   a tree's table and its count of challenges at the shared chain.
  jobDoorU, jobDoorO   the jobs at the two tests' seated places.
-/
import Johnson.Desc.ProofFile.Honest.K12.JobShared
import Johnson.Desc.ProofFile.Honest.K12.DoorsByShape
import Johnson.Desc.ProofFile.Honest.K12.DoorReturns
import Johnson.Desc.ProofFile.Honest.K12.DoorOpened
import Johnson.Desc.ProofFile.Honest.K12.NearAtHead
import Johnson.Desc.ProofFile.Honest.K12.OwnTbl
import Johnson.Desc.ProofFile.Honest.K12.ScriptLots
import Johnson.Desc.ProofFile.Honest.K14.SendingsPaid
import Johnson.Desc.ProofFile.Honest.K14.PaidAll
import Johnson.Desc.ProofFile.Honest.K14.Thread2Full
import Johnson.Desc.ProofFile.Honest.Small.FixedSent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St P14)
open ProofFile.Honest
open ProofFile.Honest.K14 (jobU jobOmega sendPlace sendTable witOf treesU)
open ProofFile.Honest.K12 (TestJob testTbl ownTbl)
open OnBytes (TableKey)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light (ManyJob jobAtU jobAtOmega doorUF doorOmegaF colsLoc colsOpened sentOf)

abbrev SeatU := VerifiableInference.Desc.K12.Seat.onGu

/-- **The letter of `keeps` at member 9.** -/
def keepsU (p : P12) (s s' : St) : Prop :=
  ∃ rs gs, (SeatU (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide s rs gs = .ok s'

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ : Type}

/-- **A tree's table at the shared chain.** -/
def tableShared (Q : P14) (weights : W₀ → Weights) (rand : Rc → TableRand)
    (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀) :
    Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table
  | .own n =>
    if n < treesU Q then sendTable (jobU ⟨Q, 0⟩) (witOf Q weights rand) (sendPlace 2) 1 n
    else if n < 3 then
      sendTable (jobOmega ⟨Q, 0⟩) (witOf Q weights rand) (sendPlace 5) 1 (n - treesU Q)
    else if n < 7 then testTbl 1 JU own₀ 8 (fun _ _ _ => true) (n - 3)
    else if n = 7 then ownTbl 1 JO own₀ 43 fun _ _ _ => true
    else testTbl 1 JO own₀ 43 (fun _ _ _ => true) (n - 8)
  | .taken _ _ => fun _ _ _ => (default, K1.wordlessTable)

/-- **After how many challenges a tree's table changes no more**: decl, the chain's declared rounds. -/
def fixedShared (decl : List Fmt.DeclaredRound) : Fmt.TreeSource → ℕ
  | .own n => ProofFile.Honest.Small.sentIn decl n
  | .taken _ _ => 0

/-- The job at the seated place of the test on G_u, with the state on entry that the door makes of the
stored columns. -/
abbrev jobDoorU (Zp : ProofFile.Pub) (Np : H2U.Places4) (bs : List (Block St Unit))
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64)) (wts : W₀ → Weights) (rnd : Rc → TableRand) :
    ManyJob (Common W₀ Rc TableKey) X₀ :=
  jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U
    (doorUF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fun w => w.key)
      (fun w fr => colsLoc (K1.qAt Zp Np) (st w.w₀ w.rc) fr.seen.rounds))
    (fun c => wts c.w₀) (fun c => rnd c.rc) none

/-- **The job at the seated place of the test on G_omega**, with the state on entry that the door makes of
the columns that the frame hands. -/
abbrev jobDoorO (Zp : ProofFile.Pub) (Np : H2U.Places4) (pO : P12) (bs : List (Block St Unit))
    (wts : W₀ → Weights) (rnd : Rc → TableRand) : ManyJob (Common W₀ Rc TableKey) X₀ :=
  jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO
    (doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U (fun w => w.key) colsOpened)
    (fun c => wts c.w₀) (fun c => rnd c.rc) none

end

end ProofFile.Honest.K12.AtFile
