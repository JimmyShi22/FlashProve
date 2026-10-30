-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OwnJob.lean: the job of the key file's own test at a prover's
parts: its public fields against the written job `jobOwn` (E2E/KeyTestSizes.lean), and the two parts'
readers agree at the coins that the key file's book lends.

  `ownJob`        the job (`jobKWAt`, E2E/KeyProverSideOfOwnTest.lean) at the parts' two sendings, their public data and
                  the reader of the shared chain's rows (`askTests`, AtFullSide/K12/KeyFourTests.lean)
  `OwnSenders`    WHAT THE TEST ASKS OF THE PARTS: the two sendings' messages, codes and rides are the written
                  ones, and the shared chain's parameters are `QK`. The offline prover's letters
  `ownJob_p`, `ownJob_members`, `ownJob_fresh`   the job's three public fields
  `omega_member`  Omega's member reads of the parameters what `AK` and `QK` share. By the kernel
  `ties_own`, `agree_at_own`   `K12At.agree` and `RunPlays.agree` at every coin that the book lends

By what. `jobKW_members`, `membersKW`, `freshKW` (E2E/KeyJobW.lean), `msgOf_atPoint` (K12/AtProof/JobW.lean),
`full_ties` (K12/TiesAtKey.lean), `agree_of_ties_letter` (K12/AgreeAtKey.lean), `rowsMu_many`.

Limits.
- `OwnSenders` is a premise: no value of the parts is given. It can be false: at other parameters the
  members are not `jobOwn`'s.
- `keyBook` at `fullPub`: that the run's book is this one is the caller's.
- The rows of the two sendings are letters of the parts: nothing here reads their data.
- NOT IN FRONT OF A LAW OVER COINS: `agree_at_own` ties a job's readers to the lent coins.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnKernel
import Johnson.Desc.ProofFile.Honest.K12.AgreeAtKey
import AtFullSide.K12.KeyFourTests

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open VerifiableInference.Desc.Key (Source LaterPlaces Xi)
open H2K.Pub (sgOf)
open H2K.Member (piKWFull)
open AtPublicFiles.KeyBook (KeyPub keyBook atFull fullPub rideW)
open AtPublicFiles.KeyTest (jobOwn sIdx sW)
open AtPublicFiles.KeyLay (jobKWAt jobKW_members membersKW freshKW parIK parWK pWK AK)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles.Full (QK)
open AtFullSide.K12 (askTests)
open ProofFile.Honest.K12.AtProof (msgK1 senderO msgOf_atPoint)

section
variable {W₀ Rc X₀ X Wk : Type} (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source) (Nr : H2U.PlaceNums)
  (Pl : LaterPlaces)

/-- **The job of the own test at a prover's parts.** -/
abbrev ownJob : TestJob (In1 W₀ Rc) X :=
  (jobKWAt Xs Nr Pl K.idx K.w K.send id (askTests K)).toRun.toTest

/-- **What the test asks of the parts.** -/
structure OwnSenders : Prop where
  idxSent : K.idx.P.sent = parIK.sent
  idxCodes : K.idx.P.codes = parIK.codes
  idxRide : K.idx.ride = fun _ => none
  wSent : K.w.P.sent = parWK.sent
  wCodes : K.w.P.codes = parWK.codes
  wRide : K.w.ride = rideW
  sendPar : K.send.P = QK

theorem ownJob_p : (ownJob K Xs Nr Pl).p = pWK Pl := rfl

/-- A sending's member reads of its parameters the messages and the codes alone: not the groups, which hold the
tenants' records. -/
theorem msgK1_own {P Q : VerifiableInference.Desc.K1.Par} (hs : P.sent = Q.sent) (hc : P.codes = Q.codes)
    (a : Addr) (ride : Nat → Option K1.Ride) (k : Nat) : msgK1 a P ride k = msgK1 a Q ride k := by
  unfold msgK1 Johnson.Prover.Send.shapeAt
  rw [hs, hc]

/-- Omega's member reads of the parameters what the two written ones share. -/
theorem omega_member : ProofFile.Honest.K12.AtProof.msgOf senderO (ProofFile.Honest.K14.jobOmega ⟨QK, 0⟩) 0 =
    ProofFile.Honest.K12.AtProof.msgOf senderO (ProofFile.Honest.K14.jobOmega AK) 0 := by
  decide +kernel

variable {K}

/-- **The job's members are `jobOwn`'s.** -/
theorem ownJob_members (h : OwnSenders K) : (ownJob K Xs Nr Pl).members = jobOwn.members := by
  rw [← membersKW, ← omega_member]
  show [msgK1 sIdx K.idx.P K.idx.ride (K.idx.P.sent.size - 1), msgK1 sW K.w.P K.w.ride 0,
    ProofFile.Honest.K12.AtProof.msgOf senderO (ProofFile.Honest.K14.jobOmega ⟨K.send.P, _⟩) 0] = _
  rw [msgK1_own h.idxSent h.idxCodes, msgK1_own h.wSent h.wCodes, h.idxSent, h.idxRide, h.wRide,
    h.sendPar, msgOf_atPoint _ _ _ 0]

/-- **The word on the fresh table is `jobOwn`'s.** -/
theorem ownJob_fresh (h : OwnSenders K) : (ownJob K Xs Nr Pl).fresh = jobOwn.fresh := by
  rw [← freshKW]
  show some (sW, K.w.P.sent.size - 1) = _
  rw [h.wSent]

end

/-- `tiesB` at the own test, out of `full_ties`. -/
theorem ties_own (K₀ : KeyPub) (hK₀ : fullPub = some K₀) :
    tiesB (keyBook K₀) jobOwn.p.place jobOwn.members.length = true := by
  have h := full_ties
  unfold atFull at h
  rw [hK₀] at h
  exact List.all_eq_true.1 h jobOwn (by simp)

/-- k = h + g at the first stage of the own test. By the kernel. -/
theorem first_k_own : (piKWFull.nums.stages.headD default).k =
    (sgOf (piKWFull.nums.stages.headD default)).h +
      (sgOf (piKWFull.nums.stages.headD default)).g := by
  decide +kernel

theorem place_own : piKWFull.place = jobOwn.p.place := by decide +kernel

theorem fresh_some_own : jobOwn.fresh.isSome = true := by decide +kernel

/-- **The two parts' readers agree at every coin that the frame lends.** -/
theorem agree_at_own {V W X : Type} (K₀ : KeyPub) (hK₀ : fullPub = some K₀)
    (A : ProofFile.Honest.K12.Light.ManyJob W X) (hp : A.toRun.toTest.p = piKWFull)
    (hm : A.toRun.toTest.members = jobOwn.members) (hf : A.toRun.toTest.fresh = jobOwn.fresh)
    (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart A.toRun.toTest : Part V W X), restPart A.toRun.toTest])
    (hc : lendRow (keyBook K₀) rows look A.toRun.toTest.p.place
      [(firstPart A.toRun.toTest : Part V W X), restPart A.toRun.toTest] 0 = .ok c)
    (w : W) (fr : Front X) :
    Agree A.toRun.toTest w fr A.toRun.toTest.s₀ (firstRd A.toRun.toTest c.1)
      (restCoins A.toRun.toTest c.2.1) := by
  obtain ⟨f, hf'⟩ := Option.isSome_iff_exists.1 fresh_some_own
  have hT : tiesB (keyBook K₀) A.toRun.toTest.p.place A.toRun.toTest.members.length = true := by
    rw [hp, hm, place_own]
    exact ties_own K₀ hK₀
  have hk : A.toRun.toTest.s₀.k = (sgOf A.toRun.toTest.s₀).h + (sgOf A.toRun.toTest.s₀).g := by
    unfold TestJob.s₀
    rw [hp]
    exact first_k_own
  exact agree_of_ties_letter A.toRun.toTest f (hf.trans hf') (keyBook K₀) rows look c hc w fr hT hk
    fun mem mem' h => ProofFile.Honest.K12.Light.rowsMu_many A _ w fr mem mem' h

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.ownJob
#print axioms ProofFile.Honest.K12.AtKey.OwnSenders
#print axioms ProofFile.Honest.K12.AtKey.ownJob_p
#print axioms ProofFile.Honest.K12.AtKey.msgK1_own
#print axioms ProofFile.Honest.K12.AtKey.omega_member
#print axioms ProofFile.Honest.K12.AtKey.ownJob_members
#print axioms ProofFile.Honest.K12.AtKey.ownJob_fresh
#print axioms ProofFile.Honest.K12.AtKey.ties_own
#print axioms ProofFile.Honest.K12.AtKey.first_k_own
#print axioms ProofFile.Honest.K12.AtKey.place_own
#print axioms ProofFile.Honest.K12.AtKey.fresh_some_own
#print axioms ProofFile.Honest.K12.AtKey.agree_at_own
