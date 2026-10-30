-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOwnJob.lean: the value ties of the own test's job: the place is the written one in scope; the job's trees and its members'
shapes are the written ones where its three sendings have the written public data.

  `pW_full`, `place_own`: the place.
  `trees_own`: the job's trees.
  `mems_closed`, `mems_own`: the members' shapes.

What stays open. hI, hW, hO: what the sendings send, at the closed value: three equations on K's fields. Not the whole plan: at the verifier's plans in scope the
field groups differs from parIK's, parWK's (by an evaluation), and the members' shapes read `sent` alone.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyOwnLines
import E2E.KeyProverSideOfOwnTest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyLastChain
open OnBytes
open ProofFile.Honest
open ProofFile.Honest.K14 (SendPub Ask jobOmega)
open ProofFile.Honest.K12.Light (ManyJob firstsOf)
open ProofFile.Honest.K12.AtProof (shapesW treesW memShape)
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces descriptionFromSource)
open AtPublicFiles.KeyLay (pWK jobKW jobKWAt parIK parWK shapeOK)
open AtPublicFiles.KeyTest (jobOwn sW)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (PF later_sourced)
open H2K.Member (piKWFull)

/-- **The place at the written values.** -/
theorem pW_full : pWK PF = piKWFull := by
  first
  | decide +kernel
  | rfl

theorem place_own {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) : pWK Pl = piKWFull := by
  obtain rfl := later_sourced hs scope
  exact pW_full

/-- The members' shapes at the written public data. -/
theorem mems_closed :
    [memShape (shapeAt parIK (parIK.sent.size - 1))
        ((firstsOf (shapesW parIK parWK shapeOK)).getD 0 (none, none)),
      memShape (shapeAt parWK 0) ((firstsOf (shapesW parIK parWK shapeOK)).getD 1 (none, none)),
      memShape shapeOK ((firstsOf (shapesW parIK parWK shapeOK)).getD 2 (none, none))] = msKW := by
  decide +kernel

theorem members_three : AtPublicFiles.KeyTest.jobOwn.members.length = 3 := by decide +kernel

theorem depths_W : (treesW piKWFull).map (·.1) = [13, 22, 22] := by decide +kernel

section
variable {W₀ Rc Tr Y Wd : Type} (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces)
  (JI JW : ProofFile.Honest.K1.SendJob Wd Y) (A : SendPub) (lift : Local W₀ Rc Xi Tr → Wd)
  (ask : Local W₀ Rc Xi Tr → Ask)

/-- **The job's trees.** -/
theorem trees_own (hpl : pWK Pl = piKWFull) :
    (jobKWAt Xs Nr Pl JI JW A lift ask).trees = treesW piKWFull := by
  show treesW (pWK Pl) = _
  rw [hpl]

/-- **The job's count of members.** -/
theorem members_own : (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.members.length = jobOwn.members.length := by
  show 3 = _
  exact members_three.symm

/-- **Its fresh table.** -/
theorem fresh_own : (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.fresh = some (sW, JW.P.sent.size - 1) := rfl

/-- **The depths of its trees**, at every plain data. -/
theorem depths_own (hpl : pWK Pl = piKWFull) (w : Local W₀ Rc Xi Tr) (fr : Front Y) (mem : Nat → ProofFile.Honest.K12.Stretch)
    (P : Johnson.Prover.Link.PS) :
    ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.trees₀ w fr mem P).map (·.1) = [13, 22, 22] := by
  have h : ((jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.trees₀ w fr mem P).map (·.1) =
      (jobKWAt Xs Nr Pl JI JW A lift ask).trees.map (·.1) := by
    show ((ProofFile.Honest.K12.Light.treesOf _ _ (jobKWAt Xs Nr Pl JI JW A lift ask).trees).map
      fun T => ProofFile.Honest.K12.Light.treeOf _ T P).map (·.1) = _
    unfold ProofFile.Honest.K12.Light.treesOf
    simp only [List.map_map]
    exact List.map_congr_left fun _ _ => rfl
  rw [h, trees_own Xs Nr Pl JI JW A lift ask hpl]
  exact depths_W

/-- **The members' shapes, at any place and door.** -/
theorem mems_job {W X : Type} {Wd' : Type} (q : VerifiableInference.Desc.K12.P12)
    (door : W → Front X → VerifiableInference.Desc.K12.T12) (JI JW : ProofFile.Honest.K1.SendJob Wd' X) (A : SendPub)
    (lift : W → Wd') (ask : W → Ask) (n₁ : Nat) (hI : JI.P.sent = parIK.sent) (hW : JW.P.sent = parWK.sent)
    (hO : ((jobOmega ⟨A.P, n₁ + A.atPoint⟩).Q.sent.getD 0 default).shape = shapeOK) :
    (jobKW q door JI JW A lift ask n₁).mems.map (·.shape) = msKW := by
  show [memShape (shapeAt JI.P (JI.P.sent.size - 1))
        ((firstsOf (shapesW JI.P JW.P ((jobOmega ⟨A.P, n₁ + A.atPoint⟩).Q.sent.getD 0 default).shape)).getD 0
          (none, none)),
      memShape (shapeAt JW.P 0)
        ((firstsOf (shapesW JI.P JW.P ((jobOmega ⟨A.P, n₁ + A.atPoint⟩).Q.sent.getD 0 default).shape)).getD 1
          (none, none)),
      memShape ((jobOmega ⟨A.P, n₁ + A.atPoint⟩).Q.sent.getD 0 default).shape
        ((firstsOf (shapesW JI.P JW.P ((jobOmega ⟨A.P, n₁ + A.atPoint⟩).Q.sent.getD 0 default).shape)).getD 2
          (none, none))] = _
  have eI : ∀ k, shapeAt JI.P k = shapeAt parIK k := fun k => by
    unfold shapeAt
    rw [hI]
  have eW : ∀ k, shapeAt JW.P k = shapeAt parWK k := fun k => by
    unfold shapeAt
    rw [hW]
  have hsz : JI.P.sent.size = parIK.sent.size := by rw [hI]
  have eS : ∀ s, shapesW JI.P JW.P s = shapesW parIK parWK s := fun s => by
    unfold shapesW
    rw [eI, eW, hsz]
  rw [eS, eI, eW, hsz, hO]
  exact mems_closed

/-- **The members' shapes at the own test's job.** -/
theorem mems_own (hI : JI.P.sent = parIK.sent) (hW : JW.P.sent = parWK.sent)
    (hO : ∀ n, ((jobOmega ⟨A.P, n + A.atPoint⟩).Q.sent.getD 0 default).shape = shapeOK) :
    (jobKWAt Xs Nr Pl JI JW A lift ask).mems.map (·.shape) = msKW :=
  mems_job _ _ _ _ _ _ _ _ hI hW (hO _)

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.pW_full
#print axioms AtPublicFiles.KeyLastChain.place_own
#print axioms AtPublicFiles.KeyLastChain.mems_closed
#print axioms AtPublicFiles.KeyLastChain.trees_own
#print axioms AtPublicFiles.KeyLastChain.members_three
#print axioms AtPublicFiles.KeyLastChain.depths_W
#print axioms AtPublicFiles.KeyLastChain.members_own
#print axioms AtPublicFiles.KeyLastChain.fresh_own
#print axioms AtPublicFiles.KeyLastChain.depths_own
#print axioms AtPublicFiles.KeyLastChain.mems_job
#print axioms AtPublicFiles.KeyLastChain.mems_own
