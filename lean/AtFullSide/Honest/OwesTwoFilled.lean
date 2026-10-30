-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/OwesTwoFilled.lean: the field owes₂ of TheThreadsHalf (TheOneObject.lean), in the
field's own type.

The protocol has three parts, named by what a user holds. offline: the proof in the key file, on the
committed table. link: from a further encoding to the first. online: the proof for a request (the
proof file). The online part has three chains of sub-protocols: the first, the shared, the second.
owes₂ is OwesS at the shared chain's thread, at every run of the base prover at a tied request: at
each member, from the chain's invariant at that member's border, PlaysS, BehindS, ExchangeS and
RidesPastS (Honest/Thread/PaysS.lean), the four that say nothing of a fall.
owes₂_filled is an implication. Its premises: the files are in scope; the maker returns A; and the
field tied of the same structure, from which the law reads that the input's key is the committer's.
By what: TheLetters.owes_socket (Honest/K12/AtFile/SharedSockets.lean), which holds all twelve members.
Limits: at the base return alone. Nothing on completeness, soundness or hiding.
-/
import AtFullSide.Honest.TheOneObject
import Johnson.Desc.ProofFile.Honest.K12.AtFile.SharedSockets

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixFilling)
open VerifierAndGoals (PublicFiles readFiles InScope)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {h : HeadAtReturn Z A}
  {pp : Inst.Model.ScalesAndPolicy} {hr : readFiles Z = .ok pp}

/-- **owes₂, in the field's type**, at every value of the shared chain's named hole. -/
theorem owes₂_filled (scope : InScope Z = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (open₂ : TheLetters.OpenShared A)
    (tied : ∀ r : TiedRun h hr, Socket.tied (A := A) (TheLetters.reads h) r.R) :
    ∀ r : TiedRun h hr,
      Socket.owes₂ h (TheLetters.reads h) (TheLetters.shared h open₂) r.R :=
  fun r => TheLetters.owes_socket h open₂ r.R scope made (tied r)

/- The field takes it, at the structure's own letter and its own field tied. -/
example (scope : InScope Z = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (T : TheThreadsHalf h hr) : TheThreadsHalf h hr :=
  { T with owes₂ := owes₂_filled scope made T.open₂ T.tied }

end AtFullSide.Honest

#print axioms AtFullSide.Honest.owes₂_filled
