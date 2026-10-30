-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/SharedSockets.lean: NOT IN FRONT OF A LAW OVER COINS. The shared
chain's two sockets of the object, filled by name.

  owes_socket, yes_socket   the texts of Socket.owes₂, Socket.yes₂ (TheSocketStatements.lean), at
                       TheLetters' values

Premises left. t: what the kinds' laws ask of the run's input, a field of TheThreadsHalf's tied.

By what. owes_letters, yes_letters (SharedAtLetters.lean).

Limits. At the base return alone. Nothing on completeness, soundness or hiding.
-/
import AtFullSide.Honest.ThreadsAtTheTerm
import AtFullSide.Honest.TheThreeThreads
import Johnson.Desc.ProofFile.Honest.K12.AtFile.SharedAtLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest.TheLetters
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixFilling)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)
  (O : OpenShared A) (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)

/-- **owes₂, by name.** -/
theorem owes_socket (scope : VerifierAndGoals.InScope Z = true)
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (t : TiedAtRun (A := A) (reads h) R.own R.common) :
    OwesS (threadTwo h (reads h) (shared h O) R) (saidTwo h (reads h) (shared h O) R) :=
  owes_letters h O R.common (sharedStand A.H R) scope base t.key

/-- **yes₂, by name, at every list of falls.** -/
theorem yes_socket (scope : VerifierAndGoals.InScope Z = true)
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (t : TiedAtRun (A := A) (reads h) R.own R.common)
    (f₂ : List (Fall h.description.S₂)) :
    YesS (threadTwo h (reads h) (shared h O) R) (saidTwo h (reads h) (shared h O) R)
      (fallsBy f₂ h.description.shared.blocksInOrder) :=
  yes_letters h O R.common (sharedStand A.H R) scope base t.key _

end AtFullSide.Honest.TheLetters

#print axioms AtFullSide.Honest.TheLetters.owes_socket
#print axioms AtFullSide.Honest.TheLetters.yes_socket
