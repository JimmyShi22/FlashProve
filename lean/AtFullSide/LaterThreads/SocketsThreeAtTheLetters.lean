-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/LaterThreads/SocketsThreeAtTheLetters.lean: CONDITIONAL. THE FULL SIZE ALONE.

THE YES AT MEMBERS 0 AND 1 IS TAKEN OUT OF THE INVARIANT IN FRONT, NOT SHOWN OF THE RUN: the stand at
border 0 holds `doorRider`'s eleven tests and the test `tiedAheadB` at the start's record, the stand at
border 1 holds what `tiedRider` says, and the yes is read off these. So THIS YES IS HALF A SENTENCE
WITHOUT THE ONE OBJECT's THREE FIELDS `doorRides`, `doorFive` AND `doorTrees`, which speak of what the door
lays into that stand. Nothing here says that the last chain accepts.

What is here. THE TWO SOCKETS `Socket.owes₃` AND `Socket.yes₃`
(AtFullSide/Honest/TheSocketStatements.lean, where `threadThree` is `lastThread` at the
run's own input) AT THE LETTERS' VALUES `first h`, `reads h`, `shared h O`, `lastParts h (first h)
(last h P)`, WITH NO FALL: the fields owes₃ and yes₃ of the one object, as that
object binds them. `owes_and_yes_three_at_the_letters`
(AtFullSide/LaterThreads/OwesAndYesThreeAtTheLetters.lean) said in these names: so Lean holds
`thread₃` and `said₃` against `threadThree` and `saidThreeTied`.

  `sockets_three_at_the_letters`   **the two sockets, from `LastChainDebtsAtTheNames`.**

Not shown here. EVERY FIELD OF `LastChainDebtsAtTheNames` IS A HYPOTHESIS HERE. Every limit of
AtFullSide/LaterThreads/OwesAndYesThreeAtTheLetters.lean's head holds here, and that head says who
meets them. NO THEOREM OF THIS LIBRARY THAT NAMES THIS THREAD SHOWS A STAND OF IT AT ANY BORDER
BEYOND 0 BUT FROM A PREMISE THAT HOLDS ONE. Had: the door (`doorAtTheTerm`,
AtFullSide/Honest/ThreadsAtTheTerm.lean): a stand at border 0 behind stands of the two earlier
threads at their ends and the start's yes, where both ends hold opened columns, under
`ThreadFieldsP` and ready's return; and the general rule `thread_in_second`
(Johnson/Desc/ProofFile/Honest/Law/InsideFile.lean): for three invariants that its premises have
carried by every member, at the two starts and through the door, at a run of runC that returns,
where ready returns, the plan is fit and served, the draws are due and no silent stop fires, a
called part of the second chain is reached from a state at which the third invariant holds. No
statement joins them into one that ends in a stand of this thread. Nothing on hiding. Nothing on
soundness, on completeness or on any other property.

No property is claimed.
-/
import AtFullSide.LaterThreads.OwesAndYesThreeAtTheLetters
import AtFullSide.Honest.TheSocketStatements

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.LaterThreads
open ProofFile ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (baseMaker)
open AtFullSide.Honest (Socket.owes₃ Socket.yes₃)
open AtFullSide.Honest.TheLetters (OpenShared OpenLast first reads shared last)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open OnBytes (TableKey)
open Johnson.AtFull.Shape (ShA)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- CONDITIONAL: on h, made and the hypotheses D. **THE SOCKETS owes₃ AND yes₃ AT THE LETTERS'
VALUES, WITH NO FALL.** Implications from the thread's stand in front of each member; no theorem of
this library that names this thread shows a stand of it at any border beyond 0 but from a premise
that holds one. -/
theorem sockets_three_at_the_letters (h : HeadAtReturn files A) (made : baseMaker files = .ok A)
    {O : OpenShared A} (P : OpenLast h O)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) {firstEnd : ShA} {w₀ : FullSizeMatrix} {rc : IndexCommitterCoins}
    {x : ProofFile.Inst} {k : Coins A.B} (D : LastChainDebtsAtTheNames h P R firstEnd w₀ rc x k) :
    Socket.owes₃ h (first h) (reads h) (shared h O) (lastParts h (first h) (last h P)) R ∧
      Socket.yes₃ h (first h) (reads h) (shared h O) (lastParts h (first h) (last h P)) R [] := by
  have both := owes_and_yes_three_at_the_letters h made P R D
  exact ⟨both.1, both.2⟩

end AtFullSide.LaterThreads

#print axioms AtFullSide.LaterThreads.sockets_three_at_the_letters
