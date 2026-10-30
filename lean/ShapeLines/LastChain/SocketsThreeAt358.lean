-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/LastChain/SocketsThreeAt358.lean: two of the six debts of the last chain's sockets owes₃
and yes₃, paid by this library's facts.
What it says. sockets_three_at_the_letters (AtFullSide/LaterThreads/SocketsThreeAtTheLetters.lean)
concludes Socket.owes₃ and Socket.yes₃ at the letters' values from the six fields of
LastChainDebtsAtTheNames (AtFullSide/LaterThreads/OwesAndYesThreeAtTheLetters.lean).
sockets_three_at_358 is that law at firstEnd := border358, with the field wholeRun paid by
runOnShapes_toEnd (ShapeLines/FirstChainRuns.lean) and the field line by lastRunAt_border358. The
four other fields stay, as premises.
How. One call and one closed line. lastRunAt border358 = true says what last_run_at_border358
(ShapeLines/LastChain/LastRunAtBorder358.lean) says, by the law's own name for the Bool (lastRunAt,
AtFullSide/LaterThreads/FramesOfTheLastThreadOfTheRun.lean). No line of Lean here ties the two
texts, and this file does not import that one: the kernel evaluates the Bool a second time. The
proof term is Eq.refl true, by kernel_rfl.
Limits. Conditional on: the head at a return (h); made: the base maker's return, not the online
maker's; P : OpenLast h O, which holds two propositions, so that there is a P is itself a premise;
and four debts: standRest, readyReturns, tied, indexInRange. That these premises can be met, one by
one or together, is not shown here; what is known of each is the law's head's to say. Both
conclusions are implications from a stand of the last chain's thread before each member; that there
is such a stand is not shown here, and by the law's head the rider at border 0 moves a debt to the
door. The two debts paid here are spent at one place in the law: the acceptance at the chain's last
member (last_end_accepts_of_the_run, OwesAndYesAtTheLastThreadFinest.lean). For the closed line the
limits of LastRunAtBorder358.lean's head hold; its controls are stated of the other text. The full
size alone; shapes alone in the two facts.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import AtFullSide.LaterThreads.SocketsThreeAtTheLetters
import ShapeLines.FirstChainRuns
import Johnson.Unfolds.KernelRfl

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- The statement's terms are deep, as in the law's own file: the recursion limit is raised.
set_option maxRecDepth 100000

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ShapeLines
open ProofFile ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (baseMaker)
open ProofFile.Honest.K12.AtFile (StandRest)
open AtFullSide.LaterThreads
open AtFullSide.Honest (Socket.owes₃ Socket.yes₃ TiedAtRun)
open AtFullSide.Honest.TheLetters (OpenShared OpenLast first reads shared last thread₃ said₃)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open OnBytes (TableKey)

-- The comparison is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- The field line of LastChainDebtsAtTheNames at border358: the guards' run over the last chain's
four members returns from the door's shape at border358. -/
theorem lastRunAt_border358 : lastRunAt border358 = true := by
  kernel_rfl

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- Under the head at a return, made, a P : OpenLast h O, and the four debts standRest,
readyReturns, tied and indexInRange: the sockets owes₃ and yes₃ at the letters' values, with no
fall. The two other debts of LastChainDebtsAtTheNames, the first chain's whole run on shapes and the
closed Bool at its end, are paid at border358. Implications from a stand of the thread; no stand is
shown. -/
theorem sockets_three_at_358 (h : HeadAtReturn files A) (made : baseMaker files = .ok A)
    {O : OpenShared A} (P : OpenLast h O)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) {w₀ : FullSizeMatrix} {rc : IndexCommitterCoins}
    {x : ProofFile.Inst} {k : Coins A.B}
    (standRest : StandRest (Zp := A.Z) (Np := h.places) (cF := h.firstChain) (thread₃ h P R)
      (said₃ h P R) P.ownMany)
    (readyReturns : ready h.description A.B A.H w₀ rc x k = .ok R)
    (tied : TiedAtRun (A := A) (reads h) R.own R.common)
    (indexInRange : A.H.inRange R.common.w₀ = true) :
    Socket.owes₃ h (first h) (reads h) (shared h O) (lastParts h (first h) (last h P)) R ∧
      Socket.yes₃ h (first h) (reads h) (shared h O) (lastParts h (first h) (last h P)) R [] :=
  sockets_three_at_the_letters h made P R
    ⟨standRest, runOnShapes_toEnd, lastRunAt_border358, readyReturns, tied, indexInRange⟩

end ShapeLines

#print axioms ShapeLines.lastRunAt_border358
#print axioms ShapeLines.sockets_three_at_358
