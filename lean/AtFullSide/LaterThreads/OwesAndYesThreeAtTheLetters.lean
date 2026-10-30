-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/LaterThreads/OwesAndYesThreeAtTheLetters.lean: CONDITIONAL. THE FULL SIZE ALONE.

THE YES AT MEMBERS 0 AND 1 IS TAKEN OUT OF THE INVARIANT IN FRONT, NOT SHOWN OF THE RUN: the stand at
border 0 holds `doorRider`'s eleven tests and the test `tiedAheadB` at the start's record, the stand at
border 1 holds what `tiedRider` says, and the yes is read off these. So THIS YES IS HALF A SENTENCE
WITHOUT THE ONE OBJECT's THREE FIELDS `doorRides`, `doorFive` AND `doorTrees`, which speak of what the door
lays into that stand. Nothing here says that the last chain accepts.

What is here. `OwesS` AND `YesS` AT THE NAMES `thread₃`, `said₃` AND `falls₃`
(AtFullSide/Honest/TheLettersLast.lean: `thread₃` is `lastThread` at the run's own input, with the
two earlier chains' ends a function of the input): one instance of
`owes_and_yes_at_the_last_thread_finest`
(AtFullSide/LaterThreads/OwesAndYesAtTheLastThreadFinest.lean). AT THAT VALUE ELEVEN OF ITS FIFTEEN
HYPOTHESES ARE PROVED: the riders, keeps, the trees taken over, the tables and the counts by
unfolding, the job being the filling's by the hole's own field; the count of rounds in front by
`lastFront_is_front` (AtFullSide/Honest/TheLettersFit.lean); the three on the own clause for
nothing, since it is "True" there; the field letter by a projection; the three widths by `widthsAtW`
(AtFullSide/K12/Part4/WidthsAtW.lean); a twelfth, the key's sizes, is brought down to three facts on
the run, hypotheses here.

  `key_sizes_of_the_tied_run` the key of the run's instance has the plan's sizes, from three facts
  on the run.
  `LastChainDebtsAtTheNames` WHAT IS A HYPOTHESIS HERE: one field a debt.

  `owes_and_yes_three_at_the_letters`   **the two.**

Not shown here. EVERY FIELD OF `LastChainDebtsAtTheNames` IS A HYPOTHESIS HERE. They are met
together at every tied run by `lastDebts_at_a_tied_run` (AtFullSide/Honest/LastSocketsOfTheClosedFacts.lean),
given wholeRun and line, with that file's limit on the coins. O AND P ARE THE LETTERS' NAMED HOLES, letters here: the one object's value
lays O at zeros and P at `openLast` (AtFullSide/Honest/TheOneObjectValue.lean, whose head says: «this does not show that a
thread stands at a run»); P holds two propositions.
standRest HOLDS THREE CLAUSES ON A STAND IN FRONT OF THE LAST PROXIMITY TEST: proved at the letters
by `standRest_at_letters` (AtFullSide/K12/Part4/StandRestAtTheLetters.lean; NOT IN FRONT OF A LAW
OVER COINS). wholeRun AND line ARE TWO CLOSED FACTS THAT STAND IN NO LIBRARY THAT THIS FILE IMPORTS:
the side library ShapeLines holds them at the shape `border358`: `runOnShapes_toEnd`
(ShapeLines/FirstChainRuns.lean) and `lastRunAt_border358`
(ShapeLines/LastChain/SocketsThreeAt358.lean). THE RIDER AT BORDER 0 MOVES A HYPOTHESIS TO THE DOOR:
not counted here. NO THEOREM OF THIS LIBRARY THAT NAMES THIS THREAD SHOWS A STAND OF IT AT ANY
BORDER BEYOND 0 BUT FROM A PREMISE THAT HOLDS ONE. Had: the door (`doorAtTheTerm`,
AtFullSide/Honest/ThreadsAtTheTerm.lean): a stand at border 0 behind stands of the two earlier
threads at their ends and the start's yes, where both ends hold opened columns, under
`ThreadFieldsP` and ready's return; and the general rule `thread_in_second`
(Johnson/Desc/ProofFile/Honest/Law/InsideFile.lean): for three invariants that its premises have
carried by every member, at the two starts and through the door, at a run of runC that returns,
where ready returns, the plan is fit and served, the draws are due and no silent stop fires, a
called part of the second chain is reached from a state at which the third invariant holds. No
statement joins them into one that ends in a stand of this thread. Every statement here is an
implication from the thread's stand in front of a member. Where a stand would come from: at a tied
run a value of the one object
gives the three threads' invariants (`TheOneObject.threads`, `atEveryTiedRunAtItsThreads`,
AtFullSide/Honest/TheOneObject.lean), this thread's stand being I₃ of `ThreadsCJ`, laid at the last
chain's start behind stands of the two earlier threads at their ends (its field b₃).
AT THE BASE MAKER's RETURN: not at the online maker's. Nothing on hiding. Nothing on soundness, on completeness or on
any other property.

No property is claimed.
-/
import AtFullSide.LaterThreads.OwesAndYesAtTheLastThreadFinest
import AtFullSide.Honest.ThreadsAtTheTerm
import Johnson.Bind.ForProver.FiveFieldsAt
import Johnson.Desc.ProofFile.Honest.Thread.EntersFirst
import AtFullSide.Honest.TheLettersFit
import AtFullSide.K12.Part4.WidthsAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.LaterThreads
open ProofFile ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (baseMaker matrixInput)
open ProofFile.Honest.K12.AtFile (StandRest)
open AtFullSide.Honest (TiedAtRun)
open AtFullSide.Honest.TheLetters (OpenShared OpenLast first reads shared later last firstRounds
  lastFront lastFront_is_front toCommon thread₃ said₃ falls₃)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open OnBytes (TableKey)
open Johnson.AtFull.Shape (ShA RunsAll startShA)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- CONDITIONAL: on h, returns, tied and inRange. **THE KEY OF THE RUN's INSTANCE HAS THE PLAN's
SIZES**: ready lays the instance's key into the common input; where the index is in range the tie
says that the committer makes that key; and such a key has the plan's sizes (the field key of
`fiveFieldsK14_inScope`, Johnson/Bind/ForProver/FiveFieldsAt.lean). -/
theorem key_sizes_of_the_tied_run (h : HeadAtReturn files A) (reads : IndexReaders FullSizeMatrix IndexCommitterCoins)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) {w₀ : FullSizeMatrix} {rc : IndexCommitterCoins} {x : ProofFile.Inst}
    {k : Coins A.B} (returns : ready h.description A.B A.H w₀ rc x k = .ok R)
    (tied : TiedAtRun (A := A) reads R.own R.common)
    (inRange : A.H.inRange R.common.w₀ = true) : KeyHasTheSizes h R.own.x := by
  obtain ⟨-, tr, -, hown, hcom, -, -, -⟩ := ready_ok returns
  have made := tied.key inRange
  have e : R.common.key = R.own.x.pub.key := by
    rw [hcom, hown]
    exact key_at_return h x
  rw [e] at made
  exact (Bind.ForProver.fiveFieldsK14_inScope h.head.scope h.head.laid.pub
    (Desc.K14.beforePointOf h.places)).key ⟨_, _, R.own.x.pub.key⟩ made

/-- **WHAT `OwesS` AND `YesS` AT `thread₃` AND `said₃` TAKE AS HYPOTHESES.** A definition, meant
as a hypothesis: each field one premise. O, P: the letters' named holes. firstEnd: the shape that
the run on shapes gives at the first chain's end. The last four: the run. -/
structure LastChainDebtsAtTheNames (h : HeadAtReturn files A) {O : OpenShared A}
    (P : OpenLast h O) (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) (firstEnd : ShA)
    (w₀ : FullSizeMatrix) (rc : IndexCommitterCoins) (x : ProofFile.Inst) (k : Coins A.B) : Prop where
  /-- what a stand in front of the last proximity test takes as hypotheses: three clauses: the field
  and the
  ends, the trees taken over, what the test's rows say: `standRest_at_letters`
  (AtFullSide/K12/Part4/StandRestAtTheLetters.lean), at the letters -/
  standRest : StandRest (Zp := A.Z) (Np := h.places) (cF := h.firstChain) (thread₃ h P R)
    (said₃ h P R) P.ownMany
  /-- the run on shapes over the first chain's 358 members returns firstEnd: a closed fact
  -/
  wholeRun : RunsAll 0 358 startShA firstEnd
  /-- the guards' run over the last chain's four members returns from the door's shape at firstEnd:
  one closed Bool: `lastRunAt_border358` (ShapeLines/LastChain/SocketsThreeAt358.lean), at the shape `border358` -/
  line : lastRunAt firstEnd = true
  /-- ready returns the run. Holder: the tied run -/
  readyReturns : ready h.description A.B A.H w₀ rc x k = .ok R
  /-- what the kinds' laws ask of the run's input: of it the key's clause is spent.
  -/
  tied : TiedAtRun (A := A) (reads h) R.own R.common
  /-- the run's index is in range. Holder: `indexInRange_at_a_tied_run`
  (AtFullSide/Honest/LastSocketsOfTheClosedFacts.lean), at a TiedRun, given made -/
  indexInRange : A.H.inRange R.common.w₀ = true

/-- CONDITIONAL: on h, made and the hypotheses D. **`OwesS` AND `YesS` AT `thread₃`, `said₃` AND
`falls₃`.** Implications from the thread's stand in front of each member; no theorem of this library
that names this thread shows a stand of it at any border beyond 0 but from a premise that holds one.
-/
theorem owes_and_yes_three_at_the_letters (h : HeadAtReturn files A)
    (made : baseMaker files = .ok A) {O : OpenShared A} (P : OpenLast h O)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) {firstEnd : ShA} {w₀ : FullSizeMatrix} {rc : IndexCommitterCoins}
    {x : ProofFile.Inst} {k : Coins A.B} (D : LastChainDebtsAtTheNames h P R firstEnd w₀ rc x k) :
    OwesS (thread₃ h P R) (said₃ h P R) ∧
      YesS (thread₃ h P R) (said₃ h P R) (fallsBy (falls₃ h) h.description.second.blocksInOrder) := by
  obtain ⟨job, isTheJob, top⟩ := owes_and_yes_at_the_last_thread_finest
    (W₂ := Common FullSizeMatrix IndexCommitterCoins TableKey) h matrixInput OnBytes.HonestTrace.Sz.ref openHonest made
  obtain rfl : job = P.ownMany := Option.some.inj (isTheJob.symm.trans P.ownIsTheFilling)
  have both := top (first h) (reads h) (last h P) R.own (said₃ h P R) (fun _ _ _ => True) firstEnd
    (firstRounds h) (lastFront h) (toCommon (A := A)) (first h).script.table
    (later (h := h) O).table (first h).script.fixed (later (h := h) O).fixed
    (fallsBy (falls₃ h) h.description.second.blocksInOrder) (reads h) WtShared (shared h O) R.common
    { ridersAreTheTiedOnes := rfl
      keepsAreTheLastKeeps := rfl
      takenAreTheWritten := rfl
      tablesAreLaid := rfl
      fixedAreLaid := rfl
      roundsInFront := lastFront_is_front h P R
      widths := ProofFile.Honest.K12.Part4.widthsAtW matrixInput OnBytes.HonestTrace.Sz.ref openHonest
        h.head made _ _ _ _ _ _ _
      standRest := D.standRest
      ownAllowsTheSources := fun _ => trivial
      ownAllowsTheEnd := fun _ => trivial
      ownHoldsBehindTheTest := fun _ _ _ _ _ _ _ _ _ _ _ => trivial
      wholeRun := D.wholeRun
      line := D.line
      keyHasTheSizes :=
        key_sizes_of_the_tied_run h (reads h) R D.readyReturns D.tied D.indexInRange
      saidGivesTheField := fun _ _ _ said => said.1 }
  exact ⟨both.1, both.2⟩

end AtFullSide.LaterThreads

#print axioms AtFullSide.LaterThreads.owes_and_yes_three_at_the_letters
