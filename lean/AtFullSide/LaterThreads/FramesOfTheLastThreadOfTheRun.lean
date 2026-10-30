-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/LaterThreads/FramesOfTheLastThreadOfTheRun.lean: CONDITIONAL: on the head at a return of the maker
and ON TWO CLOSED FACTS THAT STAND IN NO LIBRARY THAT THIS FILE IMPORTS: wholeRun and line. THE FULL SIZE ALONE.

NO THEOREM OF THIS LIBRARY THAT NAMES THE LAST CHAIN's THREAD SHOWS A STAND OF IT AT ANY BORDER
BEYOND 0 BUT FROM A PREMISE THAT HOLDS ONE. Had: the door (`doorAtTheTerm`,
AtFullSide/Honest/ThreadsAtTheTerm.lean): a stand at border 0 behind stands of the two earlier
threads at their ends and the start's yes, where both ends hold opened columns, under
`ThreadFieldsP` and ready's return; and the general rule `thread_in_second`
(Johnson/Desc/ProofFile/Honest/Law/InsideFile.lean): for three invariants that its premises have
carried by every member, at the two starts and through the door, at a run of runC that returns,
where ready returns, the plan is fit and served, the draws are due and no silent stop fires, a
called part of the second chain is reached from a state at which the third invariant holds. No
statement joins them into one that ends in a stand of this thread. Each statement is an implication
from the thread's stand in front of a member. One of the five statements at each of the two members.

What is here. THE YES OF THE FRAME's TWO MEMBERS OF THE LAST CHAIN (the chain's end, number 3; "the taken trees'
sources", number 1) WITH EVERY PREMISE ON THE VERIFIER's DESCRIPTION BROUGHT DOWN TO TWO CLOSED FACTS at a written
shape c of the first chain's end.

  lastRunAt c             **THE CLOSED Bool**: what is handed is read off c (handedOf), the shared chain's end
                          is the written one (writtenSharedEnd), and from the door's shape of the two the
                          guards' run over the last chain's four members returns (lastRunClosed)
  last_end_accepts_of_the_run, taken_sources_accept_of_the_run   **AcceptedS at 3 and at 1**

THE PREMISES.
  wholeRun : RunsAll 0 358 startShA c: the run on shapes over the first chain's 358 members, at the stored
    full-size files, returns c: closed lines of the kernel, in a library of their own: at c := `border358`
    by `runOnShapes_toEnd` (ShapeLines/FirstChainRuns.lean).
  line : lastRunAt c = true: one closed line at c. EVALUATED HERE AT NO c; at c := `border358` by
    `lastRunAt_border358` (ShapeLines/LastChain/SocketsThreeAt358.lean), a comparison by Lean's kernel.
  sizes : the run's own instance's key has the plan's sizes (paid at the served instance:
    AtFullSide/LaterThreads/KeySizesAtTheRun.lean).
  tied : what is said of the run gives SaidField at BaseTied: the threads' own letter.
  sharedReads, sharedParts, sharedInput: a thread of the shared chain, of which nothing is read but its
    list of members (AtFullSide/LaterThreads/SharedEndShape.lean's head).

Of the two yeses only the one at 3 lies on the road to the sockets. The road that the sockets' law takes to
the yes at 1 is the rider's (`five_at_last_one_late`, AtFullSide/Frames/LastAtValues.lean);
taken_sources_accept_of_the_run is a second witness, which that road does not call.
By what. last_end_accepts, taken_sources_accept (LastRunClosed.lean) · first_end_shape_of_run
(FirstEndShapeOfRun.lean: the first chain's share) · shared_end_at_the_head (SharedEndShape.lean: the
shared chain's).

Not shown here. The two closed facts. If the run on shapes refused at one member, or the line were false
at the c that it returns, all of this would be empty. PlaysS, BehindS, ExchangeS, RidesPastS at these
members. Nothing on soundness, on completeness, on hiding or on any other property.
No property is claimed.
-/
import AtFullSide.LaterThreads.LastRunClosed
import AtFullSide.LaterThreads.SharedEndShape
import AtFullSide.LaterThreads.FirstEndShapeOfRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.LaterThreads
open ProofFile.Honest
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders SharedThreadParts
  LastThreadParts lastThread)
open Johnson.AtFull.Shape
open VerifiableInference.Desc.Third (S₃)

/-- **THE CLOSED Bool AT A WRITTEN SHAPE c OF THE FIRST CHAIN's END.** -/
def lastRunAt (c : ShA) : Bool :=
  match handedOf c, writtenSharedEnd with
  | some a, some b => lastRunClosed (doorShape a b)
  | _, _ => false

/-- What the Bool's yes holds. -/
theorem lastRunAt_inv {c : ShA} (line : lastRunAt c = true) :
    ∃ a b, handedOf c = some a ∧ writtenSharedEnd = some b ∧
      lastRunClosed (doorShape a b) = true := by
  unfold lastRunAt at line
  cases ha : handedOf c with
  | none =>
    rw [ha] at line
    cases line
  | some a =>
    cases hb : writtenSharedEnd with
    | none =>
      rw [ha, hb] at line
      cases line
    | some b =>
      rw [ha, hb] at line
      exact ⟨a, b, rfl, rfl, line⟩

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
  (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
  (fall : Nat → S₃ → List Fmt.Drawn → Option String) {c : ShA}

/-- CONDITIONAL on h, wholeRun, line, sizes and tied. **THE LAST CHAIN's END SAYS YES AT EVERY STAND
IN FRONT OF IT.** An implication from the thread's stand; no theorem of this library that names this
thread shows a stand of it at any border beyond 0 but from a premise that holds one. -/
theorem last_end_accepts_of_the_run (wholeRun : RunsAll 0 358 startShA c)
    (line : lastRunAt c = true) (sizes : KeyHasTheSizes h w.x)
    (tied : ∀ n k m, Said n k m → SaidField (lastThread h first reads parts w)
      (BaseTied h.description (lastThread h first reads parts w)) n k m)
    (sharedReads : IndexReaders W₀ Rc) {Wt : Type} (sharedParts : SharedThreadParts A Wt)
    (sharedInput : Common W₀ Rc OnBytes.TableKey) :
    AcceptedS (lastThread h first reads parts w) Said fall 3 := by
  obtain ⟨a, b, ha, hb, closed⟩ := lastRunAt_inv line
  obtain ⟨b', hb', sharedEnd⟩ := shared_end_at_the_head h sharedReads sharedParts sharedInput
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  exact last_end_accepts h first reads parts w Said fall closed
    (first_end_shape_of_run h wholeRun ha) sharedEnd sizes tied

/-- CONDITIONAL on h, wholeRun, line, sizes and tied. **"THE TAKEN TREES' SOURCES" SAYS YES AT EVERY
STAND IN FRONT OF IT.** An implication from the thread's stand; no theorem of this library that
names this thread shows a stand of it at any border beyond 0 but from a premise that holds one. -/
theorem taken_sources_accept_of_the_run (wholeRun : RunsAll 0 358 startShA c)
    (line : lastRunAt c = true) (sizes : KeyHasTheSizes h w.x)
    (tied : ∀ n k m, Said n k m → SaidField (lastThread h first reads parts w)
      (BaseTied h.description (lastThread h first reads parts w)) n k m)
    (sharedReads : IndexReaders W₀ Rc) {Wt : Type} (sharedParts : SharedThreadParts A Wt)
    (sharedInput : Common W₀ Rc OnBytes.TableKey) :
    AcceptedS (lastThread h first reads parts w) Said fall 1 := by
  obtain ⟨a, b, ha, hb, closed⟩ := lastRunAt_inv line
  obtain ⟨b', hb', sharedEnd⟩ := shared_end_at_the_head h sharedReads sharedParts sharedInput
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  exact taken_sources_accept h first reads parts w Said fall closed
    (first_end_shape_of_run h wholeRun ha) sharedEnd sizes tied

end AtFullSide.LaterThreads

#print axioms AtFullSide.LaterThreads.last_end_accepts_of_the_run
#print axioms AtFullSide.LaterThreads.taken_sources_accept_of_the_run
