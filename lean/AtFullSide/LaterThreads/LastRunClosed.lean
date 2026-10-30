-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/LaterThreads/LastRunClosed.lean: CONDITIONAL: on the head at a return of the maker, ON ONE
CLOSED Bool, and on the two earlier chains' shares. THE FULL SIZE ALONE.
THE Bool IS EVALUATED NOWHERE IN THIS FILE. The side library ShapeLines evaluates it in Lean's kernel at
the written value `border358` (`last_run_at_border358`, ShapeLines/LastChain/LastRunAtBorder358.lean),
with controls; one line on a limit of it says: with the mask set to none the run returns all the same, so
the yes does not depend on the mask (`lastRunControl_withoutMask`, ShapeLines/LastChain/LastRunControls.lean):
this file does not import that
library. The shared chain's share is had under the head (AtFullSide/LaterThreads/SharedEndShape.lean),
the first chain's from a closed run on shapes (AtFullSide/LaterThreads/FirstEndShapeOfRun.lean).

What is here. THE PREMISE runReturns OF AtFullSide/LaterThreads/FramesOfTheLastThread.lean AS ONE CLOSED
Bool: a test with code that names no public file, no head and no letter: the guards' run over the last
chain's four members at the WRITTEN shape of the test on the table, the WRITTEN rounds and the WRITTEN
place of the request's own proximity test. And the yes of the frame's two members of the last chain
with that Bool and the two shares in the place of runReturns and door.

  writtenLastShape S     the last chain's shape, guards and tests at the written place piWFull
  lastRunClosed a        **THE CLOSED Bool**: at the typed sizes (realSized) the run over the four
                         members returns from the shape a
  yes_is_written         under the head the run at the head's own letters is the run at the written
                         values
  runReturns_of_closed   **the Bool gives runReturns under the head**
  last_end_accepts, taken_sources_accept   **AcceptedS at 3 and at 1** from the Bool at
                         doorShape a b, the two shares at a and b, sizes and tied

By what. written_at_head (Honest/K12/FitAtHead.lean): the shape is the typed one. reads_head_W,
facts_WFull (Honest/K12/Sim/FirstAnyAtHeadW.lean), nums_head_W, alike_head_W
(AtFullSide/K12/RestTiesAtHeadW.lean), k12_rounds (Johnson/Desc/K12/FrameLaws.lean): the rounds are the
written ones. testCore_alike (Honest/K12/FrontAtHead.lean): the own test's guards read no more of the
place than alike_head_W ties.

Not shown here. THAT THE Bool IS TRUE AT ANY a. It can be evaluated only at a written shape: a is to
be read off the first chain's end's written shape and b off the shared chain's: neither value is
named here. The two shares. NO THEOREM OF THIS LIBRARY THAT NAMES THE LAST CHAIN's THREAD SHOWS A
STAND OF IT AT ANY BORDER BEYOND 0 BUT FROM A PREMISE THAT HOLDS ONE. Had: the door
(`doorAtTheTerm`, AtFullSide/Honest/ThreadsAtTheTerm.lean): a stand at border 0 behind stands of the
two earlier threads at their ends and the start's yes, where both ends hold opened columns, under
`ThreadFieldsP` and ready's return; and the general rule `thread_in_second`
(Johnson/Desc/ProofFile/Honest/Law/InsideFile.lean): for three invariants that its premises have
carried by every member, at the two starts and through the door, at a run of runC that returns,
where ready returns, the plan is fit and served, the draws are due and no silent stop fires, a
called part of the second chain is reached from a state at which the third invariant holds. No
statement joins them into one that ends in a stand of this thread. Nothing on soundness, on
completeness, on hiding or on any other property.
No property is claimed.
-/
import AtFullSide.LaterThreads.DoorOnShapes
import AtFullSide.K12.RestTiesAtHeadW
import Johnson.Desc.ProofFile.Honest.K12.FitAtHead
import Johnson.Desc.ProofFile.Honest.K12.FrontAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.LaterThreads
open OnBytes.Params (LinShape)
open ProofFile.Honest
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastThreadParts lastThread)
open ProofFile.Honest.K12.Light (Alike written_at_head reads_head_W facts_WFull nums_head_W alike_head_W
  testCore_alike)
open ProofFile.Honest.K12.AtProof (fourOf)
open AtPublicFiles.AtFiles (Z₃ Sh₃ SharedSh gOwn)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open H2K.Member (piWFull)
open ToldDesc (p14At ownAt)

/-- **The last chain's shape, guards and tests on values at the written place of the own test.** -/
def writtenLastShape (S : LinShape) : Shape S₃ :=
  Z₃ S (proximityTestKind guardedProximityTestParts piWFull : Block T12 Unit).rounds (gOwn piWFull) fun _ _ _ => true

/-- **THE CLOSED Bool**: at the typed sizes the guards' run over the last chain's four members returns
from the shape a. By `Option.all` it would be true for nothing if realSized were none: read alone, its yes
says less than this; `runReturns_of_closed` takes realSized = some from `yes_is_written` under the head. -/
def lastRunClosed (a : Sh₃) : Bool :=
  realSized.all fun sized => (writtenLastShape sized.1.shape).yes a 4

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- CONDITIONAL on h. **Under the head the run at the head's own letters is the run at the written
values.** -/
theorem yes_is_written (h : HeadAtReturn files A) (a : Sh₃) (n : Nat) :
    ∃ sized, realSized = some sized ∧
      (lastShape A.Z h.places).yes a n = (writtenLastShape sized.1.shape).yes a n := by
  obtain ⟨x, typed, written⟩ := written_at_head h.head.toAtMg
  have shape : (p14At A.Z).S = x.shape := written.shape
  have rounds : (ownAt h.places).rounds = (proximityTestKind guardedProximityTestParts piWFull : Block T12 Unit).rounds := by
    show (proximityTestKind guardedProximityTestParts (fourOf h.places).W : Block T12 Unit).rounds = _
    refine Option.some.inj ?_
    rw [← VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts _ (reads_head_W h.head.toAtMg).2.2.2,
      ← VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts _ facts_WFull.plan,
      nums_head_W h.head.toAtMg]
  have alike : Alike (ownPlace h.places) piWFull := alike_head_W h.head.toAtMg
  have guards : gOwn (ownPlace h.places) = gOwn piWFull := by
    funext c
    unfold gOwn
    rw [testCore_alike alike]
  refine ⟨_, typed, ?_⟩
  unfold lastShape writtenLastShape
  rw [shape, rounds, guards]

/-- CONDITIONAL on h and closed. **THE CLOSED Bool GIVES runReturns UNDER THE HEAD.** -/
theorem runReturns_of_closed (h : HeadAtReturn files A) {a : Sh₃} (closed : lastRunClosed a = true) :
    (lastShape A.Z h.places).yes a 4 = true := by
  obtain ⟨sized, typed, same⟩ := yes_is_written h a 4
  rw [same]
  unfold lastRunClosed at closed
  rw [typed] at closed
  exact closed

variable (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
  (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
  (fall : Nat → S₃ → List Fmt.Drawn → Option String) {a : HandedShape} {b : SharedSh}

/-- CONDITIONAL on h, closed, the two shares, sizes and tied. **THE LAST CHAIN's END SAYS YES AT
EVERY STAND IN FRONT OF IT.** An implication from the thread's stand; no theorem of this library
that names this thread shows a stand of it at any border beyond 0 but from a premise that holds one.
-/
theorem last_end_accepts (closed : lastRunClosed (doorShape a b) = true)
    (firstEnd : FirstEndHasTheShape h a) (sharedEnd : SharedEndHasTheShape h b)
    (sizes : KeyHasTheSizes h w.x)
    (tied : ∀ n k m, Said n k m → SaidField (lastThread h first reads parts w)
      (BaseTied h.description (lastThread h first reads parts w)) n k m) :
    AcceptedS (lastThread h first reads parts w) Said fall 3 :=
  accepted_at_the_last_end h first reads parts w Said fall (runReturns_of_closed h closed)
    (door_of_the_two_ends h firstEnd sharedEnd) sizes tied

/-- CONDITIONAL on h, closed, the two shares, sizes and tied. **"THE TAKEN TREES' SOURCES" SAYS YES
AT EVERY STAND IN FRONT OF IT.** An implication from the thread's stand; no theorem of this library
that names this thread shows a stand of it at any border beyond 0 but from a premise that holds one.
-/
theorem taken_sources_accept (closed : lastRunClosed (doorShape a b) = true)
    (firstEnd : FirstEndHasTheShape h a) (sharedEnd : SharedEndHasTheShape h b)
    (sizes : KeyHasTheSizes h w.x)
    (tied : ∀ n k m, Said n k m → SaidField (lastThread h first reads parts w)
      (BaseTied h.description (lastThread h first reads parts w)) n k m) :
    AcceptedS (lastThread h first reads parts w) Said fall 1 :=
  accepted_at_the_taken_sources h first reads parts w Said fall (runReturns_of_closed h closed)
    (door_of_the_two_ends h firstEnd sharedEnd) sizes tied

end AtFullSide.LaterThreads

#print axioms AtFullSide.LaterThreads.yes_is_written
#print axioms AtFullSide.LaterThreads.runReturns_of_closed
#print axioms AtFullSide.LaterThreads.last_end_accepts
#print axioms AtFullSide.LaterThreads.taken_sources_accept
