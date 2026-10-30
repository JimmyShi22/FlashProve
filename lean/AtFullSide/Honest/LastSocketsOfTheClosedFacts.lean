-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/LastSocketsOfTheClosedFacts.lean

This file proves Socket.owes₃ and Socket.yes₃, two statements on the second chain of the proof
file's description, at every TiedRun, from two closed premises on a symbolic run of the description.
The file contains no definition.

Terms.
  * The proof file's description has three chains of sub-protocols: the first, the shared and the
    second chain (some Lean names call the second chain the last one). For each chain the library
    defines a Thread T and an invariant ThrS T Said b
    (Johnson/Desc/ProofFile/Honest/Thread/Said.lean) on the prover's coins, the description's state
    and the prover's state in front of sub-protocol number b.
  * OwesS T Said and YesS T Said fl (Johnson/Desc/ProofFile/Honest/Thread/PaysS.lean) are, for every
    sub-protocol b of the chain, implications whose premise is ThrS T Said b. OwesS concludes four
    properties of the prover's step (PlaysS, BehindS, ExchangeS, RidesPastS). YesS concludes that
    the sub-protocol's own step accepts (AcceptedS), where no stopping rule of the sub-protocol
    fires and the parameter fl, which lists the events at which the prover uses a default branch,
    does not fire. Socket.owes₃ and Socket.yes₃ (TheSocketStatements.lean of this folder) are OwesS
    and YesS at the second chain's Thread.
  * TiedRun h hr (TheOneObject.lean of this folder) is one run of the base prover at a served
    request whose instance carries the out-of-domain sample of the run's own private input. It
    consists of the copy number, the private input, the instance, the prover's coin, and the value
    that the function ready returned there.
  * O : TheLetters.OpenShared A and P : TheLetters.OpenLast h O are the two auxiliary parameters of
    the structures in TheOneObject.lean (their fields open₂ and open₃). P contains propositions, so
    a value of P is itself a premise.
  * The base construction is onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling, and HeadAtReturn
    Z A collects the library's facts on a return A of it (see the header of
    AtFullSide/Honest/CompleteAtTheFiles.lean).
  * wholeRun : RunsAll 0 358 startShA firstEnd (Johnson/AtFull/Shape/JoinAll.lean) says that the
    symbolic run on shapes over the 358 sub-protocols of the first chain, from startShA, returns the
    shape firstEnd. line : lastRunAt firstEnd = true
    (AtFullSide/LaterThreads/FramesOfTheLastThreadOfTheRun.lean) says that a Boolean check on the
    second chain, evaluated at firstEnd, succeeds.

Main statements. Beside what each entry names, the premises are at most h : HeadAtReturn Z A,
readFiles Z = .ok pp (hr), the return A of the base construction (made), and the parameters O and P.
The last two theorems also assume the two instances Inhabited P5J.TS and Inhabited Desc.K14.St, as
TheOneObject.lean does.
  * indexInRange_at_a_tied_run: at a TiedRun the index of the shared input is in range. The function
    ready returned, so the request has a trace (ready_ok), and a request with a trace has its index
    in range (inRange_of_trace, TheOneObject.lean).
  * tied_at_every_tied_run: Socket.tied at every TiedRun. This is TiedAtRun: the public part of the
    instance is that of a typed instance, and where the index is in range the run's key is one that
    the committer makes of the index and the coins. The statement has the type of the field tied of
    TheThreadsHalf.
  * lastDebts_at_a_tied_run: from wholeRun and line, the structure LastChainDebtsAtTheNames
    (AtFullSide/LaterThreads/OwesAndYesThreeAtTheLetters.lean) at a TiedRun. Its field standRest is
    standRest_at_letters, readyReturns is the run's own field, tied and indexInRange are the two
    theorems above, and wholeRun and line are the premises.
  * lastSockets_of_the_closed_facts: from wholeRun and line, Socket.owes₃ and Socket.yes₃ at every
    TiedRun, the second at the empty list [] of default-branch events.

Limits.
  * wholeRun and line are premises, at a shape firstEnd that is a variable here. Neither is proved
    in this file. By its definition RunsAll holds vacuously where publicOfO returns no value at the
    stored full-size files.
  * These statements bear the library's label "NOT IN FRONT OF A LAW OVER COINS". What the label
    bars, and what counts as a law over coins, is set out in one place:
    Johnson/Bind/ForProver/FiveFieldsAt.lean, under "A limit on the coins". The reason here:
    TiedAtRun ties a run's key to the run's own index and coins (validAt; see also
    AtFullSide/HonestTrace/TiedAtTheCommittersSample.lean). A bound on the probability that an
    honest proof is rejected is not a law over coins in that sense. Nothing on hiding follows from
    them. This applies to tied_at_every_tied_run in particular.
  * The statements are about the return of the base construction, not about the return of
    onlineMaker.
  * Socket.owes₃ and Socket.yes₃ are implications whose premise is that the second chain's invariant
    holds in front of each sub-protocol. Nothing in this file shows that this invariant holds at any
    run. In particular, the condition last.rides 0 on the second chain's first state is a statement
    of its own, Socket.doorRides (TheSocketStatements.lean of this folder). It is not proved here,
    nor in AtFullSide/LaterThreads/OwesAndYesThreeAtTheLetters.lean, on which these proofs rest.
  * The statements hold for the full-size layout and for the format's second hash function,
    OnBytes.secondHashFunction, alone.
  * The proofs in this file only combine theorems of other files.
  * Nothing on soundness, completeness or hiding.

Built on.
  * ready_ok (Johnson/Desc/ProofFile/Honest/Law/Run.lean) and inRange_of_trace (TheOneObject.lean of
    this folder).
  * tied_at_a_tied_instance (AtFullSide/HonestTrace/TiedAtATiedInstance.lean).
  * standRest_at_letters (AtFullSide/K12/Part4/StandRestAtTheLetters.lean).
  * sockets_three_at_the_letters (AtFullSide/LaterThreads/SocketsThreeAtTheLetters.lean).
-/
import AtFullSide.Honest.TheOneObject
import AtFullSide.K12.Part4.StandRestAtTheLetters
import AtFullSide.LaterThreads.SocketsThreeAtTheLetters
import AtFullSide.HonestTrace.TiedAtATiedInstance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- The default instance Inst.Model.Scl.ref is removed, so that every statement that uses a table of
scales names that table explicitly. -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput matrixFilling tableCoins)
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.Committed AtPublicFiles.TheFalls
open OnBytes.Slice (frS)
open VerifierAndGoals (PublicFiles readFiles)

/- The same three local instances as in TheOneObject.lean, where the structures are defined. -/
local instance (priority := high) nonemptyPadZ_lastSocketsClosed : Nonempty PadZ :=
  pads_nonempty frS 402653181

local instance (priority := high) nonemptyRunValue_lastSocketsClosed : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_lastSocketsClosed : Inhabited RunValue :=
  ⟨fun _ => 0⟩

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)
  {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {O : TheLetters.OpenShared A}
  (P : TheLetters.OpenLast h O)

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- At a TiedRun the index of the shared input is in range. -/
theorem indexInRange_at_a_tied_run
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (r : TiedRun h hr) :
    A.H.inRange r.R.common.w₀ = true := by
  obtain ⟨-, tr, traced, -, common, -⟩ := ready_ok r.ready
  rw [common]
  exact inRange_of_trace made (by rw [traced]; rfl)

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- TiedAtRun, the two facts on a run's own input that the sub-protocols' theorems use, holds at
every TiedRun. -/
theorem tied_at_every_tied_run :
    ∀ r : TiedRun h hr, Socket.tied (A := A) (TheLetters.reads h) r.R :=
  fun r => HonestTraceRun.Meets.tied_at_a_tied_instance h (TheLetters.reads h) (fun _ => rfl) _ _ _
    _ _ _ _ _ r.tied.2 r.ready

/-- The six fields of LastChainDebtsAtTheNames at a TiedRun, from the two closed premises wholeRun
and line. -/
theorem lastDebts_at_a_tied_run
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    {firstEnd : Johnson.AtFull.Shape.ShA}
    (wholeRun : Johnson.AtFull.Shape.RunsAll 0 358 Johnson.AtFull.Shape.startShA firstEnd)
    (line : AtFullSide.LaterThreads.lastRunAt firstEnd = true) (r : TiedRun h hr) :
    AtFullSide.LaterThreads.LastChainDebtsAtTheNames h P r.R firstEnd r.w.1
      (tableCoins Z r.w.2.1) r.x (pursesOf r.c) :=
  { standRest := AtFullSide.K12.Part4.standRest_at_letters h made P r.R
    wholeRun := wholeRun
    line := line
    readyReturns := r.ready
    tied := tied_at_every_tied_run h hr r
    indexInRange := indexInRange_at_a_tied_run h hr made r }

/-- Socket.owes₃ and Socket.yes₃ at every TiedRun, from the two closed premises wholeRun and line.
-/
theorem lastSockets_of_the_closed_facts
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    {firstEnd : Johnson.AtFull.Shape.ShA}
    (wholeRun : Johnson.AtFull.Shape.RunsAll 0 358 Johnson.AtFull.Shape.startShA firstEnd)
    (line : AtFullSide.LaterThreads.lastRunAt firstEnd = true) :
    ∀ r : TiedRun h hr,
      Socket.owes₃ h (TheLetters.first h) (TheLetters.reads h) (TheLetters.shared h O)
          (lastParts h (TheLetters.first h) (TheLetters.last h P)) r.R ∧
        Socket.yes₃ h (TheLetters.first h) (TheLetters.reads h) (TheLetters.shared h O)
          (lastParts h (TheLetters.first h) (TheLetters.last h P)) r.R [] :=
  fun r => AtFullSide.LaterThreads.sockets_three_at_the_letters h made P r.R
    (lastDebts_at_a_tied_run h hr P made wholeRun line r)

end AtFullSide.Honest

#print axioms AtFullSide.Honest.indexInRange_at_a_tied_run
#print axioms AtFullSide.Honest.tied_at_every_tied_run
#print axioms AtFullSide.Honest.lastDebts_at_a_tied_run
#print axioms AtFullSide.Honest.lastSockets_of_the_closed_facts
