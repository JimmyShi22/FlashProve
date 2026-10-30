-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/LastSocketsFilled.lean

This file proves two fields of the structures in TheOneObject.lean of this folder, at exactly the
fields' types: the field owes₃ of TheThreadsHalf and the field yes₃ of TheOneObject. Both hold at
every TiedRun and at every value of the two auxiliary parameters O and P. The file contains no
definition.

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
    Z A collects the library's facts on a return A of it (see the header of CompleteAtTheFiles.lean
    of this folder).

Main statements. The premises of all three are h : HeadAtReturn Z A, readFiles Z = .ok pp (hr), the
return A of the base construction (made), the parameters O and P, and the two instances Inhabited
P5J.TS and Inhabited Desc.K14.St, as in TheOneObject.lean. There is no other premise.
  * lastSockets_at_border358: Socket.owes₃ and Socket.yes₃ together, at every TiedRun. It is
    lastSockets_of_the_closed_facts with its two closed premises supplied: wholeRun by
    runOnShapes_toEnd, and line by lastRunAt_border358.
  * owes₃_whole_filled: the field owes₃.
  * yes₃_whole_filled: the field yes₃. It is stated at the empty list [] of default-branch events.
  * The two examples at the end only check that the types agree with the structures' fields.

Limits.
  * These statements bear the library's label "NOT IN FRONT OF A LAW OVER COINS". What the label
    bars, and what counts as a law over coins, is set out in one place:
    Johnson/Bind/ForProver/FiveFieldsAt.lean, under "A limit on the coins". The reason here: the
    proofs use tied_at_every_tied_run (LastSocketsOfTheClosedFacts.lean of this folder), in which
    TiedAtRun ties a run's key to the run's own index and coins (validAt; see also
    AtFullSide/HonestTrace/TiedAtTheCommittersSample.lean). A bound on the probability that an
    honest proof is rejected is not a law over coins in that sense.
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
  * None of these statements is one of the library's goals. Nothing on soundness, completeness or
    hiding.

Built on.
  * lastSockets_of_the_closed_facts (LastSocketsOfTheClosedFacts.lean of this folder).
  * runOnShapes_toEnd (ShapeLines/FirstChainRuns.lean) and lastRunAt_border358
    (ShapeLines/LastChain/SocketsThreeAt358.lean).
-/
import AtFullSide.Honest.LastSocketsOfTheClosedFacts
import ShapeLines.LastChain.SocketsThreeAt358

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
local instance (priority := high) nonemptyPadZ_lastSockets : Nonempty PadZ :=
  pads_nonempty frS 402653181

local instance (priority := high) nonemptyRunValue_lastSockets : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_lastSockets : Inhabited RunValue :=
  ⟨fun _ => 0⟩

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)
  {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {O : TheLetters.OpenShared A}
  (P : TheLetters.OpenLast h O)

/-- The propositions of the fields owes₃ and yes₃ together, at every TiedRun. -/
theorem lastSockets_at_border358
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) :
    ∀ r : TiedRun h hr,
      Socket.owes₃ h (TheLetters.first h) (TheLetters.reads h) (TheLetters.shared h O)
          (lastParts h (TheLetters.first h) (TheLetters.last h P)) r.R ∧
        Socket.yes₃ h (TheLetters.first h) (TheLetters.reads h) (TheLetters.shared h O)
          (lastParts h (TheLetters.first h) (TheLetters.last h P)) r.R [] :=
  lastSockets_of_the_closed_facts h hr P made ShapeLines.runOnShapes_toEnd
    ShapeLines.lastRunAt_border358

/-- The field owes₃ of TheThreadsHalf. -/
theorem owes₃_whole_filled (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) :
    ∀ r : TiedRun h hr, Socket.owes₃ h (TheLetters.first h) (TheLetters.reads h)
      (TheLetters.shared h O) (lastParts h (TheLetters.first h) (TheLetters.last h P)) r.R :=
  fun r => (lastSockets_at_border358 h hr P made r).1

/-- The field yes₃ of TheOneObject. -/
theorem yes₃_whole_filled (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) :
    ∀ r : TiedRun h hr, Socket.yes₃ h (TheLetters.first h) (TheLetters.reads h)
      (TheLetters.shared h O) (lastParts h (TheLetters.first h) (TheLetters.last h P)) r.R [] :=
  fun r => (lastSockets_at_border358 h hr P made r).2

/-- A check of types alone: owes₃_whole_filled can be put into a value T of TheThreadsHalf, at the
parameters of T. The value T is a hypothesis, and it already has a field owes₃. -/
example (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (T : TheThreadsHalf h hr) : TheThreadsHalf h hr :=
  { T with owes₃ := owes₃_whole_filled h hr T.open₃ made }

/-- The same check for yes₃_whole_filled and TheOneObject. -/
example (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (T : TheOneObject h hr) : TheOneObject h hr :=
  { T with yes₃ := yes₃_whole_filled h hr T.open₃ made }

end AtFullSide.Honest

#print axioms AtFullSide.Honest.lastSockets_at_border358
#print axioms AtFullSide.Honest.owes₃_whole_filled
#print axioms AtFullSide.Honest.yes₃_whole_filled
