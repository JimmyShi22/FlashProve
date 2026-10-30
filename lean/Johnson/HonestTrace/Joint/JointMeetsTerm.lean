-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/JointMeetsTerm.lean

Nothing on hiding. No property of the protocol is claimed.

THE END, AT THE TERM AND AT THE ONE SET OF THE STATEMENTS: at public files in scope that are read and pass protocolDataWellFormed, at
every return of the term's own maker "onlineMaker files" (the value E2E/TheHonestProver.lean, its
propositions E2E/TheHonestProverStatements.lean):
    TraceWhereServed (ServedRequest committerCoinCountLessOne files read) returned.
The executable model's trace is not used. By "traceWhereServed_at_the_term" (JointMeets.lean) and "servedRequest_below"
(JointMeetsBServed.lean: servedRequest_isTrue with below_yesAt).

NOT EMPTY ON THE SIDE OF THE REQUESTS: "served_request_has_a_trace_somewhere": in scope some request IS served, and at it
the returned prover's range test says yes and its trace is there, at every record. The weights of that member are made up
(Meaning.served_met).
A BINDER HERE: "made". That the maker returns is MakerReturns: held in the side library
("ProofFile.Honest.Term.makerReturns", AtFullSide/Honest/HonestProverLaws.lean, over maker_returns),
which this file cannot import. Where the maker does not return, both theorems hold emptily; that it
returns is typed in the side library alone.
NOT SAID: that "ready" returns; that the honest prover serves a request; anything on the trace's cells, on a message or on
acceptance.
-/
import Johnson.HonestTrace.Joint.JointMeets
import Johnson.HonestTrace.Joint.JointMeetsBServed
import E2E.TheHonestProverStatements

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.Meets

open ProofFile.Honest.Term (onlineMaker OnlineReturn)
open AtPublicFiles.AtFiles (FullSizeMatrix ServedRequest)
open AtPublicFiles.AtFiles.HonestTerm (TraceWhereServed)
open FlashProve (committerCoinCountLessOne)

variable {files : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}

/-- **A served request has a trace: the term's proposition at the served requests, at every return
of the term's maker.** -/
theorem traceWhereServed_at_servedRequest
    (scope : VerifierAndGoals.InScope files = true) (read : VerifierAndGoals.readFiles files = .ok pp)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {returned : OnlineReturn files} (made : onlineMaker files = .ok returned) :
    TraceWhereServed (ServedRequest committerCoinCountLessOne files read) returned :=
  traceWhereServed_at_the_term scope live
    (OnBytes.HonestTrace.JointMeets.servedRequest_below scope read) returned made

/-- **It speaks of something**: some request is served, and there the range test says yes and the trace is there. -/
theorem served_request_has_a_trace_somewhere
    (scope : VerifierAndGoals.InScope files = true) (read : VerifierAndGoals.readFiles files = .ok pp)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {returned : OnlineReturn files} (made : onlineMaker files = .ok returned) :
    ∃ (M : FullSizeMatrix) (x : LPFD.Full.XF), ServedRequest committerCoinCountLessOne files read M x ∧
      ∀ rec : OnBytes.Flat.RecFull, returned.H.inRange M = true ∧
        (returned.H.trace M (LPFD.Full.instanceAsPlainRecord (x, rec))).isSome = true := by
  obtain ⟨M, x, h, -⟩ := OnBytes.HonestTrace.JointMeets.servedRequest_member scope read
  exact ⟨M, x, h, fun rec => traceWhereServed_at_servedRequest scope read live made M x rec h⟩

end HonestTraceRun.Meets

#check @HonestTraceRun.Meets.traceWhereServed_at_servedRequest
#print axioms HonestTraceRun.Meets.traceWhereServed_at_servedRequest
#print axioms HonestTraceRun.Meets.served_request_has_a_trace_somewhere
