-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/JointMeets.lean

Nothing on hiding. No property of the protocol is claimed.

WHO SPENDS THE TRACE AT THE TERM, AND WHAT IT COSTS.
The honest provers' term (the value E2E/TheHonestProver.lean; its propositions
E2E/TheHonestProverStatements.lean; both imported here) names one proposition
on the trace: "TraceWhereServed Served returned := ServesAt files returned.H Served". It is the type of the field
"serves" of "AtPublicFiles.AtFiles.HonDebts" (E2E/RoadHonDebts.lean). This file proves it AT THE TERM's OWN FILLING "onlineFilling files",
at every return of "onlineMaker files". The term's trace is the specification's ("fullIn", "theTrace"), read through the index
that the matrix holds; the executable model's trace ("twinTrace") is not used and not imported.
The end at "ServedRequest": JointMeetsTerm.lean.

WHAT IS PREMISED, AND WHAT COULD MAKE IT EMPTY.
* scope, live: on the three public files.
* "made": onlineMaker files = .ok returned: it is the binder of the term's own proposition. If the maker never returned the
  theorem would be empty: that it returns under scope and live is the term's MakerReturns, which is held in the
  side library ("ProofFile.Honest.Term.makerReturns", AtFullSide/Honest/HonestProverLaws.lean, over AtFullSide.K12.maker_returns), which
  this file cannot import.
* "below": Served ≤ RyesZ files. At a free letter Served the proposition is false.
* If RyesZ files had no member the end would say nothing on traces: see servedRequest_met in JointMeetsTerm.lean.
* The end says that a trace IS THERE and that the range test says yes. It says nothing on WHICH cells the trace holds:
  that is "laws_of_readyInput" (Johnson/HonestTrace/ReadyAtFullIn.lean), carried to the matrices in JointMeetsD*.lean.
* No "LaidAt" is premised: it is had from live (AtPublicFiles.Committed.laid_of_live, E2E/TiedAtFiles.lean:608).
-/
import Johnson.HonestTrace.Joint.JointMeetsPlug
import E2E.RoadHonDebts
import E2E.TheHonestProver
import E2E.TheHonestProverStatements

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.Meets

open ProofFile.Honest.Term (matrixInput onlineFilling onlineMaker OnlineReturn)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles ServesAt)
open AtPublicFiles.AtFiles.HonestTerm (TraceWhereServed)
open AtPublicFiles.Committed (RyesZ)

/-- **The term's filling keeps the input's trace and range.** -/
theorem onlineFilling_fields (files : VerifierAndGoals.PublicFiles) :
    (onlineFilling files).trace = matrixInput.trace ∧
      (onlineFilling files).inRange = matrixInput.inRange :=
  ⟨rfl, rfl⟩

variable {files : VerifierAndGoals.PublicFiles}

/-- **A served request has a trace, at the term.** The term's own proposition, at every return of the term's own maker and every
relation below the object's. -/
theorem traceWhereServed_at_the_term
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {Served : FullSizeMatrix → LPFD.Full.XF → Prop} (below : ∀ M x, Served M x → RyesZ files M x)
    (returned : OnlineReturn files) (made : onlineMaker files = .ok returned) :
    TraceWhereServed Served returned := by
  obtain ⟨Zp, Np, cF, L⟩ := AtPublicFiles.Committed.laid_of_live files live
  exact servesAt_at_plug scope live L (onlineFilling_fields files).1 (onlineFilling_fields files).2
    made below

/-- **The same under the name of the debt**: the type of the field "serves" of "HonDebts", at H := returned.H. -/
theorem serves_debt_at_the_term
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {Yes : FullSizeMatrix → LPFD.Full.XF → Prop} (below : ∀ M x, Yes M x → RyesZ files M x)
    (returned : OnlineReturn files) (made : onlineMaker files = .ok returned) :
    AtPublicFiles.AtFiles.ServesAt files returned.H Yes :=
  traceWhereServed_at_the_term scope live below returned made

end HonestTraceRun.Meets

#check @AtPublicFiles.AtFiles.HonDebts.serves
#check @HonestTraceRun.Meets.traceWhereServed_at_the_term
#print axioms HonestTraceRun.Meets.onlineFilling_fields
#print axioms HonestTraceRun.Meets.traceWhereServed_at_the_term
#print axioms HonestTraceRun.Meets.serves_debt_at_the_term
