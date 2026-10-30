-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/CompleteAsIOPAtTheTerm.lean: completeness as an IOP with our values plugged in.
Nothing here is proved.

The statement is at the offline, link and online parts of VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription at
the public files Z, from which verify is compiled (object_description, E2E/DescriptionTie.lean).
It is a statement about a value P, not about a closed prover. The link's and the online prover take
no argument; the offline prover is a skeleton whose senders are the arguments P. A named P:
`thePartsAt` (E2E/KeyArgumentsAt.lean), with named stand-ins: that file states nothing on whether
one of them is taken in scope. The definition takes P as an argument.
The relation is the served requests: at the index of some weights, the requests on which the
model's result is their output. It is defined from the model alone, it is not empty in scope
(servedRequest_met, from served_met and canServe_atVotingWeights; canServe_exists is the general
witness), and it lies inside the requests true under the files' policy (servedRequest_isTrue).
A request for which the model has no result is in no such relation: the honest reply refuses it
above the IOP, and no proof is made. Whether a request is served depends on the weights, which the
prover holds: the value is these provers under refuseUnserved, the same provers with the private
stop set widened to everything where the request is not served.
The error is 2⁻⁴¹: the target 2⁻⁴⁰ is that of the whole statement at verify, and this is this
statement's share of it.
-/
import E2E.TheHonestProver
import E2E.CompleteAsIOPAtFiles

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (committerCoinCountLessOne protocolDataWellFormed)
open OnBytes.Prover (ofRecs)

/-- **The prover is complete as an IOP.** At public files that are in scope and that the
description's own test accepts. -/
def TheProverIsCompleteAsIOP (Z : PublicFiles) (P : Parts Z) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) : Prop :=
  InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
    CompleteOnServedRequests Z hr
      ((ofRecs (honestProvers Z P)).refuseUnserved (ServedRequest committerCoinCountLessOne Z hr))

end AtPublicFiles.AtFiles.HonestTerm
