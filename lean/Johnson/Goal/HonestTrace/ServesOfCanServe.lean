-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/HonestTrace/ServesOfCanServe.lean

From the domains that two statements on completeness name to "Serves"
(Johnson/HonestTrace/Serves.lean).

This file states no goal. It holds two theorems on the domains of two statements on completeness,
both on prompts and outputs that can be served ("CanServe", VerifiableInference/CanServe.lean): the
final line "completeOnCanServe" (AtFullSide/Face/TheSixLines.lean), at every public setup whose
files are in use, where the output is the model's own; and the goal "VerifierAndGoals.G3'pol"
(Ladder.lean), at two named sets of public files, where the output meets the policy
("Policy.MeetsPolicy"). An honest prover needs a trace there, and "Serves" says where "traceOf" has
one. Here, at a lawful table of scales whose settings are valid and at the weights that an index
holds: where prompt and output can be served and the output meets the policy, the request built from
them without padding exists, and these weights serve it; the same where the output is the model's
own, if the policy has 2^8 ≤ θ and 2^8 ≤ C.

Main theorems:
* "serves_of_canServe": from "CanServe" and "Policy.MeetsPolicy". It is "isTrueUnder_of_served"
  (Johnson/Goal/Meaning/NextToken.lean), said of "Serves".
* "serves_of_modelOutput": from "CanServe" and "VerifierAndGoals.ModelOutput", under a policy with 2^8 ≤ θ and
  2^8 ≤ C.

Limits. The reference sizes alone. Both theorems ask a lawful table of scales whose settings are the
given valid settings. That the goals' reader of the public files returns such a table is not shown
here; it is "OnBytes.Flat.settingsAtRef_lawful" (Johnson/Flat/SettingsRead.lean) with "Cm.lawful_of"
(Cm/Rel2Guards.lean): the table "Cm.Scales.of pp" is lawful; that its settings are valid is
"VerifierAndGoals.valid_of_read" (Ladder/Ties.lean). Of the two bounds on the policy the goals' "InScope" asks
2^8 ≤ θ (Ladder.lean); that the reader returns a policy with 2^8 ≤ C is not shown here. The bound on
θ cannot be dropped, by an argument and no theorem: under θ < 2^8 ≤ C no request with a counted
position is served ("not_serves_of_low_theta", Johnson/HonestTrace/ServesAtRef.lean), and some
prompt with the model's own output can be served and has one ("canServe_exists",
VerifiableInference/ModelGuards.lean: prompt and output one token 0, at the all-zero weights).
That some prompt and output can be served is that theorem's, and is not shown here. A prompt with
the model's own output that meets "CanServe" is exhibited there at the all-zero weights, at all
valid settings, and in VerifiableInference/ModelGuardsAtReference.lean
("canServe_atAttentionWeights") at the reference settings and synthetic weights whose attention
block of layer 0 computes and whose layers 1 to 47 are zero; this file exhibits none.
"completeOnCanServe" speaks of "IsModelOutput" of the compiled system, and of all weights of its
type. That the first is "VerifierAndGoals.ModelOutput" is not shown here: the field "package" of
"MeaningAt" (Johnson/Goal/Meaning/NextToken.lean) says it of the goals' system. That all weights of
the goals' type are the weights under the matrix of an index is that structure's field
"everyWeights".

Not claimed: the goal, the final line, or any part of either; that a prover exists; that a verifier
accepts.

-/
import Policy.Front.MeetsPolicyGuards
import Johnson.Goal.Meaning.NextToken
import Johnson.HonestTrace.Serves

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open VerifiableInference VerifiableInference.Meaning

variable {settings : IntegerTransformer.Settings} (valid : settingsAreValid settings = true)
  {scales : Cm.Scales} (lawful : scales.Lawful) (tie : settingsOf scales = settings)
include lawful tie

/-- From "can be served, and meets the policy". At valid settings that are those of a lawful table
of scales, for every policy and index: if prompt and output can be served at the weights that the
index holds ("CanServe": all tokens are in the vocabulary, the output is not empty, the model has a
value on the zero-filled window) and the output meets the policy ("Policy.MeetsPolicy"), then the
request built from them without padding exists, and these weights serve it. -/
theorem serves_of_canServe (policy : AcceptancePolicy) (i : Cm.Idx) {prompt output : List Token}
    (canServe : CanServe settings (weightsOfIndex valid i) prompt output)
    (meets : Policy.MeetsPolicy settings policy (weightsOfIndex valid i) prompt output) :
    ∃ x, requestOfTokens (prompt, output) [] = some x ∧
      Serves ppref scales.kap scales.nf (fun _ => tbRef) policy i.index.val x :=
  isTrueUnder_of_served valid lawful tie policy i canServe meets

/-- From "can be served, and is the model's own output". At valid settings that are those of a
lawful table of scales, under a policy with 2^8 ≤ θ and 2^8 ≤ C, for every index: if prompt and
output can be served at the weights that the index holds ("CanServe") and each output token is the
model's next token after the prompt and the output tokens before it ("VerifierAndGoals.ModelOutput"), then the
request built from them without padding exists, and these weights serve it. -/
theorem serves_of_modelOutput {policy : AcceptancePolicy} (mean : 2 ^ 8 ≤ policy.theta)
    (clip : 2 ^ 8 ≤ policy.C) (i : Cm.Idx) {prompt output : List Token}
    (canServe : CanServe settings (weightsOfIndex valid i) prompt output)
    (isOutput : VerifierAndGoals.ModelOutput settings (weightsOfIndex valid i) prompt output) :
    ∃ x, requestOfTokens (prompt, output) [] = some x ∧
      Serves ppref scales.kap scales.nf (fun _ => tbRef) policy i.index.val x :=
  serves_of_canServe valid lawful tie policy i canServe
    (Policy.meetsPolicy_of_isModelOutput mean clip canServe.2.1 isOutput)

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.serves_of_canServe
#print axioms OnBytes.HonestTrace.serves_of_modelOutput
