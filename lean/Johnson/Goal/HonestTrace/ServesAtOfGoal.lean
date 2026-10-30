-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/HonestTrace/ServesAtOfGoal.lean

When the weights that an index holds serve a request, at the public part that "publicOf" returns at
public files in the goals' scope: "ServesAt X i x" (Johnson/HonestTrace/Full.lean), said in the
terms in which the library's goal on completeness states its claim. Theorems alone; no
definition. This file states no goal, and no part of one: each theorem is a few calls of theorems of
the library.

Main theorems, under B : "PublicInScope F pp lay X"
(Johnson/Goal/HonestTrace/TraceHingeInScope.lean):
* "servesAt_iff_value_meets": at a request built of a prompt, an output and any padding: "ServesAt"
  holds exactly if the model has a value on the request's window of 1,024 tokens and the output
  meets the files' policy. It names no "CanServe".
* "servesAt_of_canServe", "servesAt_of_modelOutput": from the claim of "VerifierAndGoals.G3'pol"
  (Ladder.lean) and where prompt and output can be served and the output is the model's own, at the
  weights that an index holds: the request built without
  padding exists, the programs' reader takes it, and it is served. "servesAt_of_canServe_weights",
  "servesAt_of_modelOutput_weights": the same at weights of the goals' type, at the index of their
  own digits.
* "servesAt_iff_canServe_meets": at a request built without padding, both ways.
  "served_request_iff_canServe_meets": the same at weights of the goals' type and at every prompt
  and output, built or not.
* "servesAt_iff_result_meets", "servesAt_of_result", "servesAt_iff_result_exact": the same in the
  words of "requestResult" (VerifiableInference/RequestResult.lean).
* "window_at_empty_padding": at the empty padding the built request's window is the zero-filled
  window of "CanServe".

Nearest kin. "Meaning.true_of_served" (Johnson/Goal/Meaning/ServedMeans.lean): where prompt and
output can be served and the output is the model's own, at weights of the goals' type, to
"Policy.IsTrueUnder":
"servesAt_of_modelOutput_weights" is that theorem with two calls behind it; it has no form for an
output that meets the policy. "serves_of_canServe", "serves_of_modelOutput"
(Johnson/Goal/HonestTrace/ServesOfCanServe.lean) end in "Serves" at a table of scales; here the
table and the policy are those of the public part X. With "windowOf" unfolded, the equation of
"window_at_empty_padding" is also a step of the private theorem "result_iff_holds"
(IntegerModel/Arrays/RequestResultLaws.lean); that step is not a theorem of its own.

Limits. The reference sizes alone. Every theorem but "window_at_empty_padding" stands under
"PublicInScope": public files in the goals' scope at which "publicOf" returns; no theorem of this
file shows such files. Under a policy that admits more than exact match a request on whose window
the model has a value is served as soon as its output meets the policy, be the output the model's
result or not: "servesAt_iff_result_exact" holds at the policy of exact match alone. "The output is
the model's own" stands in this file for "VerifierAndGoals.ModelOutput". That this agrees with
"IsModelOutput" at the goals' system is the field "package" of "MeaningAt"
(Johnson/Goal/Meaning/NextToken.lean), which is not called here.
The theorems from a goal's claim speak of the request built without padding;
"servesAt_iff_value_meets" alone speaks at every padding. Whether a request is served depends on the
weights, and a client sees it; which condition fails is told by no program.

Not claimed: the goal, or any part of it; that a prover exists; that a verifier accepts.
-/
import Johnson.Goal.HonestTrace.ServesOfCanServe
import Johnson.Goal.HonestTrace.TraceHingeInScope
import Johnson.Goal.Scope.ScopeLines
import Johnson.Goal.Meaning.ServedMeans
import Johnson.Flat.BuiltOK
import Ladder.RequestResultTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open VerifiableInference

variable {F : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **Both sides; no "CanServe".** Under "PublicInScope", at every index and every request that is
built of a prompt, an output and a padding: the weights that the index holds serve the request
exactly if the model has a value on the request's window of 1,024 tokens and the output meets the
policy that the files state. "valid" is met by "VerifierAndGoals.valid_of_read B.reads" (Ladder/Ties.lean). By
"servesAt_iff_in_scope" (Johnson/Goal/HonestTrace/FullInScope.lean) and "isTrueUnder_iff"
(Johnson/Goal/Meaning/NextToken.lean). -/
theorem servesAt_iff_value_meets (B : PublicInScope F pp lay X)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true) (i : Cm.Idx)
    {x : Instance ppref} {prompt output padding : List Token}
    (built : requestOfTokens (prompt, output) padding = some x) :
    ServesAt X i x ↔
      (modelNextToken (VerifierAndGoals.settingsOfRead pp) (weightsOfIndex valid i)
          (VerifiableInference.Meaning.windowOf x)).isSome = true ∧
        Policy.MeetsPolicy (VerifierAndGoals.settingsOfRead pp) pp.pol (weightsOfIndex valid i) prompt
          output := by
  exact (servesAt_iff_in_scope B.scope B.reads B.pub i x).trans
    (VerifiableInference.Meaning.isTrueUnder_iff valid (OnBytes.Road.L5.lawful_of_read B.reads) rfl
      pp.pol i built)

/-- **From the claim of "VerifierAndGoals.G3'pol"**, at the weights that an index holds: where prompt and
output can be served and the output meets the files' policy, the request built without padding
exists, the programs' reader takes it ("WellFormed", Johnson/Flat/LedgerClaim.lean), and these
weights serve it at X. By "serves_of_canServe", "servesAt_of_true" and "wellFormed_of_built"
(Johnson/Flat/BuiltOK.lean). -/
theorem servesAt_of_canServe (B : PublicInScope F pp lay X)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true) (i : Cm.Idx)
    {prompt output : List Token}
    (can : CanServe (VerifierAndGoals.settingsOfRead pp) (weightsOfIndex valid i) prompt output)
    (meets : Policy.MeetsPolicy (VerifierAndGoals.settingsOfRead pp) pp.pol (weightsOfIndex valid i) prompt
      output) :
    ∃ x, requestOfTokens (prompt, output) [] = some x ∧
      VerifiableInference.OnPublicFiles.Flat.WellFormed x ∧ ServesAt X i x := by
  obtain ⟨x, built, S⟩ :=
    serves_of_canServe valid (OnBytes.Road.L5.lawful_of_read B.reads) rfl pp.pol i can meets
  exact ⟨x, built, VerifiableInference.OnPublicFiles.Flat.wellFormed_of_built built,
    servesAt_of_true B ((serves_iff_isTrueUnder (Cm.Scales.of pp) pp.pol i x).1 S)⟩

/-- **Where the output is the model's own**: the same where prompt and output can be served and the
output is the model's own. The two bounds 2^8 ≤ theta and 2^8 ≤ C are paid as
"Meaning.true_of_served" pays them: the scope's floor on theta ("inScope_at",
Johnson/Goal/Scope/ScopeLines.lean) and the reader's test theta ≤ C. -/
theorem servesAt_of_modelOutput (B : PublicInScope F pp lay X)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true) (i : Cm.Idx)
    {prompt output : List Token}
    (can : CanServe (VerifierAndGoals.settingsOfRead pp) (weightsOfIndex valid i) prompt output)
    (own : VerifierAndGoals.ModelOutput (VerifierAndGoals.settingsOfRead pp) (weightsOfIndex valid i) prompt output) :
    ∃ x, requestOfTokens (prompt, output) [] = some x ∧
      VerifiableInference.OnPublicFiles.Flat.WellFormed x ∧ ServesAt X i x := by
  have floor : 2 ^ 8 ≤ pp.pol.theta := (Johnson.G.ScopeLines.inScope_at B.scope B.reads).2.2
  have clip : 2 ^ 8 ≤ pp.pol.C :=
    le_trans floor (OnBytes.Flat.settingsAtRef_lawful B.reads).pol.2.1
  exact servesAt_of_canServe B valid i can
    (Policy.meetsPolicy_of_isModelOutput floor clip can.2.1 own)

/-- "servesAt_of_canServe" at weights of the goals' type, at the index of their own digits: the
letters of the claim under "CompleteFor" in "VerifierAndGoals.G3'pol". By "weightsOfIndex_indexOfWeights"
(IntegerModel/Arrays/OfIndex.lean). -/
theorem servesAt_of_canServe_weights (B : PublicInScope F pp lay X)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true)
    (w : ModelWeights (VerifierAndGoals.settingsOfRead pp)) {prompt output : List Token}
    (can : CanServe (VerifierAndGoals.settingsOfRead pp) w prompt output)
    (meets : Policy.MeetsPolicy (VerifierAndGoals.settingsOfRead pp) pp.pol w prompt output) :
    ∃ x, requestOfTokens (prompt, output) [] = some x ∧
      VerifiableInference.OnPublicFiles.Flat.WellFormed x ∧
      ServesAt X (indexOfWeights valid w) x := by
  have back := weightsOfIndex_indexOfWeights valid w
  exact servesAt_of_canServe B valid (indexOfWeights valid w) (by rw [back]; exact can)
    (by rw [back]; exact meets)

/-- "servesAt_of_modelOutput" at weights of the goals' type. It is "Meaning.true_of_served"
(Johnson/Goal/Meaning/ServedMeans.lean) with "servesAt_of_true" and "wellFormed_of_built" behind it.
-/
theorem servesAt_of_modelOutput_weights (B : PublicInScope F pp lay X)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true)
    (w : ModelWeights (VerifierAndGoals.settingsOfRead pp)) {prompt output : List Token}
    (can : CanServe (VerifierAndGoals.settingsOfRead pp) w prompt output)
    (own : VerifierAndGoals.ModelOutput (VerifierAndGoals.settingsOfRead pp) w prompt output) :
    ∃ x, requestOfTokens (prompt, output) [] = some x ∧
      VerifiableInference.OnPublicFiles.Flat.WellFormed x ∧
      ServesAt X (indexOfWeights valid w) x := by
  obtain ⟨x, built, V⟩ := _root_.Meaning.true_of_served B.scope B.reads w prompt output can own
  exact ⟨x, built, VerifiableInference.OnPublicFiles.Flat.wellFormed_of_built built,
    servesAt_of_true B V⟩

/-- At the empty padding the built request's window is the zero-filled window of "CanServe". -/
theorem window_at_empty_padding {prompt output : List Token} {x : Instance ppref}
    (built : requestOfTokens (prompt, output) [] = some x) :
    IntegerModel.zeroFilledWindow prompt output = VerifiableInference.Meaning.windowOf x := by
  obtain ⟨p, o, pad, hp, ho, hpad, hx⟩ := requestOfTokens_some built
  obtain rfl : [] = pad := Option.some.inj hpad
  obtain rfl : p.map Fin.val = prompt := map_val_of_vocabularyTokens prompt p hp
  obtain rfl : o.map Fin.val = output := map_val_of_vocabularyTokens output o ho
  unfold VerifiableInference.Meaning.windowOf
  rw [IntegerModel.zeroFilledWindow_map, IntegerModel.firstToks_requestOf hx]

/-- At a request built without padding, both ways: served exactly where the claim of "VerifierAndGoals.G3'pol"
holds. The first two clauses of "CanServe" are the fields "inVocabulary" and "outputNonempty" of
"Policy.MeetsPolicy"; the third is the value on the window, by "window_at_empty_padding". -/
theorem servesAt_iff_canServe_meets (B : PublicInScope F pp lay X)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true) (i : Cm.Idx)
    {x : Instance ppref} {prompt output : List Token}
    (built : requestOfTokens (prompt, output) [] = some x) :
    ServesAt X i x ↔
      CanServe (VerifierAndGoals.settingsOfRead pp) (weightsOfIndex valid i) prompt output ∧
        Policy.MeetsPolicy (VerifierAndGoals.settingsOfRead pp) pp.pol (weightsOfIndex valid i) prompt
          output := by
  rw [servesAt_iff_value_meets B valid i built]
  constructor
  · rintro ⟨value, meets⟩
    refine ⟨⟨meets.inVocabulary, meets.outputNonempty, ?_⟩, meets⟩
    rw [window_at_empty_padding built]
    exact value
  · rintro ⟨can, meets⟩
    refine ⟨?_, meets⟩
    rw [← window_at_empty_padding built]
    exact can.2.2

/-- **At every prompt and output, built or not**, at weights of the goals' type: the request built
without padding exists and is served exactly where the claim of "VerifierAndGoals.G3'pol" holds. No built
request is a premise: the left side is a sentence on the weights, the prompt and the output alone,
as a completeness statement for every request wants it. Where no request is built both sides fail.
-/
theorem served_request_iff_canServe_meets (B : PublicInScope F pp lay X)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true)
    (w : ModelWeights (VerifierAndGoals.settingsOfRead pp)) (prompt output : List Token) :
    (∃ x, requestOfTokens (prompt, output) [] = some x ∧ ServesAt X (indexOfWeights valid w) x) ↔
      CanServe (VerifierAndGoals.settingsOfRead pp) w prompt output ∧
        Policy.MeetsPolicy (VerifierAndGoals.settingsOfRead pp) pp.pol w prompt output := by
  constructor
  · rintro ⟨x, built, hs⟩
    have h := (servesAt_iff_canServe_meets B valid (indexOfWeights valid w) built).1 hs
    rw [weightsOfIndex_indexOfWeights valid w] at h
    exact h
  · rintro ⟨can, meets⟩
    obtain ⟨x, built, -, hs⟩ := servesAt_of_canServe_weights B valid w can meets
    exact ⟨x, built, hs⟩

/-! ## In the words of "requestResult" -/

/-- At a request built without padding: served exactly if the model's result on the request is not
failure and the output meets the files' policy. By "VerifierAndGoals.canServe_and_meetsPolicy_iff"
(Ladder/RequestResultTies.lean). -/
theorem servesAt_iff_result_meets (B : PublicInScope F pp lay X)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true) (i : Cm.Idx)
    {x : Instance ppref} {prompt output : List Token}
    (built : requestOfTokens (prompt, output) [] = some x) :
    ServesAt X i x ↔
      (requestResult (VerifierAndGoals.settingsOfRead pp) (weightsOfIndex valid i) prompt output).isSome
          = true ∧
        Policy.MeetsPolicy (VerifierAndGoals.settingsOfRead pp) pp.pol (weightsOfIndex valid i) prompt
          output := by
  exact (servesAt_iff_canServe_meets B valid i built).trans
    (VerifierAndGoals.canServe_and_meetsPolicy_iff (VerifierAndGoals.settingsOfRead pp) pp.pol (weightsOfIndex valid i)
      prompt output)

/-- Where prompt and output make a request whose result is these output tokens, the request built
without padding exists, the programs' reader takes it, and it is served: under every policy that
files in scope state. By "canServe_and_modelOutput_iff"
(IntegerModel/Arrays/RequestResultLaws.lean).
-/
theorem servesAt_of_result (B : PublicInScope F pp lay X)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true)
    (w : ModelWeights (VerifierAndGoals.settingsOfRead pp)) {prompt output : List Token}
    (form : RequestForm (VerifierAndGoals.settingsOfRead pp) prompt output)
    (result : requestResult (VerifierAndGoals.settingsOfRead pp) w prompt output = some output) :
    ∃ x, requestOfTokens (prompt, output) [] = some x ∧
      VerifiableInference.OnPublicFiles.Flat.WellFormed x ∧
      ServesAt X (indexOfWeights valid w) x := by
  obtain ⟨can, own⟩ := (canServe_and_modelOutput_iff valid w prompt output).2 ⟨form, result⟩
  exact servesAt_of_modelOutput_weights B valid w can own

/-- **At the policy of exact match alone**: at a request built without padding: served exactly if
the model's result on the request is these output tokens. "RequestForm" holds at every built request
("requestForm_iff_requestOfTokens", IntegerModel/Arrays/RequestResultLaws.lean), so it does not
stand on the right. -/
theorem servesAt_iff_result_exact (B : PublicInScope F pp lay X)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true) (exactMatch : pp.pol = AcceptancePolicy.exact)
    (i : Cm.Idx) {x : Instance ppref} {prompt output : List Token}
    (built : requestOfTokens (prompt, output) [] = some x) :
    ServesAt X i x ↔
      requestResult (VerifierAndGoals.settingsOfRead pp) (weightsOfIndex valid i) prompt output
        = some output := by
  rw [servesAt_iff_canServe_meets B valid i built, exactMatch,
    VerifierAndGoals.canServe_and_meetsPolicy_exact_iff valid (weightsOfIndex valid i) prompt output]
  constructor
  · exact fun h => h.2
  · exact fun h =>
      ⟨(requestForm_iff_requestOfTokens valid prompt output).2 (by rw [built]; rfl), h⟩

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.servesAt_iff_value_meets
#print axioms OnBytes.HonestTrace.servesAt_of_canServe
#print axioms OnBytes.HonestTrace.servesAt_of_modelOutput
#print axioms OnBytes.HonestTrace.servesAt_of_canServe_weights
#print axioms OnBytes.HonestTrace.servesAt_of_modelOutput_weights
#print axioms OnBytes.HonestTrace.window_at_empty_padding
#print axioms OnBytes.HonestTrace.servesAt_iff_canServe_meets
#print axioms OnBytes.HonestTrace.served_request_iff_canServe_meets
#print axioms OnBytes.HonestTrace.servesAt_iff_result_meets
#print axioms OnBytes.HonestTrace.servesAt_of_result
#print axioms OnBytes.HonestTrace.servesAt_iff_result_exact
