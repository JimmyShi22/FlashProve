-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/NeverBuilt.lean: the instance that stands where a request builds none, and
that no request builds.

 1. A request that is ill formed builds no instance, so the compiled prover runs at a fall-back.
 2. neverBuiltRequest is that fall-back: a well-formed instance with r = 0 and e = 1.
 3. Its window is all zeros but for a token 1 at the last position.
 4. A request with padding [] has r = 0 and e = 1 only with one token of prompt and one of output.
 5. Its window is then zero after position 1, so it is not neverBuiltRequest.
-/
import VerifiableInference.RequestOutcome
import Johnson.Flat.BuiltOK
import IntegerModel.Arrays.RequestResultLaws
import Johnson.PV.DescribeBinds
import Johnson.Goal.Conditions.BindsAtThe

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Compilation
open VerifiableInference.OnPublicFiles Inst.Model

/-- Token 1. -/
def tokenOne : IntegerModel.Token := ⟨1, by decide⟩

/-- The fall-back request, as an instance. -/
def neverBuiltInstance : Instance ppref where
  prompt := fun position =>
    if position.val = 1023 then tokenOne else IntegerModel.tokenZero
  y := IntegerModel.tokenZero
  rF := ⟨0, by decide⟩
  eF := ⟨1, by decide⟩

/-- The fall-back request: it is well formed. -/
def neverBuiltRequest : Flat.Req :=
  ⟨neverBuiltInstance, ⟨Nat.zero_lt_one, fun _ => rfl⟩⟩

/-- **No request builds the fall-back request**, at the padding that the honest side uses. -/
theorem buildReq_ne_neverBuilt (request : List Token × List Token) :
    Flat.buildReq request [] ≠ some neverBuiltRequest := by
  intro built
  obtain ⟨prompt, output, padding, -, -, hPadding, hRequest⟩ :=
    requestOfTokens_some (Flat.buildReq_some built)
  have hEmpty : padding = [] := (Option.some.inj hPadding).symm
  subst hEmpty
  obtain ⟨⟨hPrompt, hOutput, -⟩, hr, he, -⟩ := IntegerModel.requestOf_some hRequest
  have hr' : 0 = prompt.length - 1 := hr
  have he' : 1 = prompt.length - 1 + output.length := he
  have hLength : (prompt ++ output ++ []).length ≤ 1023 := by
    simp only [List.length_append, List.length_nil]
    omega
  unfold IntegerModel.requestOf at hRequest
  split at hRequest
  · have hToken := congrFun (congrArg Instance.prompt (Option.some.inj hRequest))
      ⟨1023, by decide⟩
    have hLeft : (prompt ++ output ++ []).getD 1023 IntegerModel.tokenZero =
        IntegerModel.tokenZero := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hLength]
      rfl
    have hRight : neverBuiltInstance.prompt ⟨1023, by decide⟩ = tokenOne := rfl
    have hValues := congrArg Fin.val (hLeft.symm.trans (hToken.trans hRight))
    exact absurd hValues (by decide)
  · cases hRequest

/-- A description built from a lay builds its instances by `Flat.buildReq`. -/
theorem build_dStarBuilt (lay : FlashProve.DescriptionData) (files : VerifierAndGoals.PublicFiles) (digest : Digest)
    (further : (FlashProve.descriptionOfDataOnBytes lay).More) (request : List Token × List Token)
    (padding : List Token) :
    ((FlashProve.descriptionOfDataOnBytes lay).input files digest further).buildInstance request padding =
      Flat.buildReq request padding :=
  rfl

/-- **At the protocol's description no request builds the fall-back request.** -/
theorem neverBuilt_at_the_protocol (files : VerifierAndGoals.PublicFiles) (request : List Token × List Token) :
    (FlashProve.flashProveDescription.input files FlashProve.allZeroDigest []).buildInstance request [] ≠ some neverBuiltRequest :=
  fun built => buildReq_ne_neverBuilt request
    ((build_dStarBuilt FlashProve.flashProveData files FlashProve.allZeroDigest [] request []).symm.trans built)

/-- **At valid settings every well-formed request builds an instance**, at the padding that the
honest side uses. -/
theorem buildReq_of_requestForm {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) (prompt output : List Token)
    (form : RequestForm settings prompt output) :
    ∃ instance_, Flat.buildReq (prompt, output) [] = some instance_ := by
  obtain ⟨built, hBuilt⟩ :=
    Option.isSome_iff_exists.1 ((requestForm_iff_requestOfTokens valid prompt output).1 form)
  exact ⟨_, Flat.buildReq_of_built hBuilt⟩

/-- The same at the protocol's description. -/
theorem builds_of_requestForm (files : VerifierAndGoals.PublicFiles) {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) (prompt output : List Token)
    (form : RequestForm settings prompt output) :
    ∃ instance_, (FlashProve.flashProveDescription.input files FlashProve.allZeroDigest []).buildInstance (prompt, output) [] =
      some instance_ := by
  obtain ⟨instance_, built⟩ := buildReq_of_requestForm valid prompt output form
  exact ⟨instance_,
    (build_dStarBuilt FlashProve.flashProveData files FlashProve.allZeroDigest [] (prompt, output) []).trans built⟩

/-- **A served instance**: at the index of some weights, a prompt and output tokens make a request,
the model's result on it is these output tokens, and the instance is what the verifier's builder
makes of them. -/
def ServedAt (files : VerifierAndGoals.PublicFiles) (settings : IntegerTransformer.Settings)
    (index : (FlashProve.flashProveDescription.C files).I) (instance_ : (FlashProve.flashProveDescription.C files).X) : Prop :=
  ∃ (weights : ModelWeights settings) (prompt output : List Token),
    index = FlashProve.backThe files settings weights ∧ RequestForm settings prompt output ∧
    requestResult settings weights prompt output = some output ∧
    (FlashProve.flashProveDescription.input files FlashProve.allZeroDigest []).buildInstance (prompt, output) [] = some instance_

/-- No instance that stands as the fall-back request is served, at any index. -/
theorem not_servedAt_neverBuilt (files : VerifierAndGoals.PublicFiles) (settings : IntegerTransformer.Settings)
    (index : (FlashProve.flashProveDescription.C files).I) : ¬ ServedAt files settings index neverBuiltRequest :=
  fun ⟨_, prompt, output, _, _, _, built⟩ => neverBuilt_at_the_protocol files (prompt, output) built

/-- **At valid settings the prover's test on an instance is the statement's rule on its request**:
at the index of the weights, the instance that a request builds is served exactly if that request's
outcome at these weights is served. -/
theorem servedAt_backThe_iff (files : VerifierAndGoals.PublicFiles) {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) (weights : ModelWeights settings)
    (request : List Token × List Token) (instance_ : (FlashProve.flashProveDescription.C files).X)
    (built : (FlashProve.flashProveDescription.input files FlashProve.allZeroDigest []).buildInstance request [] = some instance_) :
    ServedAt files settings (FlashProve.backThe files settings weights) instance_ ↔
      AtEveryRequest.requestOutcome settings weights request = .served := by
  have hBack : ∀ other : ModelWeights settings,
      FlashProve.backThe files settings other = VerifierAndGoals.Fit.backO valid other :=
    fun _ => dif_pos valid
  constructor
  · rintro ⟨other, prompt, output, hIndex, hForm, hResult, hBuilt⟩
    have hSame : VerifierAndGoals.Fit.backO valid weights = VerifierAndGoals.Fit.backO valid other :=
      ((hBack weights).symm.trans hIndex).trans (hBack other)
    have hWeights : weights = other := Option.some.inj
      ((VerifierAndGoals.Fit.section_backO valid weights).symm.trans
        ((congrArg (VerifierAndGoals.Fit.phiO valid) hSame).trans (VerifierAndGoals.Fit.section_backO valid other)))
    have hFirst : Flat.buildReq request [] = some instance_ :=
      (build_dStarBuilt FlashProve.flashProveData files FlashProve.allZeroDigest [] request []).symm.trans built
    have hSecond : Flat.buildReq (prompt, output) [] = some instance_ :=
      (build_dStarBuilt FlashProve.flashProveData files FlashProve.allZeroDigest [] (prompt, output) []).symm.trans
        hBuilt
    have hRequest : request = (prompt, output) :=
      (Flat.buildReq_reads hFirst).symm.trans (Flat.buildReq_reads hSecond)
    subst hWeights
    subst hRequest
    exact (AtEveryRequest.requestOutcome_eq_served_iff settings weights _).2 ⟨hForm, hResult⟩
  · intro served
    obtain ⟨hForm, hResult⟩ :=
      (AtEveryRequest.requestOutcome_eq_served_iff settings weights request).1 served
    exact ⟨weights, request.1, request.2, rfl, hForm, hResult, built⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.buildReq_ne_neverBuilt
#print axioms VerifiableInference.Compilation.build_dStarBuilt
#print axioms VerifiableInference.Compilation.neverBuilt_at_the_protocol
#print axioms VerifiableInference.Compilation.not_servedAt_neverBuilt
#print axioms VerifiableInference.Compilation.servedAt_backThe_iff
#print axioms VerifiableInference.Compilation.builds_of_requestForm
