-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/TwoIndicesServeOneRequest.lean

It states no goal. No property of the protocol is claimed.

TWO DIFFERENT INDICES THAT SERVE ONE REQUEST, for public files in scope.

The pair. Both sets of weights are the library's made-up voting weights "Cm.biteW σ τ"
(Cm/TargetPartBite2K.lean): all 48 layers are zero, token t is embedded in the channel σ t, and the
channel j votes for the token τ j. Here σ = "Cm.biteS" (token 1 in channel 1, every other token in
channel 0) at both.
* "answersZeroWeights": τ = 0 everywhere: after any one token the model answers 0.
* "repeatsOneWeights": τ = "Cm.biteT" (channel 1 votes for token 1, every other channel for token 0):
  after the one token 1 the model answers 1, after any other one token it answers 0.
The request: the prompt [0], the output [0]. Both models give it. On the prompt [1] they differ.

Main theorems:
* "votingIndex_serves": at every lawful table of scales: after the prompt [a] the voting weights' own
  output is [τ (σ a)], and it can be served.
* "twoModels_serve_and_differ": at all valid settings: both sets of weights can serve ([0], [0]), it is
  the own output of both, and their next tokens after [1] are 0 and 1.
* "twoWeightsServeOneRequest": in scope, at any number b: the indices of the two sets of weights differ
  and one instance is a served request ("AtPublicFiles.AtFiles.ServedRequest") at both.
* "twoIndicesServeOneRequest": the same with the range, in the words that
  "TwoIndicesServeOneRequest" asks, written out.
* "twoIndicesInTheRelation": the same pair and instance in the object's relation
  ("AtPublicFiles.Committed.RyesZ").

Limits.
* Both sets of weights are made up, and all their layers are zero: nothing passes through attention or a
  feed-forward block. Nothing is said of a trained model's weights.
* The shared request has one prompt token and one output token.
* It says that there are two such indices. How many there are, and how alike the two models are
  elsewhere, is not said beyond the prompt [1].
* That some public files are in scope is not said here.
* No prover, verifier or view is named: nothing on hiding, completeness or soundness follows from this
  file alone.
-/
import E2E.CompleteAsIOPServedLaws
import Johnson.FrontRoad.FromDebts
import Johnson.FrontRoad.LaidBeside
import Johnson.FrontRoad.RangeOf
import Johnson.Goal.Skeleton.SoundOfVerifyGoals
import Cm.TargetPartBite2K
import IntegerModel.ModelOutput
import IntegerModel.Arrays.SameModel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.TwoIndicesServe

open VerifiableInference
open VerifiableInference.OnPublicFiles (Flat.InRange)
open AtPublicFiles.AtFiles (FullSizeMatrix ServedRequest)
open AtPublicFiles.Committed (RyesZ)
open VerifierAndGoals (PublicFiles InScope readFiles settingsOfRead valid_of_read ModelOutput)
open FlashProve (homeR committerCoinCountLessOne backB build_home_of_built)

/-! ## 1. The voting weights at every lawful table -/

/-- **The voting weights serve their own answer**, at every lawful table of scales: for σ into the 5,120
channels, τ into the vocabulary and a token a of the vocabulary, after the prompt [a] the model's output
is [τ (σ a)], and the prompt with this output can be served. By "Cm.target_bite2_pos". -/
theorem votingIndex_serves (s : Cm.Scales) (hs : s.Lawful) (σ τ : ℕ → ℕ)
    (hσ : ∀ t, σ t < 5120) (hτ : ∀ j, τ j < 202048) (a : ℕ) (ha : a < 202048) :
    IntegerModel.CanServeModelOutput s (Cm.biteI σ τ).index [a] [τ (σ a)] := by
  obtain ⟨x, hx⟩ : ∃ x, IntegerModel.requestOf [(⟨a, ha⟩ : IntegerModel.Token)]
      [(⟨τ (σ a), hτ _⟩ : IntegerModel.Token)] [] = some x := by
    unfold IntegerModel.requestOf
    rw [dif_pos ⟨Nat.succ_pos 0, Nat.succ_pos 0,
      (by decide : (1 : ℕ) + 1 ≤ Inst.Model.ppref.T + 1)⟩]
    exact ⟨_, rfl⟩
  obtain ⟨-, hr, he, ht⟩ := IntegerModel.requestOf_some hx
  have hr0 : x.r = 0 := hr
  have he1 : x.e = 1 := he
  have t0 : x.tok 0 = a := ht 0 (Nat.succ_pos 1)
  have t1 : x.tok 1 = τ (σ a) := ht 1 (Nat.lt_succ_self 1)
  have checked : ∀ t (h : t < Inst.Model.ppref.T), x.r ≤ t → t < x.e →
      x.w t = τ (σ (x.prompt ⟨t, h⟩)) := by
    intro t h _ h2
    obtain rfl : t = 0 := by omega
    have p0 : (x.prompt ⟨0, h⟩).val = a := by
      rw [← t0]
      unfold Inst.Model.Instance.tok
      rw [dif_pos h]
    show x.tok 1 = τ (σ (x.prompt ⟨0, h⟩).val)
    rw [p0, t1]
  have holds : Cm.PaperTrue s.kap s.nf (Cm.biteI σ τ) x :=
    (Cm.target_bite2_pos s hs σ τ hσ hτ x).2
      ⟨IntegerModel.form_of_requestWellFormed (IntegerModel.requestWellFormed_requestOf hx),
        checked⟩
  have built : requestOfTokens ([a], [τ (σ a)]) [] = some x :=
    (requestOfTokens_eq (vocabularyTokens_map_val [(⟨a, ha⟩ : IntegerModel.Token)])
      (vocabularyTokens_map_val [(⟨τ (σ a), hτ _⟩ : IntegerModel.Token)]) rfl).trans hx
  exact IntegerModel.canServeModelOutput_of_isTrueRequest s hs (Cm.biteI σ τ) built holds

theorem biteS_lt (t : ℕ) : Cm.biteS t < 5120 := by unfold Cm.biteS; split <;> norm_num

theorem biteT_lt (j : ℕ) : Cm.biteT j < 202048 := by unfold Cm.biteT; split <;> norm_num

/-! ## 2. The two sets of weights at valid settings -/

section Valid
variable {settings : IntegerTransformer.Settings} (valid : settingsAreValid settings = true)

/-- The same at valid settings, in the words of the model on arrays: the output [τ (σ a)] after the
prompt [a] can be served and is the model's. -/
theorem votingWeights_serve (σ τ : ℕ → ℕ) (hσ : ∀ t, σ t < 5120) (hτ : ∀ j, τ j < 202048) (a : ℕ)
    (ha : a < 202048) :
    CanServe settings (weightsOfIndex valid (Cm.biteI σ τ)) [a] [τ (σ a)] ∧
      ModelOutput settings (weightsOfIndex valid (Cm.biteI σ τ)) [a] [τ (σ a)] := by
  have h := votingIndex_serves (scalesOf settings) (lawful_scalesOf valid) σ τ hσ hτ a ha
  refine ⟨(canServe_weightsOfIndex_iff (lawful_scalesOf valid) valid (settingsOf_scalesOf valid) _ _
    _).2 h.1, fun position hp => ?_⟩
  rw [modelNextToken_eq_nextToken (lawful_scalesOf valid) valid (settingsOf_scalesOf valid)]
  exact h.2 position hp

/-- **Made-up weights whose model answers 0 after any one token.** All layers are zero. -/
noncomputable def answersZeroWeights : ModelWeights settings :=
  weightsOfIndex valid (Cm.biteI Cm.biteS fun _ => 0)

/-- **Made-up weights whose model answers 1 after the one token 1, and 0 after any other one token.**
All layers are zero. -/
noncomputable def repeatsOneWeights : ModelWeights settings :=
  weightsOfIndex valid (Cm.biteI Cm.biteS Cm.biteT)

/-- After any one token a of the vocabulary the first model's output [0] can be served and is its own. -/
theorem answersZero_serves (a : ℕ) (ha : a < 202048) :
    CanServe settings (answersZeroWeights valid) [a] [0] ∧
      ModelOutput settings (answersZeroWeights valid) [a] [0] :=
  votingWeights_serve valid Cm.biteS (fun _ => 0) biteS_lt (fun _ => by norm_num) a ha

/-- After the one token 0 the second model's output [0] can be served and is its own. -/
theorem repeatsOne_serves_zero :
    CanServe settings (repeatsOneWeights valid) [0] [0] ∧
      ModelOutput settings (repeatsOneWeights valid) [0] [0] :=
  votingWeights_serve valid Cm.biteS Cm.biteT biteS_lt biteT_lt 0 (by norm_num)

/-- After the one token 1 the second model's output [1] can be served and is its own. -/
theorem repeatsOne_serves_one :
    CanServe settings (repeatsOneWeights valid) [1] [1] ∧
      ModelOutput settings (repeatsOneWeights valid) [1] [1] :=
  votingWeights_serve valid Cm.biteS Cm.biteT biteS_lt biteT_lt 1 (by norm_num)

/-- **Two models that give one request alike and another differently**, at all valid settings: the
output [0] after the prompt [0] can be served at both sets of weights and is the own output of both;
after the prompt [1] the first model's next token is 0 and the second's is 1. -/
theorem twoModels_serve_and_differ :
    (CanServe settings (answersZeroWeights valid) [0] [0] ∧
      ModelOutput settings (answersZeroWeights valid) [0] [0]) ∧
    (CanServe settings (repeatsOneWeights valid) [0] [0] ∧
      ModelOutput settings (repeatsOneWeights valid) [0] [0]) ∧
    modelNextToken settings (answersZeroWeights valid) [1] = some 0 ∧
    modelNextToken settings (repeatsOneWeights valid) [1] = some 1 :=
  ⟨answersZero_serves valid 0 (by norm_num), repeatsOne_serves_zero valid,
    (answersZero_serves valid 1 (by norm_num)).2 0 Nat.zero_lt_one,
    (repeatsOne_serves_one valid).2 0 Nat.zero_lt_one⟩

/-- The two sets of weights differ. -/
theorem answersZero_ne_repeatsOne : answersZeroWeights valid ≠ repeatsOneWeights valid := fun e => by
  obtain ⟨-, -, h0, h1⟩ := twoModels_serve_and_differ valid
  rw [e, h1] at h0
  exact absurd (Option.some.inj h0) Nat.one_ne_zero

end Valid

/-! ## 3. In scope: one served request at two indices -/

section Scope
variable (b : PublicFiles → ℕ) (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy}

/-- **In scope, what can be served with the model's own output is a served request**, and the instance
is the same for all weights: it is what the builder makes of the tokens. -/
theorem servedRequest_of_built (hr : readFiles Z = .ok pp)
    (w : ModelWeights (settingsOfRead pp)) (prompt output : List Token)
    (served : CanServe (settingsOfRead pp) w prompt output)
    (own : ModelOutput (settingsOfRead pp) w prompt output) {x : (homeR b Z).Instance}
    (built : (homeR b Z).buildInstance (prompt, output) [] = some x) :
    ServedRequest b Z hr (backB b Z (settingsOfRead pp) w) x := by
  obtain ⟨form, result⟩ :=
    (canServe_and_modelOutput_iff (valid_of_read hr) w prompt output).1 ⟨served, own⟩
  exact ⟨w, prompt, output, rfl, form, result, built⟩

/-- **In scope two sets of weights with different indices serve one request**, at any number b: the
weights "answersZeroWeights" and "repeatsOneWeights", the prompt [0] and the output [0]. The two models
differ: their next tokens after the prompt [1] are 0 and 1. -/
theorem twoWeightsServeOneRequest (scope : InScope Z = true) (hr : readFiles Z = .ok pp) :
    ∃ (w w' : ModelWeights (settingsOfRead pp)) (x : (homeR b Z).Instance),
      backB b Z (settingsOfRead pp) w ≠ backB b Z (settingsOfRead pp) w' ∧
      ServedRequest b Z hr (backB b Z (settingsOfRead pp) w) x ∧
      ServedRequest b Z hr (backB b Z (settingsOfRead pp) w') x ∧
      modelNextToken (settingsOfRead pp) w [1] = some 0 ∧
      modelNextToken (settingsOfRead pp) w' [1] = some 1 := by
  obtain ⟨h, h', n, n'⟩ := twoModels_serve_and_differ (valid_of_read hr)
  obtain ⟨x, hx, -⟩ := Meaning.true_of_served scope hr _ [0] [0] h.1 h.2
  have built := build_home_of_built b Z hx
  exact ⟨_, _, _,
    fun e => answersZero_ne_repeatsOne (valid_of_read hr)
      (OnBytes.FrontRoad.backB_injective b Z pp hr e),
    servedRequest_of_built b Z hr _ [0] [0] h.1 h.2 built,
    servedRequest_of_built b Z hr _ [0] [0] h'.1 h'.2 built, n, n'⟩

end Scope

/-- **Two different indices in range serve one request**, for public files in scope. The proposition is
that of "TwoIndicesServeOneRequest Z hr", written out, with "Flat.InRange"
for its "rangeAtFiles". -/
theorem twoIndicesServeOneRequest (Z : PublicFiles) (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) :
    ∃ (i i' : FullSizeMatrix) (x : LPFD.Full.XF), i ≠ i' ∧ Flat.InRange i ∧ Flat.InRange i' ∧
      ServedRequest committerCoinCountLessOne Z hr i x ∧ ServedRequest committerCoinCountLessOne Z hr i' x := by
  obtain ⟨w, w', x, ne, s, s', -, -⟩ := twoWeightsServeOneRequest committerCoinCountLessOne Z scope hr
  exact ⟨_, _, x, ne, OnBytes.FrontRoad.inRange_backThe Z _ w,
    OnBytes.FrontRoad.inRange_backThe Z _ w', s, s'⟩

/-- **The same pair and instance in the object's relation.** -/
theorem twoIndicesInTheRelation (Z : PublicFiles) (scope : InScope Z = true) :
    ∃ (i i' : FullSizeMatrix) (x : LPFD.Full.XF), i ≠ i' ∧ RyesZ Z i x ∧ RyesZ Z i' x := by
  obtain ⟨pp, hr⟩ := VerifierAndGoals.AtTheName.read_of_scope Z scope
  obtain ⟨i, i', x, ne, -, -, s, s'⟩ := twoIndicesServeOneRequest Z scope hr
  exact ⟨i, i', x, ne,
    OnBytes.FrontRoad.below_yesAt committerCoinCountLessOne Z hr i x
      (AtPublicFiles.AtFiles.servedRequest_isTrue committerCoinCountLessOne Z scope hr s),
    OnBytes.FrontRoad.below_yesAt committerCoinCountLessOne Z hr i' x
      (AtPublicFiles.AtFiles.servedRequest_isTrue committerCoinCountLessOne Z scope hr s')⟩

end OnBytes.HonestTrace.TwoIndicesServe

#print axioms OnBytes.HonestTrace.TwoIndicesServe.votingIndex_serves
#print axioms OnBytes.HonestTrace.TwoIndicesServe.votingWeights_serve
#print axioms OnBytes.HonestTrace.TwoIndicesServe.twoModels_serve_and_differ
#print axioms OnBytes.HonestTrace.TwoIndicesServe.answersZero_ne_repeatsOne
#print axioms OnBytes.HonestTrace.TwoIndicesServe.servedRequest_of_built
#print axioms OnBytes.HonestTrace.TwoIndicesServe.twoWeightsServeOneRequest
#print axioms OnBytes.HonestTrace.TwoIndicesServe.twoIndicesServeOneRequest
#print axioms OnBytes.HonestTrace.TwoIndicesServe.twoIndicesInTheRelation
