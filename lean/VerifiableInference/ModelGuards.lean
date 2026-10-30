-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/ModelGuards.lean

Guards against reading the statements on the model as more, or as less, than they say: the
statements' quantifiers do not range over nothing, and the model function is not constant.

* `notModelOutput_exists`: at all weights some output that is not empty is not the model's, so the
  statements on soundness have claims to refuse.
* `canServe_exists`: at all valid settings some weights, prompt and output meet `CanServe` with the
  output the model's, so the statements on completeness and on zero-knowledge are not empty. It is
  shown for made-up models alone: one at whose weights every logit is 0
  (Inst/Model/ProgramRGuards.lean: `lg_zero`), and those of `canServe_atVotingWeights`, all of whose
  layers are zero; at the settings of the library's reference table of scales also one with a layer
  whose attention block computes (`canServe_atAttentionWeights`,
  VerifiableInference/ModelGuardsAtReference.lean; what computes there, and what is not ruled
  out: "Limits" in that file's head).
* `modelNextToken_answers_one`, `modelNextToken_reads_weights`, `modelNextToken_reads_prompt`: at
  all valid settings the model function is not constant: some weights answer a token other than 0,
  two sets of weights answer one prompt differently, and some weights answer two prompts
  differently. The weights are made up and all their layers are zero: the answer reads the last
  token alone, and nothing passes through attention or a feed-forward block. For a layer whose
  attention block computes and for an earlier token: `modelNextToken_reads_layer`,
  `modelNextToken_reads_earlier_token` (VerifiableInference/ModelGuardsAtReference.lean), at the
  settings of the library's reference table of scales, at made-up weights; the limits: that file's
  head.
* `twoModels_serve_one_request_alike`: at all valid settings there are two different models to hide
  between: they serve one request alike and answer another prompt differently. The weights are made
  up and all their layers are zero.
* `validSettings_exist`, `validSettings_two`: valid settings exist, and there are two different
  ones.
-/
import IntegerModel.Arrays.SameModel
import IntegerModel.ReplyOnWindow
import Cm.Rel2Idle
import Cm.TargetPartBite2K

set_option autoImplicit false

/- No default table of scales here: `Scl.ref` (Inst/Model/Scl.lean) is off; each `Scl` is named. -/
attribute [-instance] Inst.Model.Scl.ref

open scoped ENNReal

namespace VerifiableInference

/-- Valid settings. -/
abbrev ValidSettings : Type :=
  { settings : IntegerTransformer.Settings // settingsAreValid settings = true }

/-- In every argument system, at all weights, some output that is not empty is not the model's:
after the prompt of one token 0, the outputs of one token 0 and of one token 1 cannot both be. -/
theorem notModelOutput_exists (system : ArgumentSystem) (weights : system.Weights) :
    ∃ prompt output : List Token, output ≠ [] ∧ ¬ system.IsModelOutput weights prompt output := by
  by_cases h : system.IsModelOutput weights [0] [0]
  · refine ⟨[0], [1], List.cons_ne_nil _ _, fun h' => ?_⟩
    have a : system.nextToken weights [0] = some 0 := h 0 Nat.zero_lt_one
    have b : system.nextToken weights [0] = some 1 := h' 0 Nat.zero_lt_one
    exact absurd (Option.some.inj (a.symm.trans b)) Nat.zero_ne_one
  · exact ⟨[0], [0], List.cons_ne_nil _ _, h⟩

/-- Valid settings exist. -/
theorem validSettings_exist : Nonempty ValidSettings :=
  let ⟨settings, valid⟩ := exists_valid_settings
  ⟨⟨settings, valid⟩⟩

/-- There are two different valid settings: those of two of the library's lawful tables of scales,
which differ, among others, in the final norm's number of bits. -/
theorem validSettings_two : ∃ first second : ValidSettings, first ≠ second :=
  ⟨⟨settingsOf Cm.sRef, settingsAreValid_settingsOf Cm.lawful_sRef⟩,
    ⟨settingsOf Cm.sIdle, settingsAreValid_settingsOf Cm.lawful_idle⟩,
    fun h => (by decide : (settingsOf Cm.sRef).finalBits ≠ (settingsOf Cm.sIdle).finalBits)
      (congrArg (fun t : ValidSettings => t.1.finalBits) h)⟩

/-- At all valid settings some weights, prompt and output meet `CanServe`, with the output the
model's: the weights of the library's made-up index `ScalesSanity.iZero`, at which every logit is 0,
the prompt of one token 0 and the output of one token 0. -/
theorem canServe_exists (settings : IntegerTransformer.Settings)
    (valid : settingsAreValid settings = true) :
    ∃ (weights : ModelWeights settings) (prompt output : List Token),
      CanServe settings weights prompt output ∧
        ∀ position (h : position < output.length),
          modelNextToken settings weights (prompt ++ output.take position)
            = some output[position] := by
  have h : IntegerModel.CanServeModelOutput (scalesOf settings)
      (Cm.Idx.ofIndex Inst.Model.ScalesSanity.iZero).index [0] [0] := by
    rw [Cm.index_ofIndex]
    exact IntegerModel.canServeModelOutput_atZeroWeights (scalesOf settings) (lawful_scalesOf valid)
  refine ⟨weightsOfIndex valid (Cm.Idx.ofIndex Inst.Model.ScalesSanity.iZero), [0], [0],
    (canServe_weightsOfIndex_iff (lawful_scalesOf valid) valid (settingsOf_scalesOf valid) _ _
      _).2 h.1, fun position hp => ?_⟩
  rw [modelNextToken_eq_nextToken (lawful_scalesOf valid) valid (settingsOf_scalesOf valid)]
  exact h.2 position hp

/-- The library's made-up weights `Cm.biteW σ τ` (Cm/TargetPartBite2K.lean): token t is embedded in
the channel σ t, the channel j votes for the token τ j, and all layers are zero. At every lawful
table, for σ into the 5,120 channels, τ into the vocabulary and a token a of the vocabulary: after
the prompt of one token a the model's output is the one token τ (σ a), and the prompt with this
output meets `IntegerModel.CanServeAtIndex`. -/
theorem canServeModelOutput_atVotingWeights (s : Cm.Scales) (hs : s.Lawful) (σ τ : ℕ → ℕ)
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

/-- At all valid settings and the made-up weights of `canServeModelOutput_atVotingWeights`, the
model answers τ (σ a) after the one token a. All layers of these weights are zero: the answer reads
the last token alone (for longer prompts: `Cm.target_bite2_pos`, Cm/TargetPartBite2K.lean, in the
library's types), and nothing passes through attention or a feed-forward block. -/
theorem modelNextToken_atVotingWeights (settings : IntegerTransformer.Settings)
    (valid : settingsAreValid settings = true) (σ τ : ℕ → ℕ) (hσ : ∀ t, σ t < 5120)
    (hτ : ∀ j, τ j < 202048) (a : ℕ) (ha : a < 202048) :
    modelNextToken settings (weightsOfIndex valid (Cm.biteI σ τ)) [a] = some (τ (σ a)) := by
  rw [modelNextToken_eq_nextToken (lawful_scalesOf valid) valid (settingsOf_scalesOf valid)]
  exact (canServeModelOutput_atVotingWeights (scalesOf settings) (lawful_scalesOf valid) σ τ hσ hτ a
    ha).2 0 Nat.zero_lt_one

/-- At all valid settings and the made-up weights of `canServeModelOutput_atVotingWeights`, the
prompt of one token a with the output of one token τ (σ a) meets `CanServe`. -/
theorem canServe_atVotingWeights (settings : IntegerTransformer.Settings)
    (valid : settingsAreValid settings = true) (σ τ : ℕ → ℕ) (hσ : ∀ t, σ t < 5120)
    (hτ : ∀ j, τ j < 202048) (a : ℕ) (ha : a < 202048) :
    CanServe settings (weightsOfIndex valid (Cm.biteI σ τ)) [a] [τ (σ a)] :=
  (canServe_weightsOfIndex_iff (lawful_scalesOf valid) valid (settingsOf_scalesOf valid) _ _ _).2
    (canServeModelOutput_atVotingWeights (scalesOf settings) (lawful_scalesOf valid) σ τ hσ hτ a
      ha).1

/-- At all valid settings some weights make the model answer a token other than 0. The weights are
made up; see `modelNextToken_atVotingWeights`. -/
theorem modelNextToken_answers_one (settings : IntegerTransformer.Settings)
    (valid : settingsAreValid settings = true) :
    ∃ weights : ModelWeights settings, modelNextToken settings weights [0] = some 1 :=
  ⟨_, modelNextToken_atVotingWeights settings valid (fun _ => 0) (fun _ => 1)
    (fun _ => by norm_num) (fun _ => by norm_num) 0 (by norm_num)⟩

/-- At all valid settings the model's answer depends on the weights: two sets of weights answer one
prompt differently. The weights are made up; see `modelNextToken_atVotingWeights`. -/
theorem modelNextToken_reads_weights (settings : IntegerTransformer.Settings)
    (valid : settingsAreValid settings = true) :
    ∃ first second : ModelWeights settings,
      modelNextToken settings first [0] ≠ modelNextToken settings second [0] := by
  refine ⟨weightsOfIndex valid (Cm.biteI (fun _ => 0) fun _ => 1),
    weightsOfIndex valid (Cm.biteI (fun _ => 0) fun _ => 0), fun h => ?_⟩
  rw [modelNextToken_atVotingWeights settings valid (fun _ => 0) (fun _ => 1)
      (fun _ => by norm_num) (fun _ => by norm_num) 0 (by norm_num),
    modelNextToken_atVotingWeights settings valid (fun _ => 0) (fun _ => 0)
      (fun _ => by norm_num) (fun _ => by norm_num) 0 (by norm_num)] at h
  exact absurd (Option.some.inj h) Nat.one_ne_zero

/-- At all valid settings the model's answer depends on the prompt: some weights answer the prompts
of one token 0 and of one token 1 differently. The weights are made up, and the answer reads the
last token alone; see `modelNextToken_atVotingWeights`. -/
theorem modelNextToken_reads_prompt (settings : IntegerTransformer.Settings)
    (valid : settingsAreValid settings = true) :
    ∃ weights : ModelWeights settings,
      modelNextToken settings weights [0] ≠ modelNextToken settings weights [1] := by
  have small : ∀ t : ℕ, t % 2 < 5120 := fun t =>
    Nat.lt_of_lt_of_le (Nat.mod_lt t (by norm_num)) (by norm_num)
  have small' : ∀ t : ℕ, t % 2 < 202048 := fun t =>
    Nat.lt_of_lt_of_le (Nat.mod_lt t (by norm_num)) (by norm_num)
  refine ⟨weightsOfIndex valid (Cm.biteI (fun t => t % 2) fun j => j % 2), fun h => ?_⟩
  rw [modelNextToken_atVotingWeights settings valid (fun t => t % 2) (fun j => j % 2) small small'
      0 (by norm_num),
    modelNextToken_atVotingWeights settings valid (fun t => t % 2) (fun j => j % 2) small small'
      1 (by norm_num)] at h
  exact absurd (Option.some.inj h) Nat.zero_ne_one

/-- At all valid settings there are two different models that serve one request alike: two sets of
weights at which the prompt of one token 0 with the output of one token 1 meets `CanServe` and is
the model's output, and which answer the prompt of one token 1 differently. The weights are made up
and all their layers are zero; see `modelNextToken_atVotingWeights`. -/
theorem twoModels_serve_one_request_alike (settings : IntegerTransformer.Settings)
    (valid : settingsAreValid settings = true) :
    ∃ first second : ModelWeights settings,
      CanServe settings first [0] [1] ∧ CanServe settings second [0] [1] ∧
      modelNextToken settings first [0] = some 1 ∧ modelNextToken settings second [0] = some 1 ∧
      modelNextToken settings first [1] ≠ modelNextToken settings second [1] := by
  have hσ : ∀ t : ℕ, t % 2 < 5120 := fun t =>
    Nat.lt_of_lt_of_le (Nat.mod_lt t (by norm_num)) (by norm_num)
  have h1 : ∀ _ : ℕ, (1 : ℕ) < 202048 := fun _ => by norm_num
  have h2 : ∀ j : ℕ, 1 - j % 2 < 202048 := fun j =>
    Nat.lt_of_le_of_lt (Nat.sub_le 1 _) (by norm_num)
  refine ⟨weightsOfIndex valid (Cm.biteI (fun t => t % 2) fun _ => 1),
    weightsOfIndex valid (Cm.biteI (fun t => t % 2) fun j => 1 - j % 2),
    canServe_atVotingWeights settings valid (fun t => t % 2) (fun _ => 1) hσ h1 0 (by norm_num),
    canServe_atVotingWeights settings valid (fun t => t % 2) (fun j => 1 - j % 2) hσ h2 0
      (by norm_num),
    modelNextToken_atVotingWeights settings valid (fun t => t % 2) (fun _ => 1) hσ h1 0
      (by norm_num),
    modelNextToken_atVotingWeights settings valid (fun t => t % 2) (fun j => 1 - j % 2) hσ h2 0
      (by norm_num), fun h => ?_⟩
  rw [modelNextToken_atVotingWeights settings valid (fun t => t % 2) (fun _ => 1) hσ h1 1
      (by norm_num),
    modelNextToken_atVotingWeights settings valid (fun t => t % 2) (fun j => 1 - j % 2) hσ h2 1
      (by norm_num)] at h
  exact absurd (Option.some.inj h) Nat.one_ne_zero

end VerifiableInference

#print axioms VerifiableInference.validSettings_two
#print axioms VerifiableInference.validSettings_exist
#print axioms VerifiableInference.notModelOutput_exists
#print axioms VerifiableInference.canServe_exists
#print axioms VerifiableInference.canServeModelOutput_atVotingWeights
#print axioms VerifiableInference.modelNextToken_atVotingWeights
#print axioms VerifiableInference.canServe_atVotingWeights
#print axioms VerifiableInference.twoModels_serve_one_request_alike
#print axioms VerifiableInference.modelNextToken_answers_one
#print axioms VerifiableInference.modelNextToken_reads_weights
#print axioms VerifiableInference.modelNextToken_reads_prompt
