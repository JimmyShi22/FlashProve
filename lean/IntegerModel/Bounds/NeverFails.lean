-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import IntegerModel.Bounds.Attention

/-!
# Weights that pass the worst-case check never fail a range condition

`allConditionsHold_of_boxWorstCaseCheck`: for settings, tables and weights that fit together
(`wellFormed`) and pass `boxWorstCaseCheck` (IntegerModel/Bounds/Check.lean), all range conditions
hold at all positions of every prompt (`isPrompt`). So the model has a value on every prompt
(`model_isSome_of_boxWorstCaseCheck`).

The proof: by induction over the layers, the stream above `l` layers is within `streamBound .. l`,
at every position of every prompt (`stream_within`). Then each layer's conditions follow from that
layer's part of the check (`layer_conditions`), and the final norm's from the check's last line.

Limits: those at the head of IntegerModel/Bounds/Check.lean. The theorem says nothing of weights
that do not pass, and this file says of no weights that they pass. Only Lean's core library is used.
-/

namespace IntegerTransformer.Bounds

/-- A mixture-of-experts layer has experts. -/
theorem isMixture_experts (s : Settings) (l : Nat) (mix : s.isMixture l = true) :
    0 < s.experts := by
  simp only [Settings.isMixture, Bool.and_eq_true, decide_eq_true_eq] at mix
  exact mix.1

/-- Row `t` that a layer returns: the feed-forward block's result on row `t` after attention. -/
theorem layer_out_read (s : Settings) (tables : Tables) (weights : Weights) (l : Nat) (X : Matrix)
    (t : Nat) (ht : t < X.size) :
    (layer s tables weights l X).out.entry t =
      (feedForward s (s.perLayer.entry l) tables (weights.perLayer.entry l) (s.isMixture l)
        ((attention s (s.perLayer.entry l) tables (weights.perLayer.entry l) X).out.entry
          t)).out := by
  simp only [layer, map_read, Array.size_map, (size_attention _ _ _ _ _).2.2.2.2.2, ht]

/-- Entry `t` of a layer's feed-forward records. -/
theorem layer_feedForward_read (s : Settings) (tables : Tables) (weights : Weights) (l : Nat)
    (X : Matrix) (t : Nat) (ht : t < X.size) :
    (layer s tables weights l X).feedForward.entry t =
      feedForward s (s.perLayer.entry l) tables (weights.perLayer.entry l) (s.isMixture l)
        ((attention s (s.perLayer.entry l) tables (weights.perLayer.entry l) X).out.entry t) := by
  simp only [layer, map_read, (size_attention _ _ _ _ _).2.2.2.2.2, ht]

/-- One layer's step on the stream's bound. -/
theorem layer_out_within (s : Settings) (tables : Tables) (weights : Weights) (l : Nat) (X : Matrix)
    (some_entry : 0 < tables.exponential.size) (first : 0 < tables.exponential.entry 0)
    (none_negative : (tables.exponential.all fun e => 0 ≤ e) = true)
    (routedFit : routedInputFits tables = true)
    (rows : ∀ t, t < X.size → (X.entry t).size = s.width)
    (within : ∀ t, t < X.size → RowWithin (streamBound s tables weights l) (X.entry t))
    (t : Nat) (ht : t < X.size) :
    RowWithin (streamBound s tables weights (l + 1))
      ((layer s tables weights l X).out.entry t) := by
  have attended := attention_out_within s (s.perLayer.entry l) tables (weights.perLayer.entry l) X
    (streamBound s tables weights l) some_entry first none_negative rows within t ht
  have size : ((attention s (s.perLayer.entry l) tables (weights.perLayer.entry l) X).out.entry
      t).size = s.width := by
    rw [(size_attention_rows _ _ _ _ _ t ht).2.2.2]; exact rows t ht
  have fed := feedForward_out_within s (s.perLayer.entry l) tables (weights.perLayer.entry l)
    (s.isMixture l) _ _ (isMixture_experts s l) size attended routedFit
  rw [layer_out_read s tables weights l X t ht]
  intro k inside
  have := fed k inside
  simp only [streamBound, sumOver, layerAdditionBound] at this ⊢
  omega

/-- The stream above `l` layers is within `streamBound .. l`, at every position of every prompt. Of
the check only `routedInputFits` is used. -/
theorem stream_within (s : Settings) (tables : Tables) (weights : Weights)
    (formed : wellFormed s tables weights = true) (routedFit : routedInputFits tables = true)
    (prompt : Array Nat) (prompt_ok : isPrompt s prompt = true) (l : Nat)
    (t : Nat) (ht : t < prompt.size) :
    RowWithin (streamBound s tables weights l)
      ((streamAbove (prompt.map fun token => weights.embedding.entry token)
        (firstLayers s tables weights (prompt.map fun token => weights.embedding.entry token)
          l)).entry t) := by
  have parts := wellFormed_spec s tables weights formed
  have shape := embedded_shape s tables weights prompt formed prompt_ok
  induction l generalizing t with
  | zero =>
    rw [streamAbove_zero, map_read _ _ _ ht]
    intro k _
    have token := (isPrompt_spec s prompt prompt_ok).2.2 t ht
    have := (maxUpTo_spec (fun token => magnitude ((weights.embedding.entry token).entry k))
      (s.vocabulary - 1)).1 (prompt.entry t) (by omega)
    simp only [streamBound, sumOver, embeddingBound]
    omega
  | succ l ih =>
    rw [streamAbove_succ]
    have stream := stream_shape s tables weights
      (prompt.map fun token => weights.embedding.entry token) s.width l
      (fun t ht => shape.2 t (by rw [← shape.1]; exact ht))
    apply layer_out_within s tables weights l _ parts.2.2.1.2.2.1 parts.2.2.1.2.2.2.1
      parts.2.2.1.2.2.2.2.1 routedFit
    · intro t ht
      exact stream.2 t (by rw [← stream.1]; exact ht)
    · intro t ht
      exact ih t (by rw [← shape.1, ← stream.1]; exact ht)
    · rw [stream.1, shape.1]; exact ht

/-- All conditions of one layer at one position. -/
theorem layer_conditions (s : Settings) (tables : Tables) (weights : Weights) (l : Nat) (X : Matrix)
    (some_entry : 0 < tables.exponential.size) (first : 0 < tables.exponential.entry 0)
    (none_negative : (tables.exponential.all fun e => 0 ≤ e) = true)
    (formedLayer : layerWellFormed s (s.perLayer.entry l) (weights.perLayer.entry l)
      (s.isMixture l) = true)
    (routedFit : routedInputFits tables = true) (fits : layerFits s tables weights l = true)
    (few : X.size ≤ s.positions) (rows : ∀ t, t < X.size → (X.entry t).size = s.width)
    (within : ∀ t, t < X.size → RowWithin (streamBound s tables weights l) (X.entry t))
    (t : Nat) (ht : t < X.size) :
    attentionOk (s.perLayer.entry l) (layer s tables weights l X).attention t = true ∧
    feedForwardOk (s.perLayer.entry l) ((layer s tables weights l X).feedForward.entry t) =
      true := by
  simp only [layerFits, Bool.and_eq_true] at fits
  have eps := (layerWellFormed_spec _ _ _ _ formedLayer).2.2.2.2.1
  have attended := attention_out_within s (s.perLayer.entry l) tables (weights.perLayer.entry l) X
    (streamBound s tables weights l) some_entry first none_negative rows within t ht
  have size : ((attention s (s.perLayer.entry l) tables (weights.perLayer.entry l) X).out.entry
      t).size = s.width := by
    rw [(size_attention_rows _ _ _ _ _ t ht).2.2.2]; exact rows t ht
  constructor
  · exact attentionOk_of_fits s (s.perLayer.entry l) tables (weights.perLayer.entry l) X
      (streamBound s tables weights l) eps.1 few rows within fits.1.1.1 fits.1.1.2 t ht
  · rw [layer_feedForward_read s tables weights l X t ht]
    exact feedForwardOk_of_fits s (s.perLayer.entry l) tables (weights.perLayer.entry l)
      (s.isMixture l) _ _ (isMixture_experts s l) eps.2 size attended routedFit fits.1.2 fits.2

/-- **Weights that pass the check never fail a range condition.** For settings, tables and weights
that fit together and pass the check, all range conditions hold at all positions of every prompt. -/
theorem allConditionsHold_of_boxWorstCaseCheck (settings : Settings) (tables : Tables)
    (weights : Weights) (formed : wellFormed settings tables weights = true)
    (passes : boxWorstCaseCheck settings tables weights = true)
    (prompt : Array Nat) (prompt_ok : isPrompt settings prompt = true) :
    allConditionsHold settings (trace settings tables weights prompt) = true := by
  simp only [boxWorstCaseCheck, Bool.and_eq_true, allBelow_spec] at passes
  have parts := wellFormed_spec settings tables weights formed
  have shape := embedded_shape settings tables weights prompt formed prompt_ok
  have few := (isPrompt_spec settings prompt prompt_ok).2.1
  have stream := fun l => stream_shape settings tables weights
    (prompt.map fun token => weights.embedding.entry token) settings.width l
    (fun t ht => shape.2 t (by rw [← shape.1]; exact ht))
  have within := stream_within settings tables weights formed passes.1.1 prompt prompt_ok
  simp only [allConditionsHold, List.all_eq_true, List.mem_range, Bool.and_eq_true]
  intro t ht
  have ht' : t < prompt.size := by
    have : (trace settings tables weights prompt).embedded.size = prompt.size := shape.1
    omega
  constructor
  · intro l hl
    have read : (trace settings tables weights prompt).layer.entry l =
        layer settings tables weights l
          (streamAbove (prompt.map fun token => weights.embedding.entry token)
            (firstLayers settings tables weights
              (prompt.map fun token => weights.embedding.entry token) l)) := by
      simp only [trace]
      rw [firstLayers_read _ _ _ _ _ _ hl]
    rw [read]
    apply layer_conditions settings tables weights l _ parts.2.2.1.2.2.1 parts.2.2.1.2.2.2.1
      parts.2.2.1.2.2.2.2.1 (parts.2.2.2.2.2.2 l hl) passes.1.1 (passes.1.2 l hl)
    · rw [(stream l).1, shape.1]; exact few
    · intro t ht
      exact (stream l).2 t (by rw [← (stream l).1]; exact ht)
    · intro t ht
      exact within l t (by rw [← shape.1, ← (stream l).1]; exact ht)
    · rw [(stream l).1, shape.1]; exact ht'
  · have read : (trace settings tables weights prompt).finalNorm.entry t =
        rmsNorm settings.finalBits settings.finalShift settings.finalEps
          ((streamAbove (prompt.map fun token => weights.embedding.entry token)
            (firstLayers settings tables weights
              (prompt.map fun token => weights.embedding.entry token) settings.layers)).entry
            t) := by
      simp only [trace]
      rw [map_read _ _ _ (by rw [(stream settings.layers).1, shape.1]; exact ht')]
    rw [read]
    apply normOk_of_normFits _ _ _ _ (streamBound settings tables weights settings.layers)
      parts.2.1.1 (within settings.layers t ht')
    rw [(stream settings.layers).2 t (by rw [shape.1]; exact ht')]
    exact passes.2

/-- So the model has a value on every prompt. -/
theorem model_isSome_of_boxWorstCaseCheck (settings : Settings) (tables : Tables)
    (weights : Weights) (formed : wellFormed settings tables weights = true)
    (passes : boxWorstCaseCheck settings tables weights = true)
    (prompt : Array Nat) (prompt_ok : isPrompt settings prompt = true) :
    (model settings tables weights prompt).isSome = true := by
  have hold :=
    allConditionsHold_of_boxWorstCaseCheck settings tables weights formed passes prompt prompt_ok
  simp [model, formed, prompt_ok, hold]

end IntegerTransformer.Bounds

