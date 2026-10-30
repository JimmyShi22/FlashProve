-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import IntegerModel.Model
import IntegerModel.Readable.Facts

/-!
# The sizes and bounds that the reads rely on

`IntegerModel/Model.lean` reads arrays with `v.entry k`, which gives 0 (or an empty array, or a
record of such) outside. The symbols (`dq`, `n_h`, `NE`, ...) and the conditions' numbers are those
of its comments. This file proves, each under the hypotheses of its statement, what the notes
"Reads:" in `IntegerModel/Model.lean` rest on:

- the sizes of the arrays that the steps from `addVectors` to `layer` make (part 1, with `size_product`
  and `size_tabulate` of IntegerModel/Readable/Facts.lean);
- the bounds on the indices that are not plain loop variables: heads, groups, rotary pairs, the
  softmax table's key, the
  chosen expert (part 2);
- what `wellFormed` and `isPrompt` say about the sizes of the arguments (part 3);
- that the stream has one row of `d` entries for each token, above every number of layers (part 4);
- stage by stage, the sizes and bounds that the reads rely on (parts 5 to 7, with parts 1 and 2);
- that a key which a table covers is read inside the table's entries (part 8; the ranges of the
  gate's key and the router's logit: part 2), and that the divisors that are neither constants nor
  powers of two are positive: a norm's root, a softmax's total, and the number of query heads for
  each key head (part 8; `wellFormed` asks directly that `dh` and `n_g` be positive).

Part 9 is a remark on the lower end of condition 2.

Limit: no theorem here says that these sizes and bounds fit the reads of `IntegerModel/Model.lean`:
`v.entry k` leaves no trace of whether it was inside. `Checked.lean` builds on this file and comes
at the question from another side: a version of the model with checked reads gives the same
values.
-/

namespace IntegerTransformer

/-! ## 1. The sizes of the arrays that the steps make -/

/-- `addVectors x y` has as many entries as `x`. -/
theorem size_addVec (x y : IntegerVector) : (addVectors x y).size = x.size := by
  simp only [addVectors, size_tabulate]

/-- A norm's quotient and result have as many entries as the row. -/
theorem size_rmsNorm (bits shift : Nat) (eps : Int) (x : IntegerVector) :
    (rmsNorm bits shift eps x).quotient.size = x.size ∧
    (rmsNorm bits shift eps x).out.size = x.size := by
  simp only [rmsNorm, Array.size_map, and_self]

/-- The rotated vector has as many entries as the vector. -/
theorem size_rotate (cosine sine : IntegerVector) (headDim : Nat) (A : IntegerVector) :
    (rotate cosine sine headDim A).size = A.size := by
  simp only [rotate, size_tabulate]

/-- All ten vectors of `projections`: those of the queries have `dq` entries, those of keys and
values `dkv`. -/
theorem size_projections (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (t : Nat) (a : IntegerVector) :
    let pr := projections s p tables w t a
    (pr.queryProducts.size = s.queryWidth ∧
      pr.rotatedQuery.size = s.queryWidth ∧
      pr.wideQuery.size = s.queryWidth ∧
      pr.query.size = s.queryWidth) ∧
    (pr.keyProducts.size = s.keyValueWidth ∧ pr.rotatedKey.size = s.keyValueWidth ∧
      pr.wideKey.size = s.keyValueWidth ∧ pr.key.size = s.keyValueWidth) ∧
    (pr.wideValue.size = s.keyValueWidth ∧ pr.value.size = s.keyValueWidth) := by
  simp only [projections, Array.size_map, size_rotate, size_product, and_self]

/-- The vectors of `attendHead`: those over `j` have `i + 1` entries, those over `c` have `dh`. -/
theorem size_attendHead (s : Settings) (p : LayerSettings) (tables : Tables)
    (projected : Array Projections) (i h : Nat) :
    let head := attendHead s p tables projected i h
    (head.scores.size = i + 1 ∧ head.distances.size = i + 1 ∧ head.exponentials.size = i + 1) ∧
    (head.mix.size = s.headDim ∧ head.out.size = s.headDim) := by
  simp only [attendHead, Array.size_map, size_tabulate, and_self]

/-- The six arrays of `attention` have one entry for each position. -/
theorem size_attention (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (x : Matrix) :
    let a := attention s p tables w x
    a.norm.size = x.size ∧ a.projected.size = x.size ∧ a.heads.size = x.size ∧
    a.mixed.size = x.size ∧ a.addition.size = x.size ∧ a.out.size = x.size := by
  simp only [attention, Array.size_map, size_tabulate, and_self]

/-- At a position `t`: there are `n_h` heads, `o` has `dq` entries, `ad` has `d`, and `x'` has as
many as `x`. -/
theorem size_attention_rows (s : Settings) (p : LayerSettings) (tables : Tables) (w : LayerWeights)
    (x : Matrix) (t : Nat) (h : t < x.size) :
    let a := attention s p tables w x
    (a.heads.entry t).size = s.queryHeads ∧
    (a.mixed.entry t).size = s.queryWidth ∧
    (a.addition.entry t).size = s.width ∧
    (a.out.entry t).size = (x.entry t).size := by
  simp only [attention, tabulate_read, map_read, size_tabulate, size_addVec, size_product,
    Array.size_map, h, and_self]

/-- All seven vectors of `hiddenUnits` have `hidden` entries. -/
theorem size_hiddenUnits (tables : Tables) (w : GatedWeights)
    (hidden gateShift upShift : Nat) (z : IntegerVector) :
    let units := hiddenUnits tables w hidden gateShift upShift z
    units.wideGate.size = hidden ∧ units.lowByte.size = hidden ∧ units.highPart.size = hidden ∧
      units.clampedHigh.size = hidden ∧ units.key.size = hidden ∧ units.activation.size = hidden ∧
      units.up.size = hidden := by
  simp only [hiddenUnits, Array.size_map, size_tabulate, size_product, and_self]

/-- The router's four vectors have `NE` entries, and the routed expert's input has as many as
`m`. -/
theorem size_routedExpert (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (m : IntegerVector) :
    let r := routedExpert s p tables w m
    r.wide.size = s.experts ∧ r.high.size = s.experts ∧ r.low.size = s.experts ∧
    r.logits.size = s.experts ∧ r.input.size = m.size := by
  simp only [routedExpert, Array.size_map, size_tabulate, size_product, and_self]

/-- `ad` has `d` entries, and `x''` has as many as `x'`. -/
theorem size_feedForward (s : Settings) (p : LayerSettings) (tables : Tables) (w : LayerWeights)
    (mixture : Bool) (x : IntegerVector) :
    (feedForward s p tables w mixture x).addition.size = s.width ∧
    (feedForward s p tables w mixture x).out.size = x.size := by
  cases mixture <;> simp [feedForward, size_tabulate, size_addVec]

/-- A layer returns as many rows as it takes in, and keeps one record of the feed-forward block for
each. -/
theorem size_layer (s : Settings) (tables : Tables) (weights : Weights) (l : Nat) (x : Matrix) :
    (layer s tables weights l x).out.size = x.size ∧
    (layer s tables weights l x).feedForward.size = x.size := by
  simp only [layer, Array.size_map, (size_attention _ _ _ _ _).2.2.2.2.2, and_self]

/-- Row `t` that a layer returns has as many entries as row `t` that it takes in. -/
theorem size_layer_row (s : Settings) (tables : Tables) (weights : Weights) (l : Nat) (x : Matrix)
    (t : Nat) (h : t < x.size) :
    ((layer s tables weights l x).out.entry t).size = (x.entry t).size := by
  have rows := (size_attention s (s.perLayer.entry l) tables (weights.perLayer.entry l) x).2.2.2.2.2
  have row :=
    (size_attention_rows s (s.perLayer.entry l) tables (weights.perLayer.entry l) x t h).2.2.2
  simp only [layer, map_read, Array.size_map, rows, h, (size_feedForward _ _ _ _ _ _).2, row]

/-! ## 2. The indices that are not plain loop variables -/

/-- Entry `c < dh` of head `h < n`, at index `h dh + c`, is inside a vector of `n` heads. -/
theorem head_index (n dh h c : Nat) (hh : h < n) (hc : c < dh) : h * dh + c < n * dh := by
  have step : (h + 1) * dh ≤ n * dh := Nat.mul_le_mul_right dh hh
  rw [Nat.succ_mul] at step
  omega

/-- If `n_g` divides `n_h`, the key and value head `g = h / (n_h / n_g)` that query head `h` reads
is one of the `n_g` heads. -/
theorem group_index (nh ng h : Nat) (divides : nh % ng = 0) (hh : h < nh) : h / (nh / ng) < ng := by
  have whole : ng * (nh / ng) = nh := by
    have := Nat.div_add_mod nh ng
    omega
  have positive : 0 < nh / ng := by
    apply Nat.pos_of_ne_zero
    intro zero
    rw [zero, Nat.mul_zero] at whole
    omega
  rw [Nat.div_lt_iff_lt_mul positive, whole]
  exact hh

/-- An index `j` into `n` heads side by side splits into a head `j / dh` and an entry `j % dh` of
it. -/
theorem split_index (n dh j : Nat) (h : j < n * dh) : j / dh < n ∧ j % dh < dh := by
  have positive : 0 < dh := by
    apply Nat.pos_of_ne_zero
    intro zero
    rw [zero, Nat.mul_zero] at h
    omega
  exact ⟨(Nat.div_lt_iff_lt_mul positive).mpr h, Nat.mod_lt _ positive⟩

/-- The reads of `rotate`, for `dh` positive and even, a size that is a multiple of `dh` and `j`
below it: the angle's number is below `dh / 2`; the partner `j + 1` of an even `j` is inside; an odd
`j` has a partner `j - 1`. -/
theorem rotate_index (size dh j : Nat) (positive : 0 < dh) (even : dh % 2 = 0)
    (heads : size % dh = 0) (h : j < size) :
    j % dh / 2 < dh / 2 ∧ (j % 2 = 0 → j + 1 < size) ∧ (j % 2 ≠ 0 → 1 ≤ j) := by
  have inHead : j % dh < dh := Nat.mod_lt _ positive
  have sizeEven : size % 2 = 0 := by
    have a := Nat.div_add_mod size dh
    have b := Nat.div_add_mod dh 2
    have c : size = 2 * (dh / 2 * (size / dh)) := by
      rw [← Nat.mul_assoc]
      have : 2 * (dh / 2) = dh := by omega
      rw [this]
      omega
    omega
  refine ⟨by omega, fun _ => by omega, fun _ => by omega⟩

/-- A score's distance to the largest score of its row, divided by a power of two, is not negative.
So its `toNat` is the number itself, and the test "below the table's size" is all that the read of
the softmax table needs. -/
theorem distance_nonneg (f : Nat → Int) (i j k : Nat) (h : j ≤ i) :
    0 ≤ (maxUpTo f i - f j) / 2 ^ k := by
  have := (maxUpTo_spec f i).1 j h
  exact Int.ediv_nonneg (by omega) (Int.le_of_lt (Int.pow_pos (by decide)))

/-- The chosen expert is one of the `NE` experts, if there is any. -/
theorem chosen_index (s : Settings) (p : LayerSettings) (tables : Tables) (w : LayerWeights)
    (m : IntegerVector) (some_expert : 0 < s.experts) :
    (routedExpert s p tables w m).chosen < s.experts := by
  simp only [routedExpert]
  exact (firstArgmax_spec _ _ some_expert).1

/-- The greedy choice is a token, if the vocabulary is not empty. -/
theorem choice_index (lam : IntegerVector) (V : Nat) (some_token : 0 < V) :
    firstArgmax (fun v => lam.entry v) V < V :=
  (firstArgmax_spec _ _ some_token).1

/-- The gate's key is in `-32,640 .. 32,639`, whatever the wide key is. So the SiLU table, which
`wellFormed` asks to have the keys `-32,768 .. 32,767`, has it. -/
theorem gateKeyOf_range (gw : Int) : -32640 ≤ gateKeyOf gw ∧ gateKeyOf gw ≤ 32639 := by
  have byte := balancedLowByte_spec gw
  have high := clamp_spec ((gw - balancedLowByte gw) / 256) 127 (by decide)
  simp only [gateKeyOf]
  omega

/-- The router's logit is in `-16,376 .. 16,383`, whatever the wide logit is. So the sigmoid table,
which `wellFormed`
asks to have the keys `-16,384 .. 16,383`, has it. -/
theorem routerLogitOf_range (lw : Int) : -16376 ≤ routerLogitOf lw ∧ routerLogitOf lw ≤ 16383 := by
  have high := clamp_spec (lw / 8) 2047 (by decide)
  simp only [routerLogitOf]
  omega

/-! ## 3. What `wellFormed` and `isPrompt` say about the arguments -/

/-- A matrix that `hasSize` has that many rows, and each row that many entries. -/
theorem hasSize_spec (rows columns : Nat) (W : Matrix) (h : hasSize rows columns W = true) :
    W.size = rows ∧ ∀ k, k < rows → (W.entry k).size = columns := by
  simp only [hasSize, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h
  refine ⟨h.1, fun k hk => ?_⟩
  have inside : k < W.size := by omega
  rw [entry_inside W k inside]
  exact h.2 k inside

/-- The parts of `wellFormed`, as statements. -/
theorem wellFormed_spec (s : Settings) (tables : Tables) (weights : Weights)
    (h : wellFormed s tables weights = true) :
    (0 < s.keyValueHeads ∧ 0 < s.queryHeads ∧ s.queryHeads % s.keyValueHeads = 0 ∧ 0 < s.headDim ∧
      s.headDim % 2 = 0 ∧ 0 < s.vocabulary ∧ (s.experts = 0 ∨ s.hidden = 2 * s.expertHidden)) ∧
    (1 ≤ s.finalEps ∧ 1 ≤ s.finalShift) ∧
    (hasSize s.positions (s.headDim / 2) tables.cosine = true ∧
      hasSize s.positions (s.headDim / 2) tables.sine = true ∧
      0 < tables.exponential.size ∧
      0 < tables.exponential.entry 0 ∧
      (tables.exponential.all fun e => 0 ≤ e) = true ∧
      tables.silu.covers (-32768) 32767 = true ∧
      tables.sigmoid.covers (-16384) 16383 = true) ∧
    (hasSize s.vocabulary s.width weights.embedding = true ∧
      hasSize s.width s.vocabulary weights.head = true) ∧
    (s.perLayer.size = s.layers ∧
      weights.perLayer.size = s.layers ∧
      ∀ l, l < s.layers →
        layerWellFormed s (s.perLayer.entry l) (weights.perLayer.entry l) (s.isMixture l) =
          true) := by
  simp only [wellFormed, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, b3⟩, b4⟩, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩,
                  c6⟩,
                c7⟩,
              d1⟩,
            d2⟩,
          e1⟩,
        e2⟩,
      e3⟩ := h
  exact ⟨⟨a1, a2, a3, a4, a5, a6, a7⟩, ⟨b3, b4⟩, ⟨c1, c2, c3, c4, c5, c6, c7⟩, ⟨d1, d2⟩, e1, e2, e3⟩

/-- The parts of `isPrompt`, as statements. -/
theorem isPrompt_spec (s : Settings) (prompt : Array Nat) (h : isPrompt s prompt = true) :
    0 < prompt.size ∧
    prompt.size ≤ s.positions ∧
    ∀ t, t < prompt.size → prompt.entry t < s.vocabulary := by
  simp only [isPrompt, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true] at h
  refine ⟨h.1.1, h.1.2, fun t ht => ?_⟩
  rw [entry_inside prompt t ht]
  exact h.2 t ht

/-! ## 4. The shape of the stream, for arguments that fit together and a prompt -/

/-- For arguments that fit together and a prompt, the embedded tokens are one row of `d` entries for
each token. -/
theorem embedded_shape (s : Settings) (tables : Tables) (weights : Weights) (prompt : Array Nat)
    (formed : wellFormed s tables weights = true) (prompt_ok : isPrompt s prompt = true) :
    (prompt.map fun token => weights.embedding.entry token).size = prompt.size ∧
    ∀ t, t < prompt.size →
      ((prompt.map fun token => weights.embedding.entry token).entry t).size = s.width := by
  refine ⟨Array.size_map .., fun t ht => ?_⟩
  rw [map_read _ _ _ ht]
  have embedding := hasSize_spec _ _ _ (wellFormed_spec s tables weights formed).2.2.2.1.1
  exact embedding.2 _ ((isPrompt_spec s prompt prompt_ok).2.2 t ht)

/-- If each row of the stream below has `d` entries, then above any number of layers it has as many
rows, each of `d` entries. -/
theorem stream_shape (s : Settings) (tables : Tables) (weights : Weights) (x0 : Matrix) (d l : Nat)
    (rows : ∀ t, t < x0.size → (x0.entry t).size = d) :
    (streamAbove x0 (firstLayers s tables weights x0 l)).size = x0.size ∧
    ∀ t, t < x0.size → ((streamAbove x0 (firstLayers s tables weights x0 l)).entry t).size = d := by
  induction l with
  | zero => rw [streamAbove_zero]; exact ⟨rfl, rows⟩
  | succ l ih =>
    rw [streamAbove_succ]
    refine ⟨by rw [(size_layer _ _ _ _ _).1, ih.1], fun t ht => ?_⟩
    rw [size_layer_row _ _ _ _ _ _ (by rw [ih.1]; exact ht)]
    exact ih.2 t ht

/-- **The shape of the trace.** For arguments that fit together and a prompt of `n` tokens: there
are `L` layers; the stream that enters each layer, and the last stream, have `n` rows of `d`
entries; there are `n` final norms, `n` rows of
`V` logits and `n` choices, each of them a token. -/
theorem trace_shape (s : Settings) (tables : Tables) (weights : Weights) (prompt : Array Nat)
    (formed : wellFormed s tables weights = true) (prompt_ok : isPrompt s prompt = true) :
    let values := trace s tables weights prompt
    values.embedded.size = prompt.size ∧ values.layer.size = s.layers ∧
    (∀ l, l < s.layers → (values.layer.entry l).input.size = prompt.size ∧
      ∀ t, t < prompt.size → ((values.layer.entry l).input.entry t).size = s.width) ∧
    (values.last.size = prompt.size ∧ ∀ t, t < prompt.size → (values.last.entry t).size = s.width) ∧
    values.finalNorm.size = prompt.size ∧
    (values.logits.size = prompt.size ∧
      ∀ t, t < prompt.size → (values.logits.entry t).size = s.vocabulary) ∧
    (values.choices.size = prompt.size ∧
      ∀ t, t < prompt.size → values.choices.entry t < s.vocabulary) := by
  have embedded := embedded_shape s tables weights prompt formed prompt_ok
  have shape := fun l =>
    stream_shape s tables weights _ s.width l (by rw [embedded.1]; exact embedded.2)
  have some_token := (wellFormed_spec s tables weights formed).1.2.2.2.2.2.1
  simp only [embedded.1] at shape
  simp only [trace, Array.size_map, size_firstLayers, true_and]
  refine ⟨fun l hl => ?_, shape s.layers, (shape s.layers).1, ⟨(shape s.layers).1, fun t ht => ?_⟩,
    (shape s.layers).1, fun t ht => ?_⟩
  · rw [firstLayers_read _ _ _ _ _ _ hl]
    exact shape l
  · rw [map_read _ _ _ (by rw [Array.size_map, (shape s.layers).1]; exact ht), size_product]
  · rw [map_read _ _ _ (by rw [Array.size_map, Array.size_map, (shape s.layers).1]; exact ht)]
    exact choice_index _ _ some_token

/-! ## 5. One stage: the sizes and bounds that the reads of attention rely on -/

/-- The parts of `layerWellFormed` that are about sizes and about `eps`, as statements. -/
theorem layerWellFormed_spec (s : Settings) (p : LayerSettings) (w : LayerWeights) (mixture : Bool)
    (h : layerWellFormed s p w mixture = true) :
    hasSize s.width s.queryWidth w.query = true ∧
    hasSize s.width s.keyValueWidth w.key = true ∧
    hasSize s.width s.keyValueWidth w.value = true ∧
    hasSize s.queryWidth s.width w.output = true ∧
    (1 ≤ p.attentionEps ∧ 1 ≤ p.feedForwardEps) ∧
    (mixture = false → w.shared.hasSizes s.width s.hidden = true) ∧
    (mixture = true →
      w.shared.hasSizes s.width s.expertHidden = true ∧
      hasSize s.width s.experts w.router = true ∧
      w.routed.size = s.experts ∧
      ∀ e, e < s.experts → (w.routed.entry e).hasSizes s.width s.expertHidden = true) := by
  simp only [layerWellFormed, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨q, k⟩, v⟩, o⟩, eps1⟩, eps2⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, rest⟩ := h
  refine ⟨q, k, v, o, ⟨eps1, eps2⟩, fun dense => ?_, fun mix => ?_⟩
  · simpa [dense] using rest
  · simp only [mix, if_true, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq, Array.all_eq_true] at rest
    obtain ⟨⟨⟨⟨⟨⟨shared, router⟩, count⟩, each⟩, _⟩, _⟩, _⟩ := rest
    refine ⟨shared, router, count, fun e he => ?_⟩
    have inside : e < w.routed.size := by omega
    rw [entry_inside w.routed e inside]
    exact each e inside

/-- **The sizes and bounds that the reads of attention rely on**, at a position `t`, for a layer
that is well formed, a shape that obeys docs/model.md, section 2 (the statement asks of it only that
`n_g` divide `n_h`), rotary tables of `T` rows of `dh / 2` entries and a stream of at most `T` rows
of `d` entries. The statement goes through the reads of `projections`, `rotate`, `attendHead` and
`attention` in the order of `IntegerModel/Model.lean`: it gives the size of the array that is read,
or the bound on the index. (Others: `size_attention`, `size_attendHead`, `distance_nonneg`, and
`rotate_index`, which also asks that `dh` be positive and even.) -/
theorem attention_reads (s : Settings) (p : LayerSettings) (tables : Tables) (w : LayerWeights)
    (mixture : Bool) (x : Matrix) (formed : layerWellFormed s p w mixture = true)
    (divides : s.queryHeads % s.keyValueHeads = 0)
    (cosines : hasSize s.positions (s.headDim / 2) tables.cosine = true)
    (sines : hasSize s.positions (s.headDim / 2) tables.sine = true) (few : x.size ≤ s.positions)
    (rows : ∀ t, t < x.size → (x.entry t).size = s.width) (t : Nat) (ht : t < x.size) :
    let a := attention s p tables w x
    -- the three products of the normed row: it has d entries, and the matrices have d rows of dq or
    -- dkv entries
    (a.norm.entry t).out.size = s.width ∧
    (w.query.size = s.width ∧ ∀ k, k < s.width → (w.query.entry k).size = s.queryWidth) ∧
    (w.key.size = s.width ∧ ∀ k, k < s.width → (w.key.entry k).size = s.keyValueWidth) ∧
    (w.value.size = s.width ∧ ∀ k, k < s.width → (w.value.entry k).size = s.keyValueWidth) ∧
    -- the rotary tables have a row t, of dh / 2 entries; the rotated vectors are whole heads (see
    -- rotate_index)
    (t < tables.cosine.size ∧ (tables.cosine.entry t).size = s.headDim / 2) ∧
    (t < tables.sine.size ∧ (tables.sine.entry t).size = s.headDim / 2) ∧
    (s.queryWidth % s.headDim = 0 ∧ s.keyValueWidth % s.headDim = 0) ∧
    -- attendHead at position t, head h: positions j ≤ t, and entries of the query, key and value
    -- heads
    (∀ j h c, j ≤ t → h < s.queryHeads → c < s.headDim →
      j < a.projected.size ∧ h * s.headDim + c < (a.projected.entry t).query.size ∧
      h / (s.queryHeads / s.keyValueHeads) * s.headDim + c < (a.projected.entry j).key.size ∧
      h / (s.queryHeads / s.keyValueHeads) * s.headDim + c < (a.projected.entry j).value.size) ∧
    -- the heads side by side
    (∀ j, j < s.queryWidth →
      j / s.headDim < (a.heads.entry t).size ∧
      j % s.headDim < ((a.heads.entry t).entry (j / s.headDim)).out.size) ∧
    -- the output projection, and the residual addition
    ((a.mixed.entry t).size = s.queryWidth ∧ w.output.size = s.queryWidth ∧
      ∀ k, k < s.queryWidth → (w.output.entry k).size = s.width) ∧
    (a.addition.entry t).size = (x.entry t).size := by
  have sizes := layerWellFormed_spec s p w mixture formed
  have cosine := hasSize_spec _ _ _ cosines
  have sine := hasSize_spec _ _ _ sines
  have atRow := size_attention_rows s p tables w x t ht
  have projectedAt : ∀ j, j < x.size → (attention s p tables w x).projected.entry j =
      projections s p tables w j ((attention s p tables w x).norm.entry j).out := by
    intro j hj
    simp only [attention, tabulate_read, hj]
  refine ⟨?_,
    hasSize_spec _ _ _ sizes.1,
    hasSize_spec _ _ _ sizes.2.1,
    hasSize_spec _ _ _ sizes.2.2.1,
    ⟨by omega, cosine.2 t (by omega)⟩,
    ⟨by omega, sine.2 t (by omega)⟩,
    ⟨Nat.mul_mod_left _ _, Nat.mul_mod_left _ _⟩,
    fun j h c hj hh hc => ?_,
    fun j hj => ?_,
    ⟨atRow.2.1, hasSize_spec _ _ _ sizes.2.2.2.1⟩,
    by rw [atRow.2.2.1, rows t ht]⟩
  · simp only [attention, map_read, ht, (size_rmsNorm _ _ _ _).2, rows t ht]
  · have group := group_index _ _ h divides hh
    rw [(size_attention s p tables w x).2.1, projectedAt t ht, projectedAt j (by omega)]
    have here := size_projections s p tables w t ((attention s p tables w x).norm.entry t).out
    have there := size_projections s p tables w j ((attention s p tables w x).norm.entry j).out
    rw [here.1.2.2.2, there.2.1.2.2.2, there.2.2.2]
    exact ⟨by omega, head_index _ _ _ _ hh hc,
      head_index _ _ _ _ group hc, head_index _ _ _ _ group hc⟩
  · have split := split_index _ _ _ hj
    refine ⟨by rw [atRow.1]; exact split.1, ?_⟩
    simp only [attention, tabulate_read, ht, split.1, (size_attendHead _ _ _ _ _ _).2.2]
    exact split.2

/-! ## 6. The other stages: feed-forward, the head, the conditions, the last read -/

/-- The three matrices of a block that `hasSizes`: their numbers of rows, and the size of each
row. -/
theorem hasSizes_spec (d h : Nat) (w : GatedWeights) (sizes : w.hasSizes d h = true) :
    (w.gate.size = d ∧ ∀ k, k < d → (w.gate.entry k).size = h) ∧
    (w.up.size = d ∧ ∀ k, k < d → (w.up.entry k).size = h) ∧
    (w.down.size = h ∧ ∀ j, j < h → (w.down.entry j).size = d) := by
  simp only [GatedWeights.hasSizes, Bool.and_eq_true] at sizes
  exact ⟨hasSize_spec _ _ _ sizes.1.1, hasSize_spec _ _ _ sizes.1.2, hasSize_spec _ _ _ sizes.2⟩

/-- **The sizes and bounds that the reads of the feed-forward block rely on**, for a layer that is
well formed, a stream row of `d` entries and, in a mixture-of-experts layer, `NE > 0`. The normed
row has `d` entries. In a dense layer the block's matrices have the sizes for `f` units. In a
mixture-of-experts layer the shared expert's have the sizes for `fe` units, the router has `d` rows
of `NE` entries, the chosen expert is one of the experts that are there, its matrices have the sizes
for `fe` units, and its input has `d` entries. The addition has as many entries as the row. (The
vectors of the hidden units have the block's number of entries by `size_hiddenUnits`, those of the
router `NE` by `size_routedExpert`; the keys that are read are in the intervals of `gateKeyOf_range`
and `routerLogitOf_range`, which `wellFormed` asks the two tables to have.) -/
theorem feedForward_reads (s : Settings) (p : LayerSettings) (tables : Tables) (w : LayerWeights)
    (mixture : Bool) (x : IntegerVector) (formed : layerWellFormed s p w mixture = true)
    (some_expert : mixture = true → 0 < s.experts) (row : x.size = s.width) :
    let m := (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out
    m.size = s.width ∧
    (mixture = false → w.shared.hasSizes s.width s.hidden = true) ∧
    (mixture = true →
      w.shared.hasSizes s.width s.expertHidden = true ∧
      (w.router.size = s.width ∧ ∀ k, k < s.width → (w.router.entry k).size = s.experts) ∧
      (routedExpert s p tables w m).chosen < w.routed.size ∧
      (w.routed.entry ((routedExpert s p tables w m).chosen)).hasSizes s.width s.expertHidden =
        true ∧
      (routedExpert s p tables w m).input.size = s.width) ∧
    (feedForward s p tables w mixture x).addition.size = x.size := by
  have sizes := layerWellFormed_spec s p w mixture formed
  have normed := (size_rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).2
  refine ⟨by rw [normed, row], sizes.2.2.2.2.2.1, fun mix => ?_,
    by rw [(size_feedForward _ _ _ _ _ _).1, row]⟩
  obtain ⟨shared, router, count, each⟩ := sizes.2.2.2.2.2.2 mix
  have chosen := chosen_index s p tables w
    (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out (some_expert mix)
  exact ⟨shared, hasSize_spec _ _ _ router, by rw [count]; exact chosen, each _ chosen,
    by rw [(size_routedExpert _ _ _ _ _).2.2.2.2, normed, row]⟩

/-- **The sizes and bounds that the reads of the head, of the range conditions and of `model` rely
on**, for arguments that fit together and a prompt of `n` tokens. At each position the final norm's
result has `d` entries, and the output matrix has `d` rows of `V` entries. In each layer the arrays
that the conditions read have `n` entries. The last position `n - 1` is a position. -/
theorem head_and_condition_reads (s : Settings) (tables : Tables) (weights : Weights)
    (prompt : Array Nat) (formed : wellFormed s tables weights = true)
    (prompt_ok : isPrompt s prompt = true) :
    let values := trace s tables weights prompt
    (∀ t, t < prompt.size → (values.finalNorm.entry t).out.size = s.width) ∧
    (weights.head.size = s.width ∧ ∀ k, k < s.width → (weights.head.entry k).size = s.vocabulary) ∧
    (∀ l, l < s.layers →
      (values.layer.entry l).attention.norm.size = prompt.size ∧
      (values.layer.entry l).attention.projected.size = prompt.size ∧
      (values.layer.entry l).feedForward.size = prompt.size) ∧
    prompt.size - 1 < values.choices.size := by
  have shape := trace_shape s tables weights prompt formed prompt_ok
  have some_token := (isPrompt_spec s prompt prompt_ok).1
  refine ⟨fun t ht => ?_,
    hasSize_spec _ _ _ (wellFormed_spec s tables weights formed).2.2.2.1.2,
    fun l hl => ?_,
    by rw [shape.2.2.2.2.2.2.1]; omega⟩
  · have last := shape.2.2.2.1
    simp only [trace] at last ⊢
    rw [map_read _ _ _ (by rw [last.1]; exact ht), (size_rmsNorm _ _ _ _).2]
    exact last.2 t ht
  · have input := (shape.2.2.1 l hl).1
    simp only [trace] at input ⊢
    rw [firstLayers_read _ _ _ _ _ _ hl] at input ⊢
    simp only [layer] at input
    refine ⟨?_, ?_, ?_⟩
    · simp only [layer]; rw [(size_attention _ _ _ _ _).1, input]
    · simp only [layer]; rw [(size_attention _ _ _ _ _).2.1, input]
    · rw [(size_layer _ _ _ _ _).2, input]

/-! ## 7. For arguments that fit together and a prompt, both stage theorems apply in every layer -/

/-- For arguments that fit together and a prompt, layer `l < L` of the trace is `layer` applied to
its own input `x`, and all hypotheses of `attention_reads` (for `x`) and of `feedForward_reads` (for
each row of the stream after attention) hold. -/
theorem stage_hypotheses (s : Settings) (tables : Tables) (weights : Weights)
    (prompt : Array Nat) (formed : wellFormed s tables weights = true)
    (prompt_ok : isPrompt s prompt = true) (l : Nat) (hl : l < s.layers) :
    let x := ((trace s tables weights prompt).layer.entry l).input
    (trace s tables weights prompt).layer.entry l = layer s tables weights l x ∧
    layerWellFormed s (s.perLayer.entry l) (weights.perLayer.entry l) (s.isMixture l) = true ∧
    s.queryHeads % s.keyValueHeads = 0 ∧
    hasSize s.positions (s.headDim / 2) tables.cosine = true ∧
    hasSize s.positions (s.headDim / 2) tables.sine = true ∧
    x.size ≤ s.positions ∧ (∀ t, t < x.size → (x.entry t).size = s.width) ∧
    (s.isMixture l = true → 0 < s.experts) ∧
    (∀ t, t < x.size →
      ((attention s (s.perLayer.entry l) tables (weights.perLayer.entry l) x).out.entry t).size =
        s.width) := by
  have parts := wellFormed_spec s tables weights formed
  have shape := (trace_shape s tables weights prompt formed prompt_ok).2.2.1 l hl
  have few := (isPrompt_spec s prompt prompt_ok).2.1
  have rows : ∀ t, t < ((trace s tables weights prompt).layer.entry l).input.size →
      (((trace s tables weights prompt).layer.entry l).input.entry t).size = s.width := by
    intro t ht
    exact shape.2 t (by rw [← shape.1]; exact ht)
  refine ⟨?_, parts.2.2.2.2.2.2 l hl, parts.1.2.2.1, parts.2.2.1.1, parts.2.2.1.2.1,
    by rw [shape.1]; exact few, rows, fun mix => ?_, fun t ht => ?_⟩
  · simp only [trace]
    rw [firstLayers_read _ _ _ _ _ _ hl]
    simp only [layer]
  · simp only [Settings.isMixture, Bool.and_eq_true, decide_eq_true_eq] at mix
    exact mix.1
  · rw [(size_attention_rows _ _ _ _ _ t ht).2.2.2]
    exact rows t ht

/-! ## 8. The tables' keys, and the divisors -/

/-- A key that the table covers is read at an index inside the table's entries. -/
theorem read_inside (table : KeyedTable) (low high key : Int)
    (covers : table.covers low high = true) (h1 : low ≤ key) (h2 : key ≤ high) :
    table.lowestKey ≤ key ∧ (key - table.lowestKey).toNat < table.entries.size := by
  simp only [KeyedTable.covers, Bool.and_eq_true, decide_eq_true_eq] at covers
  omega

/-- The divisor `n_h / n_g`, the number of query heads for each key head, is at least 1, if both
numbers are positive and `n_g` divides `n_h`. -/
theorem heads_per_group_positive (nh ng : Nat) (a : 0 < ng) (b : 0 < nh) (c : nh % ng = 0) :
    1 ≤ nh / ng := by
  have : ng ≤ nh := Nat.le_of_dvd b (Nat.dvd_of_mod_eq_zero c)
  exact (Nat.le_div_iff_mul_le a).mpr (by omega)

/-- The divisor of a norm: the root is at least 1, if `eps` is. -/
theorem root_positive (bits shift : Nat) (eps : Int) (x : IntegerVector) (h : 1 ≤ eps) :
    1 ≤ (rmsNorm bits shift eps x).root := by
  have sum : 0 ≤ sumOver x.size fun k => x.entry k * x.entry k :=
    sumOver_nonneg _ (fun k => square_nonneg _) _
  simp only [rmsNorm]
  generalize sumOver x.size (fun k => x.entry k * x.entry k) = v at sum
  have spec := isqrt_spec (v + eps).toNat
  generalize integerSquareRoot (v + eps).toNat = r at spec
  have : r ≠ 0 := by
    intro zero
    subst zero
    omega
  omega

/-- An entry of a vector without negative entries is not negative, and neither is a read outside it,
which gives 0. -/
theorem read_nonneg (v : IntegerVector) (none_negative : (v.all fun e => 0 ≤ e) = true) (k : Nat) :
    0 ≤ v.entry k := by
  simp only [Array.all_eq_true, decide_eq_true_eq] at none_negative
  by_cases inside : k < v.size
  · rw [entry_inside v k inside]
    exact none_negative k inside
  · rw [entry_outside v k inside]
    exact Int.le_refl 0

/-- The divisor of attention's last step: the total of the softmax's weights is positive, if the
table is not empty, its first entry is positive and none of its entries is negative. The top score
has distance 0, so its weight is the table's first entry, and no weight is negative. -/
theorem total_positive (s : Settings) (p : LayerSettings) (tables : Tables)
    (projected : Array Projections) (i h : Nat) (some_entry : 0 < tables.exponential.size)
    (first : 0 < tables.exponential.entry 0)
    (none_negative : (tables.exponential.all fun e => 0 ≤ e) = true) :
    0 < (attendHead s p tables projected i h).total := by
  have sizes := (size_attendHead s p tables projected i h).1
  have weight : ∀ j, j < i + 1 →
      (attendHead s p tables projected i h).exponentials.entry j =
        if (attendHead s p tables projected i h).distances.entry j < tables.exponential.size then
          tables.exponential.entry (((attendHead s p tables projected i h).distances.entry j).toNat)
        else 0 := by
    intro j hj
    have inside : j < (attendHead s p tables projected i h).distances.size := by
      rw [sizes.2.1]; exact hj
    have made : (attendHead s p tables projected i h).exponentials =
        (attendHead s p tables projected i h).distances.map fun (u : Int) =>
          if u < tables.exponential.size then tables.exponential.entry u.toNat else 0 := rfl
    rw [made]
    exact map_read _ _ _ inside
  have distance : ∀ j, j < i + 1 →
      (attendHead s p tables projected i h).distances.entry j =
        ((attendHead s p tables projected i h).top -
            (attendHead s p tables projected i h).scores.entry j) /
          2 ^ p.softmaxShift := by
    intro j hj
    have inside : j < (attendHead s p tables projected i h).scores.size := by rw [sizes.1]; exact hj
    have made : (attendHead s p tables projected i h).distances =
        (attendHead s p tables projected i h).scores.map fun sj =>
          ((attendHead s p tables projected i h).top - sj) / 2 ^ p.softmaxShift := rfl
    rw [made]
    exact map_read _ _ _ inside
  have top : (attendHead s p tables projected i h).top =
      maxUpTo (fun j => (attendHead s p tables projected i h).scores.entry j) i := rfl
  have total : (attendHead s p tables projected i h).total =
      sumOver (i + 1) fun j => (attendHead s p tables projected i h).exponentials.entry j := rfl
  have weights_nonneg : ∀ j : Nat,
      (0 : Int) ≤ (attendHead s p tables projected i h).exponentials.entry j := by
    intro j
    by_cases hj : j < i + 1
    · rw [weight j hj]
      split
      · exact read_nonneg _ none_negative _
      · exact Int.le_refl 0
    · rw [entry_outside _ j (by rw [sizes.2.2]; exact hj)]
      exact Int.le_refl 0
  obtain ⟨j0, hj0, attained⟩ :=
    (maxUpTo_spec (fun j => (attendHead s p tables projected i h).scores.entry j) i).2
  have at_top : (attendHead s p tables projected i h).exponentials.entry j0 =
      tables.exponential.entry 0 := by
    have zero : (attendHead s p tables projected i h).distances.entry j0 = 0 := by
      rw [distance j0 (by omega), top, ← attained, Int.sub_self, Int.zero_ediv]
    rw [weight j0 (by omega), zero]
    simp [some_entry]
  have least : (attendHead s p tables projected i h).exponentials.entry j0 ≤
      sumOver (i + 1) fun j => (attendHead s p tables projected i h).exponentials.entry j :=
    term_le_sumOver (fun j => (attendHead s p tables projected i h).exponentials.entry j)
      weights_nonneg (i + 1) j0 (by omega)
  rw [total]
  rw [at_top] at least
  omega

/-! ## 9. A remark on condition 2 -/

/-- The lower end of condition 2 never decides for settings with `M - 14 ≤ K` and `eps ≥ 1`: a
norm's quotient is then at least -32,768. -/
theorem quotient_lower_end (bits shift : Nat) (eps : Int) (x : IntegerVector) (k : Nat) (inside : k < x.size)
    (eps_pos : 1 ≤ eps) (admitted : bits ≤ shift + 14) :
    -32768 ≤ (rmsNorm bits shift eps x).quotient.entry k := by
  have rootPos := root_positive bits shift eps x eps_pos
  have made : (rmsNorm bits shift eps x).quotient =
      x.map fun xk => roundShift (xk * (rmsNorm bits shift eps x).reciprocal) shift := rfl
  have reciprocal : (rmsNorm bits shift eps x).reciprocal =
      (2 ^ bits + (rmsNorm bits shift eps x).root / 2) / (rmsNorm bits shift eps x).root := rfl
  have root : (rmsNorm bits shift eps x).root =
      integerSquareRoot ((rmsNorm bits shift eps x).sumSquares + eps).toNat := rfl
  have term : x.entry k * x.entry k ≤ (rmsNorm bits shift eps x).sumSquares :=
    term_le_sumOver (fun k => x.entry k * x.entry k) (fun k => square_nonneg _) x.size k inside
  have spec := (isqrt_spec ((rmsNorm bits shift eps x).sumSquares + eps).toNat).2
  rw [made, map_read _ _ _ inside]
  generalize (rmsNorm bits shift eps x).reciprocal = R at reciprocal
  generalize (rmsNorm bits shift eps x).root = σ at rootPos reciprocal root
  generalize (rmsNorm bits shift eps x).sumSquares = V at root term spec
  generalize x.entry k = a at term
  -- |a| ≤ σ
  have small : -(σ + 1) < a ∧ a < σ + 1 := by
    apply bounded_of_square_lt a (σ + 1) (by omega)
    have cast : ((integerSquareRoot (V + eps).toNat + 1) * (integerSquareRoot (V + eps).toNat + 1) : Nat) =
        ((σ + 1) * (σ + 1) : Int) := by
      rw [root]; simp
    have : ((V + eps).toNat : Int) < (σ + 1) * (σ + 1) := by
      rw [← cast]; exact Int.ofNat_lt.mpr spec
    have nonneg := square_nonneg a
    omega
  have power : (0 : Int) < 2 ^ bits := Int.pow_pos (by decide)
  have product : R * σ ≤ 2 ^ bits + σ / 2 := by rw [reciprocal]; exact Int.ediv_mul_le _ (by omega)
  have Rnonneg : 0 ≤ R := by rw [reciprocal]; exact Int.ediv_nonneg (by omega) (by omega)
  -- a R ≥ -2^(M+1)
  have bound : -(2 * 2 ^ bits) ≤ a * R := by
    by_cases zero : R = 0
    · rw [zero, Int.mul_zero]; omega
    · have one : 1 ≤ R := by omega
      have : σ ≤ R * σ := by
        have := Int.mul_le_mul_of_nonneg_right one (by omega : (0 : Int) ≤ σ)
        omega
      have low : (-σ) * R ≤ a * R := Int.mul_le_mul_of_nonneg_right (by omega) Rnonneg
      have swap : (-σ) * R = -(R * σ) := by rw [Int.neg_mul, Int.mul_comm]
      omega
  have shiftPower : (0 : Int) < 2 ^ shift := Int.pow_pos (by decide)
  have half : (0 : Int) < 2 ^ (shift - 1) := Int.pow_pos (by decide)
  have powers : (2 : Int) * 2 ^ bits ≤ 32768 * 2 ^ shift := by
    have nat : 2 ^ (bits + 1) ≤ 2 ^ (shift + 15) := Nat.pow_le_pow_right (by decide) (by omega)
    have : ((2 ^ (bits + 1) : Nat) : Int) ≤ ((2 ^ (shift + 15) : Nat) : Int) := Int.ofNat_le.mpr nat
    simp only [Nat.pow_succ] at this
    push_cast at this
    omega
  unfold roundShift
  apply (Int.le_ediv_iff_mul_le shiftPower).mpr
  omega

end IntegerTransformer
