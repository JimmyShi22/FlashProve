-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import IntegerModel.Bounds.Norm

/-!
# Bounds in the feed-forward block

For one row of the stream after attention, in a dense layer or in a mixture-of-experts layer:
- `feedForward_out_within`: if the row is within a bound, the block's result is within that bound
  plus `feedForwardAdditionBound`. Of the check, only `routedInputFits` is used.
- `feedForwardOk_of_fits`: if also `normFits` and `feedForwardFits` pass, range conditions 1, 2, 5,
  6 and 7 hold at this row.

The router's choice depends on the prompt. The proofs use of it only that it is an index below the
number of experts (`chosen_index`, IntegerModel/Readable/Reads.lean). Only Lean's core library is
used.
-/

namespace IntegerTransformer.Bounds

/-- If `|a| ≤ A` and `|b| ≤ B`, then `|a b| ≤ A B`. -/
theorem magnitude_mul_le_mul (a b A B : Int) (ha : magnitude a ≤ A) (hb : magnitude b ≤ B) :
    magnitude (a * b) ≤ A * B := by
  rw [magnitude_mul]
  exact Int.mul_le_mul ha hb (magnitude_nonneg b) (Int.le_trans (magnitude_nonneg a) ha)

/-- A test that holds of every read inside a vector holds of all its entries. -/
theorem all_of_entries (v : IntegerVector) (test : Int → Bool)
    (h : ∀ k, k < v.size → test (v.entry k) = true) : v.all test = true := by
  rw [Array.all_eq_true]
  intro k inside
  have := h k inside
  rwa [entry_inside v k inside] at this

/-- A product with an input in the box, shifted. -/
theorem shifted_product_le (z : IntegerVector) (W : Matrix) (outputs shift width j : Nat)
    (size : z.size = width) (box : InBox z) (inside : j < outputs) :
    magnitude (((product z W outputs).map fun e => roundShift e shift).entry j) ≤
      roundShift (boxColumnBound W width j) shift := by
  rw [map_read _ _ _ (by rw [size_product]; exact inside)]
  apply magnitude_roundShift_le
  have := magnitude_product_entry_le z W outputs j inside (fun _ => activationBound)
    (fun k _ => box k)
  rw [size] at this
  exact this

/-- The sum of a row within `boundX` and a vector within `boundY` is within the sum of the two
bounds. -/
theorem addVec_within (x y : IntegerVector) (boundX boundY : Nat → Int) (hx : RowWithin boundX x)
    (hy : ∀ k, k < x.size → magnitude (y.entry k) ≤ boundY k) :
    RowWithin (fun k => boundX k + boundY k) (addVectors x y) := by
  intro k inside
  rw [size_addVec] at inside
  unfold addVectors
  rw [tabulate_read _ _ _ inside]
  have := magnitude_add_le (x.entry k) (y.entry k)
  have := hx k inside
  have := hy k inside
  show magnitude _ ≤ boundX k + boundY k
  omega

/-- Conditions 6 and 7 hold of a gated block that reads a vector in the box, if `unitsFit` passes.
-/
theorem hiddenUnits_fit (tables : Tables) (w : GatedWeights) (width hidden gateShift upShift : Nat)
    (z : IntegerVector) (size : z.size = width) (box : InBox z)
    (fits : unitsFit w width hidden gateShift upShift = true) :
    unitsOk (hiddenUnits tables w hidden gateShift upShift z) = true := by
  rw [unitsFit, allBelow_spec] at fits
  have sizes := size_hiddenUnits tables w hidden gateShift upShift z
  simp only [unitsOk, Bool.and_eq_true]
  constructor
  · apply all_of_entries
    intro j inside
    rw [sizes.2.2.1] at inside
    have fit := fits j inside
    simp only [Bool.and_eq_true, decide_eq_true_eq] at fit
    have gate := shifted_product_le z w.gate hidden gateShift width j size box inside
    have made : (hiddenUnits tables w hidden gateShift upShift z).highPart.entry j =
        ((((product z w.gate hidden).map fun e => roundShift e gateShift).entry j) -
          balancedLowByte (((product z w.gate hidden).map fun e => roundShift e gateShift).entry j))
            / 256 := by
      simp only [hiddenUnits, tabulate_read, map_read, size_product, Array.size_map, inside]
    rw [made]
    generalize ((product z w.gate hidden).map fun e => roundShift e gateShift).entry j = g at gate
    rw [magnitude_le_iff] at gate
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    unfold balancedLowByte
    omega
  · apply fits16_of_bounded _ 32767 _ (Int.le_refl _)
    intro j inside
    rw [sizes.2.2.2.2.2.2] at inside
    have fit := fits j inside
    simp only [Bool.and_eq_true, decide_eq_true_eq] at fit
    exact Int.le_trans (shifted_product_le z w.up hidden upShift width j size box inside) fit.2

/-- A block's down projection, before the shift, is at most `downBound` in absolute value, if the
block reads a vector in the box. -/
theorem downSum_le (tables : Tables) (w : GatedWeights) (width hidden gateShift upShift : Nat)
    (z : IntegerVector) (size : z.size = width) (box : InBox z) (k : Nat) :
    magnitude (downSum (hiddenUnits tables w hidden gateShift upShift z) w.down k) ≤
      downBound tables w width hidden upShift k := by
  have sizes := size_hiddenUnits tables w hidden gateShift upShift z
  unfold downSum downBound columnBound
  rw [sizes.2.2.2.2.2.2]
  apply magnitude_sumOver_le
  intro j inside
  apply magnitude_mul_le
  apply magnitude_mul_le_mul
  · have made : (hiddenUnits tables w hidden gateShift upShift z).activation =
        (hiddenUnits tables w hidden gateShift upShift z).key.map tables.silu.read := rfl
    rw [made, map_read _ _ _ (by rw [sizes.2.2.2.2.1]; exact inside)]
    exact magnitude_read_le _ _
  · exact shifted_product_le z w.up hidden upShift width j size box inside

/-- A routed expert's input is in the box, if the normed row is and `routedInputFits` passes. -/
theorem routedExpert_input_inBox (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (m : IntegerVector) (box : InBox m) (fits : routedInputFits tables = true) :
    InBox (routedExpert s p tables w m).input := by
  intro k
  have made : (routedExpert s p tables w m).input =
      m.map fun mk => roundShift ((routedExpert s p tables w m).scale * mk) 16 := rfl
  simp only [routedInputFits, decide_eq_true_eq] at fits
  by_cases inside : k < m.size
  · rw [made, map_read _ _ _ inside]
    apply Int.le_trans _ fits
    apply magnitude_roundShift_le
    apply magnitude_mul_le_mul
    · exact magnitude_read_le _ _
    · exact box k
  · rw [entry_outside _ k (by rw [made, Array.size_map]; exact inside)]; decide

/-- Condition 5 holds, if the router reads a vector in the box and every expert's bound fits. -/
theorem routedExpert_high_fits (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (m : IntegerVector) (size : m.size = s.width) (box : InBox m)
    (fits : ∀ e, e < s.experts →
      roundShift (boxColumnBound w.router s.width e) p.routerShift ≤ 262143) :
    fits16 (routedExpert s p tables w m).high = true := by
  have sizes := size_routedExpert s p tables w m
  unfold fits16
  apply all_of_entries
  intro e inside
  rw [sizes.2.1] at inside
  have wide := shifted_product_le m w.router s.experts p.routerShift s.width e size box inside
  have made : (routedExpert s p tables w m).high.entry e =
      (((product m w.router s.experts).map fun e => roundShift e p.routerShift).entry e) / 8 := by
    simp only [routedExpert, map_read, size_product, Array.size_map, inside]
  rw [made]
  have fit := fits e inside
  generalize ((product m w.router s.experts).map fun e => roundShift e p.routerShift).entry e = lw
    at wide
  rw [magnitude_le_iff] at wide
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- What the feed-forward block adds to the stream is at most `feedForwardAdditionBound`, entry by
entry. The chosen expert's bound is at most the largest over all experts. -/
theorem feedForward_addition_le (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (mixture : Bool) (x : IntegerVector) (some_expert : mixture = true → 0 < s.experts)
    (size : x.size = s.width) (routedFit : routedInputFits tables = true) (k : Nat)
    (hk : k < s.width) :
    magnitude ((feedForward s p tables w mixture x).addition.entry k) ≤
      feedForwardAdditionBound s p tables w mixture k := by
  have box := norm_out_inBox p.feedForwardBits p.feedForwardShift p.feedForwardEps x
  have normed : (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out.size =
      s.width := by rw [(size_rmsNorm _ _ _ _).2, size]
  cases mixture with
  | false =>
    simp only [feedForward, feedForwardAdditionBound, Bool.false_eq_true, if_false, tabulate_read,
      hk]
    apply magnitude_roundShift_le
    exact downSum_le tables w.shared s.width s.hidden p.gateShift p.upShift _ normed box k
  | true =>
    simp only [feedForward, feedForwardAdditionBound, if_true, tabulate_read, hk]
    apply magnitude_roundShift_le
    apply Int.le_trans (magnitude_add_le _ _)
    apply Int.add_le_add
    · exact downSum_le tables w.shared s.width s.expertHidden p.gateShift p.upShift _ normed box k
    · have chosen := chosen_index s p tables w
        (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out (some_expert rfl)
      have inputBox := routedExpert_input_inBox s p tables w _ box routedFit
      have inputSize : (routedExpert s p tables w
          (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out).input.size =
          s.width := by rw [(size_routedExpert _ _ _ _ _).2.2.2.2, normed]
      apply Int.le_trans (downSum_le tables (w.routed.entry _) s.width s.expertHidden
        p.routedGateShift p.routedUpShift _ inputSize inputBox k)
      exact (maxUpTo_spec (fun e => downBound tables (w.routed.entry e) s.width s.expertHidden
        p.routedUpShift k) (s.experts - 1)).1 (routedExpert s p tables w
          (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out).chosen (by omega)

/-- The block's result is its input plus its addition. -/
theorem feedForward_out (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (mixture : Bool) (x : IntegerVector) :
    (feedForward s p tables w mixture x).out =
      addVectors x (feedForward s p tables w mixture x).addition := by
  cases mixture <;> rfl

/-- The stream after the feed-forward block. No part of the check but `routedInputFits` is used. -/
theorem feedForward_out_within (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (mixture : Bool) (x : IntegerVector) (bound : Nat → Int)
    (some_expert : mixture = true → 0 < s.experts) (size : x.size = s.width)
    (within : RowWithin bound x) (routedFit : routedInputFits tables = true) :
    RowWithin (fun k => bound k + feedForwardAdditionBound s p tables w mixture k)
      (feedForward s p tables w mixture x).out := by
  rw [feedForward_out]
  apply addVec_within x _ bound _ within
  intro k inside
  exact feedForward_addition_le s p tables w mixture x some_expert size routedFit k
    (by rw [← size]; exact inside)

/-- Conditions 1, 2, 5, 6, 7 at one position of one layer. -/
theorem feedForwardOk_of_fits (s : Settings) (p : LayerSettings) (tables : Tables)
    (w : LayerWeights) (mixture : Bool) (x : IntegerVector) (bound : Nat → Int)
    (some_expert : mixture = true → 0 < s.experts) (eps_pos : 1 ≤ p.feedForwardEps)
    (size : x.size = s.width) (within : RowWithin bound x)
    (routedFit : routedInputFits tables = true)
    (normFit : normFits p.feedForwardBits p.feedForwardShift p.feedForwardEps s.width bound = true)
    (fits : feedForwardFits s p w mixture = true) :
    feedForwardOk p (feedForward s p tables w mixture x) = true := by
  have box := norm_out_inBox p.feedForwardBits p.feedForwardShift p.feedForwardEps x
  have normed : (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out.size =
      s.width := by rw [(size_rmsNorm _ _ _ _).2, size]
  have norm := normOk_of_normFits p.feedForwardBits p.feedForwardShift p.feedForwardEps x bound
    eps_pos within (by rw [size]; exact normFit)
  cases mixture with
  | false =>
    simp only [feedForwardFits, Bool.false_eq_true, if_false] at fits
    simp only [feedForwardOk, feedForward, Bool.false_eq_true, if_false, Bool.and_eq_true]
    exact ⟨⟨⟨norm, hiddenUnits_fit tables w.shared s.width s.hidden p.gateShift p.upShift _ normed
      box fits⟩, by simp [noRoute, fits16]⟩, by simp [noRoute, unitsOk, fits16]⟩
  | true =>
    simp only [feedForwardFits, if_true, Bool.and_eq_true, allBelow_spec, decide_eq_true_eq] at fits
    simp only [feedForwardOk, feedForward, if_true, Bool.and_eq_true]
    have chosen := chosen_index s p tables w
      (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out (some_expert rfl)
    have inputBox := routedExpert_input_inBox s p tables w _ box routedFit
    have inputSize : (routedExpert s p tables w
        (rmsNorm p.feedForwardBits p.feedForwardShift p.feedForwardEps x).out).input.size =
        s.width := by rw [(size_routedExpert _ _ _ _ _).2.2.2.2, normed]
    exact ⟨⟨⟨norm, hiddenUnits_fit tables w.shared s.width s.expertHidden p.gateShift p.upShift _
      normed box fits.1⟩,
      routedExpert_high_fits s p tables w _ normed box fun e he => (fits.2 e he).1⟩,
      hiddenUnits_fit tables (w.routed.entry _) s.width s.expertHidden p.routedGateShift
        p.routedUpShift _ inputSize inputBox (fits.2 _ chosen).2⟩

end IntegerTransformer.Bounds
