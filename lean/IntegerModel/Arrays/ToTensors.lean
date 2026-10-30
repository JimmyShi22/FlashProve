-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Arrays/ToTensors.lean: from settings and weights as arrays
(`IntegerTransformer.Settings`, `.Weights`, IntegerModel/Model.lean) back to the library's tables of
parameters (`ScalesAndPolicy`, Inst/Model/ProgTests.lean) and weight tensors (`Weights`,
Inst/Model/Program.lean).
`ppBack`, `lawful_ppBack`: a lawful (`Lawful`, Inst/Model/Scales.lean) table of parameters for all
valid settings.
`settings_back`: its settings are the given ones.
`wf_weightsTo`, `weights_back`: the tensors of valid weights at valid settings are well formed
(`Weights.WF`, Inst/Model/Program.lean), and their arrays are the given ones. So, with
`settingsAreValid_arrays` and `weightsAreValid_arrays` (IntegerModel/Arrays/OfTensors.lean), the two
tests (`settingsAreValid`, `weightsAreValid`, VerifiableInference/ModelWeights.lean) are exact (an
argument; no theorem of this file states it): they pass exactly, at the sizes `ppref`, the settings
of lawful tables and, at valid settings, the arrays of well-formed tensors.
`settingsArraysOf` writes 0 for the router's shift and the routed expert's two shifts of each dense
layer, which the model does not read; `ppBack` sets them to 17, 16, 20, which lie in the ranges that
a lawful table requires.
`layerTo`, `weightsTo`: from IntegerModel/Readable/AnyInput.lean. All declarations of this file are
in `VerifiableInference.Back`.
-/
import IntegerModel.Arrays.OfTensors
import IntegerModel.Readable.AnyInput

set_option autoImplicit false

/- No default table of scales here: `Scl.ref` (Inst/Model/Scl.lean) is off; each `Scl` is named. -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference

open Inst.Model IntegerModel.Readable IntegerModel.Runnable

namespace Back

/-! ## 1. Arrays -/

theorem andL {a b : Bool} (h : (a && b) = true) : a = true := by
  rw [Bool.and_eq_true] at h
  exact h.1

theorem andR {a b : Bool} (h : (a && b) = true) : b = true := by
  rw [Bool.and_eq_true] at h
  exact h.2

/-- An array of size n is the table of its n entries. -/
theorem array_eq {α : Type} [Inhabited α] (v : Array α) {n : ℕ} (h : v.size = n) : v = tabl n fun j
    => v.entry j := by
  apply Array.ext
  · simp [tabl, h]
  · intro i h1 _
    simp [tabl, Array.entry, Array.getD, h1]

theorem empty_of_size {α : Type} (v : Array α) (h : v.size = 0) : v = #[] := by
  apply Array.ext
  · simp [h]
  · intro i h1 _
    omega

/-- Outside the array an entry is the default value. -/
theorem entry_out {α : Type} [Inhabited α] (v : Array α) {k : ℕ} (h : v.size ≤ k) : v.entry k =
    default := by
  simp [Array.entry, Array.getD, Nat.not_lt.2 h]

theorem entry_empty (x : ℕ) : ((default : Array ℤ)).entry x = 0 :=
  entry_out (default : Array ℤ) (Nat.zero_le x)

theorem hasSize_size {r c : ℕ} {M : Array (Array ℤ)} (h : IntegerTransformer.hasSize r c M = true) :
    M.size = r :=
  beq_iff_eq.1 (andL h)

/-- A matrix of the stated size is the table of its entries. -/
theorem mat_entries {r c : ℕ} {M : Array (Array ℤ)} (h : IntegerTransformer.hasSize r c M = true) :
    mat r c (fun j x => (M.entry j).entry x) = M := by
  unfold mat
  refine (tabl_congr fun j hj => ?_).trans (array_eq M (hasSize_size h)).symm
  exact (row_eq (M.entry j) (hasSize_row h hj)).symm

/-- Outside its size the entries of a matrix are 0. -/
theorem entries_out {r c : ℕ} {M : Array (Array ℤ)} (h : IntegerTransformer.hasSize r c M = true)
    {j x : ℕ} (ho : ¬ (j < r ∧ x < c)) : (M.entry j).entry x = 0 := by
  by_cases hj : j < r
  · have hx : c ≤ x := by
      by_contra hc
      exact ho ⟨hj, by omega⟩
    exact entry_out (M.entry j) (by rw [hasSize_row h hj]; exact hx)
  · rw [entry_out M (by rw [hasSize_size h]; omega)]
    exact entry_empty x

theorem entries_in {r c : ℕ} {low high : ℤ} {M : Array (Array ℤ)}
    (h : IntegerTransformer.hasSize r c M = true) (hw : entriesWithin low high M = true) {j x : ℕ}
    (hj : j < r) (hx : x < c) :
    low ≤ (M.entry j).entry x ∧ (M.entry j).entry x ≤ high := by
  unfold entriesWithin at hw
  have h1 := Array.all_eq_true_iff_forall_mem.1 hw (M.entry j)
      (entry_mem M (by rw [hasSize_size h]; exact hj))
  have h2 := Array.all_eq_true_iff_forall_mem.1 h1 ((M.entry j).entry x)
      (entry_mem (M.entry j) (by rw [hasSize_row h hj]; exact hx))
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h2
  exact h2

theorem box_entries {r c : ℕ} {low high : ℤ} {M : Array (Array ℤ)}
    (h : IntegerTransformer.hasSize r c M = true) (hw : entriesWithin low high M = true) :
    Box r c low high (fun j x => (M.entry j).entry x) := by
  intro j x
  by_cases hi : j < r ∧ x < c
  · rw [if_pos hi]
    exact entries_in h hw hi.1 hi.2
  · rw [if_neg hi]
    exact entries_out h hi

theorem two_entries {r c : ℕ} {M : Array (Array ℤ)} (h : IntegerTransformer.hasSize r c M = true)
    (hw : entriesWithin (-4096) 4095 M = true) :
    Two r c (fun j x => (M.entry j).entry x) := by
  have e1 : (-2 ^ 12 : ℤ) = -4096 := by norm_num
  have e2 : (2 ^ 12 - 1 : ℤ) = 4095 := by norm_num
  unfold Two
  rw [e1, e2]
  exact box_entries h hw

theorem two_zero {W : Mat} (h : ∀ j x, W j x = 0) : Two 0 0 W := by
  intro j x
  rw [if_neg (by omega)]
  exact h j x

/-- The entries of an empty matrix are 0. -/
theorem entries_empty {M : Array (Array ℤ)} (h : M.size = 0) (j x : ℕ) : (M.entry j).entry x = 0 :=
    by
  rw [entry_out M (by omega)]
  exact entry_empty x

theorem gated_entries {d h : ℕ} {g : IntegerTransformer.GatedWeights} (hg : g.hasSizes d h = true) :
    gatedOf d h (fun j c => (g.gate.entry j).entry c) (fun j c => (g.up.entry j).entry c)
        (fun j c => (g.down.entry j).entry c) = g := by
  unfold IntegerTransformer.GatedWeights.hasSizes at hg
  unfold gatedOf
  rw [mat_entries (andL (andL hg)), mat_entries (andR (andL hg)), mat_entries (andR hg)]

/-! ## 2. One layer's weights -/

/-- What `weightsAreValid` gives at valid settings for the weights of one layer
(`valid_layerFits`). -/
structure LayerFits (P : Params) (L : ℕ) (W : IntegerTransformer.LayerWeights) : Prop where
  query : IntegerTransformer.hasSize P.d (P.nq * P.ch) W.query = true ∧ entriesWithin (-4096) 4095
      W.query = true
  key : IntegerTransformer.hasSize P.d (P.nkv * P.ch) W.key = true ∧ entriesWithin (-4096) 4095
      W.key = true
  value : IntegerTransformer.hasSize P.d (P.nkv * P.ch) W.value = true ∧ entriesWithin (-4096) 4095
      W.value = true
  output : IntegerTransformer.hasSize (P.nq * P.ch) P.d W.output = true ∧ entriesWithin (-4096) 4095
      W.output = true
  shared : W.shared.hasSizes P.d (if hasExperts L then P.fe else P.f) = true ∧ gatedWithin W.shared
      = true
  mixture : hasExperts L → (IntegerTransformer.hasSize P.d P.nexp W.router = true ∧ entriesWithin
      (-4096) 4095 W.router = true) ∧ W.routed.size = P.nexp ∧
    ∀ e < P.nexp, (W.routed.entry e).hasSizes P.d P.fe = true ∧ gatedWithin (W.routed.entry e) =
        true
  dense : ¬ hasExperts L → W.router.size = 0 ∧ W.routed.size = 0

theorem layerArrays_layerTo {P : Params} {L : ℕ} {W : IntegerTransformer.LayerWeights}
    (h : LayerFits P L W) : layerArrays P (layerTo W) L = W := by
  have hq : mat P.d (P.nq * P.ch) (layerTo W).Wq = W.query := mat_entries h.query.1
  have hk : mat P.d (P.nkv * P.ch) (layerTo W).Wk = W.key := mat_entries h.key.1
  have hv : mat P.d (P.nkv * P.ch) (layerTo W).Wv = W.value := mat_entries h.value.1
  have ho : mat (P.nq * P.ch) P.d (layerTo W).Wo = W.output := mat_entries h.output.1
  have hs : gatedOf P.d (if hasExperts L then P.fe else P.f) (layerTo W).Wg (layerTo W).Wu
      (layerTo W).Wd = W.shared := gated_entries h.shared.1
  unfold layerArrays
  by_cases hE : hasExperts L
  · obtain ⟨⟨hr, -⟩, hn, he⟩ := h.mixture hE
    have hr' : mat P.d P.nexp (layerTo W).Wr = W.router := mat_entries hr
    have ht : (tabl P.nexp fun e => gatedOf P.d P.fe ((layerTo W).Eg e) ((layerTo W).Eu e)
        ((layerTo W).Ed e)) = W.routed :=
      (tabl_congr fun e hlt => gated_entries (he e hlt).1).trans (array_eq W.routed hn).symm
    rw [if_pos hE]
    unfold layerWeightsOf
    rw [hq, hk, hv, ho, hs, hr', ht]
  · obtain ⟨hr, hn⟩ := h.dense hE
    rw [if_neg hE]
    unfold layerWeightsOf
    rw [hq, hk, hv, ho, hs, ← empty_of_size W.router hr, ← empty_of_size W.routed hn]

theorem gated_two {d h : ℕ} {g : IntegerTransformer.GatedWeights} (hg : g.hasSizes d h = true)
    (hw : gatedWithin g = true) :
    Two d h (fun j c => (g.gate.entry j).entry c) ∧ Two d h (fun j c => (g.up.entry j).entry c) ∧
        Two h d (fun j c => (g.down.entry j).entry c) := by
  unfold IntegerTransformer.GatedWeights.hasSizes at hg
  unfold gatedWithin at hw
  exact ⟨two_entries (andL (andL hg)) (andL (andL hw)), two_entries (andR (andL hg))
      (andR (andL hw)), two_entries (andR hg) (andR hw)⟩

/-- The three matrices of a missing expert are 0. -/
theorem gated_out {v : Array IntegerTransformer.GatedWeights} {e : ℕ} (h : v.size ≤ e) :
    Two 0 0 (fun j c => ((v.entry e).gate.entry j).entry c) ∧ Two 0 0
        (fun j c => ((v.entry e).up.entry j).entry c) ∧ Two 0 0
        (fun j c => ((v.entry e).down.entry j).entry c) := by
  rw [entry_out v h]
  exact ⟨two_zero fun j x => entries_empty (M := (default : IntegerTransformer.GatedWeights).gate)
      rfl j x, two_zero fun j x => entries_empty (M := (default :
      IntegerTransformer.GatedWeights).up) rfl j x,
    two_zero fun j x => entries_empty (M := (default : IntegerTransformer.GatedWeights).down) rfl j
        x⟩

theorem wf_layerTo {P : Params} {L : ℕ} {W : IntegerTransformer.LayerWeights} (h : LayerFits P L W)
    : (layerTo W).WF P L := by
  refine ⟨two_entries h.query.1 h.query.2, two_entries h.key.1 h.key.2, two_entries h.value.1
      h.value.2, two_entries h.output.1 h.output.2, ?_⟩
  have hs := h.shared
  by_cases hE : hasExperts L
  · obtain ⟨⟨hr, hrw⟩, hn, he⟩ := h.mixture hE
    rw [if_pos hE] at hs
    rw [if_pos hE]
    obtain ⟨g1, g2, g3⟩ := gated_two hs.1 hs.2
    refine ⟨g1, g2, g3, two_entries hr hrw, fun e => ?_⟩
    by_cases hlt : e < P.nexp
    · rw [if_pos hlt]
      exact gated_two (he e hlt).1 (he e hlt).2
    · rw [if_neg hlt]
      exact gated_out (by omega)
  · obtain ⟨hr, hn⟩ := h.dense hE
    rw [if_neg hE] at hs
    rw [if_neg hE]
    obtain ⟨g1, g2, g3⟩ := gated_two hs.1 hs.2
    exact ⟨g1, g2, g3, two_zero fun j x => entries_empty hr j x, fun e => gated_out (by omega)⟩

theorem isZero_default : (layerTo (default : IntegerTransformer.LayerWeights)).IsZero :=
  ⟨two_zero fun j x => entries_empty (M := (default : IntegerTransformer.LayerWeights).query) rfl j
      x, two_zero fun j x => entries_empty (M := (default : IntegerTransformer.LayerWeights).key)
      rfl j x,
   two_zero fun j x => entries_empty (M := (default : IntegerTransformer.LayerWeights).value) rfl j
       x, two_zero fun j x => entries_empty (M := (default :
       IntegerTransformer.LayerWeights).output) rfl j x,
   two_zero fun j x => entries_empty (M := (default : IntegerTransformer.LayerWeights).shared.gate)
       rfl j x, two_zero fun j x => entries_empty (M := (default :
       IntegerTransformer.LayerWeights).shared.up) rfl j x,
   two_zero fun j x => entries_empty (M := (default : IntegerTransformer.LayerWeights).shared.down)
       rfl j x, two_zero fun j x => entries_empty (M := (default :
       IntegerTransformer.LayerWeights).router) rfl j x,
   fun e => gated_out (v := (default : IntegerTransformer.LayerWeights).routed) (Nat.zero_le e)⟩

/-! ## 3. One layer's parameters -/

/-- The numbers of one layer in a table (`Words`, Inst/Model/ProgTests.lean). In a dense layer the
router's shift and the routed expert's two shifts, which the model does not read, are 17, 16, 20. -/
def wordsBack (p : IntegerTransformer.LayerSettings) (L : ℕ) : Words where
  kq := p.queryShift
  kk := p.keyShift
  kv := p.valueShift
  ko := p.outputShift
  kg := p.gateShift
  ku := p.upShift
  kd := p.downShift
  kr := if L % 2 = 1 then p.routerShift else 17
  kg' := if L % 2 = 1 then p.routedGateShift else 16
  ku' := if L % 2 = 1 then p.routedUpShift else 20
  n1 := ⟨p.attentionBits, p.attentionShift, p.attentionEps⟩
  n2 := ⟨p.feedForwardBits, p.feedForwardShift, p.feedForwardEps⟩
  sh := p.softmaxShift

theorem norm_back {bits shift : ℕ} {eps : ℤ} (h : normInRange bits shift eps = true) :
    (⟨bits, shift, eps⟩ : NormPar).OK ∧ shift ≤ bits := by
  simp only [normInRange, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold NormPar.OK
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> (try dsimp only) <;> omega

/-- What `layerSettingsInRange mixture` gives for the parameters of layer L, if `mixture` is true
exactly at odd L. -/
theorem ranges_back {p : IntegerTransformer.LayerSettings} {L : ℕ} {mixture : Bool}
    (hm : mixture = true ↔ L % 2 = 1) (h : layerSettingsInRange mixture p = true) :
    FFSeg.Ranges (wordsBack p L).scale ∧ (4 ≤ p.softmaxShift ∧ p.softmaxShift ≤ 12) ∧
        p.attentionShift ≤ p.attentionBits ∧ p.feedForwardShift ≤ p.feedForwardBits ∧
      (L % 2 ≠ 1 → p.routerShift = 0 ∧ p.routedGateShift = 0 ∧ p.routedUpShift = 0) := by
  unfold layerSettingsInRange at h
  have hlast := andR h
  have hn2 := norm_back (andR (andL h))
  have hn1 := norm_back (andR (andL (andL h)))
  have hrest := andL (andL (andL h))
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hrest
  by_cases hL : L % 2 = 1
  · rw [hm.2 hL, if_pos rfl] at hlast
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hlast
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hn1.1, hn2.1⟩, ?_, hn1.2, hn2.2, fun hc =>
        absurd hL hc⟩ <;> (try simp only [wordsBack, Words.scale, if_pos hL]) <;> omega
  · have hf : mixture = false := Bool.eq_false_iff.2 fun a => hL (hm.1 a)
    rw [hf, if_neg (by simp)] at hlast
    simp only [Bool.and_eq_true, beq_iff_eq] at hlast
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hn1.1, hn2.1⟩, ?_, hn1.2, hn2.2, fun _ =>
        ⟨hlast.1.1, hlast.1.2, hlast.2⟩⟩ <;> (try simp only [wordsBack, Words.scale, if_neg hL]) <;>
        omega

/-- The parameters of one layer, to `Words` and back. -/
theorem layerScales_back {p : IntegerTransformer.LayerSettings} {L : ℕ}
    (hr : p.rotary = decide (¬ rotaryOff L))
    (hd : L % 2 ≠ 1 → p.routerShift = 0 ∧ p.routedGateShift = 0 ∧ p.routedUpShift = 0) : layerScales
        (wordsBack p L).scale L = p := by
  unfold layerScales
  by_cases hE : hasExperts L
  · have hL : L % 2 = 1 := hE
    rw [if_pos hE]
    simp only [layerSettingsOf, wordsBack, Words.scale, if_pos hL]
    rw [← hr]
  · have hL : L % 2 ≠ 1 := hE
    obtain ⟨h1, h2, h3⟩ := hd hL
    have e : p = { p with routerShift := 0, routedGateShift := 0, routedUpShift := 0 } := by
      cases p
      dsimp only at h1 h2 h3
      subst h1 h2 h3
      rfl
    rw [if_neg hE]
    simp only [layerSettingsOf, wordsBack, Words.scale]
    rw [← hr]
    exact e.symm

/-! ## 4. All parameters -/

theorem settings_eta (s : IntegerTransformer.Settings) (h1 : s.positions = 1024)
    (h2 : s.layers = 48) (h3 : s.width = 5120) (h4 : s.queryHeads = 40) (h5 : s.keyValueHeads = 8)
    (h6 : s.headDim = 128)
    (h7 : s.hidden = 16384) (h8 : s.expertHidden = 8192) (h9 : s.experts = 128)
        (h10 : s.vocabulary = 202048) (h11 : s.rotaryScale = 12) :
    ({ positions := 1024, layers := 48, width := 5120, queryHeads := 40, keyValueHeads := 8,
       headDim := 128, hidden := 16384, expertHidden := 8192, experts := 128, vocabulary := 202048,
       rotaryScale := 12,
       finalEps := s.finalEps, finalBits := s.finalBits, finalShift := s.finalShift,
       perLayer := s.perLayer } : IntegerTransformer.Settings) = s := by
  cases s
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  rfl

/-- The library's table of parameters. A table also has an acceptance policy, which the model
does not read: it is set to exact match. -/
def ppBack (settings : IntegerTransformer.Settings) : ScalesAndPolicy :=
  ⟨fun L => wordsBack (settings.perLayer.entry L.val) L.val,
      ⟨settings.finalBits, settings.finalShift, settings.finalEps⟩, AcceptancePolicy.exact⟩

/-- The three numbers of exact match are in the ranges that a lawful table requires. -/
theorem exact_inRange : AcceptancePolicy.exact.C < 2 ^ 32 ∧ AcceptancePolicy.exact.theta ≤ AcceptancePolicy.exact.C ∧
    AcceptancePolicy.exact.cap ≤ 1024 := by decide

theorem kap_ppBack (settings : IntegerTransformer.Settings) {L : ℕ} (h : L < 48) :
    (ppBack settings).kap L = (wordsBack (settings.perLayer.entry L) L).scale :=
  kap_lt (ppBack settings) h

section ValidSettings
variable {settings : IntegerTransformer.Settings} (hs : settingsAreValid settings = true)
include hs

theorem valid_sizes : hasModelSizes settings = true := by
  unfold settingsAreValid at hs
  exact andL (andL hs)

theorem valid_ranges : settingsInRange settings = true := by
  unfold settingsAreValid at hs
  exact andR (andL hs)

/-- The eleven sizes. -/
theorem valid_numbers : settings.positions = 1024 ∧ settings.layers = 48 ∧ settings.width = 5120 ∧
    settings.queryHeads = 40 ∧ settings.keyValueHeads = 8 ∧ settings.headDim = 128 ∧
    settings.hidden = 16384 ∧ settings.expertHidden = 8192 ∧ settings.experts = 128 ∧
    settings.vocabulary = 202048 ∧ settings.rotaryScale = 12 := by
  have h := andL (valid_sizes hs)
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem valid_size : settings.perLayer.size = 48 := by
  have e := (valid_numbers hs).2.1
  unfold settingsAreValid at hs
  exact (beq_iff_eq.1 (andR hs)).trans e

theorem valid_rotary {L : ℕ} (hL : L < 48) : (settings.perLayer.entry L).rotary = decide
    (¬ rotaryOff L) := by
  have h := List.all_eq_true.1 (andR (valid_sizes hs)) L (List.mem_range.2 hL)
  rw [beq_iff_eq] at h
  rw [h]
  unfold rotaryOff
  by_cases h3 : L % 4 = 3 <;> simp [h3]

theorem valid_mixture (L : ℕ) : settings.isMixture L = true ↔ L % 2 = 1 := by
  unfold IntegerTransformer.Settings.isMixture
  rw [(valid_numbers hs).2.2.2.2.2.2.2.2.1]
  simp

theorem valid_layer {L : ℕ} (hL : L < 48) : layerSettingsInRange (settings.isMixture L)
    (settings.perLayer.entry L) = true ∧
    (settings.perLayer.entry L).softmaxShift = (settings.perLayer.entry
        (4 * (L / 4))).softmaxShift := by
  have h := List.all_eq_true.1 (andR (valid_ranges hs)) L (List.mem_range.2 hL)
  exact ⟨andL h, beq_iff_eq.1 (andR h)⟩

theorem lawful_ppBack : Lawful (ppBack settings) := by
  have hf := norm_back (andL (valid_ranges hs))
  have hl : ∀ L : Fin 48, _ := fun L => ranges_back (valid_mixture hs L.val)
      (valid_layer hs L.isLt).1
  refine ⟨⟨fun L => (hl L).1, fun L => (hl L).2.1, fun g l => ?_, hf.1, exact_inRange⟩,
      ⟨fun L => ⟨(hl L).2.2.1, (hl L).2.2.2.1⟩, hf.2⟩⟩
  have h1 : 4 * g.val + l.val < 48 := by omega
  have h2 : 4 * g.val < 48 := by omega
  rw [kap_ppBack settings h1, kap_ppBack settings h2]
  have e := (valid_layer hs h1).2
  rw [show 4 * ((4 * g.val + l.val) / 4) = 4 * g.val by omega] at e
  exact e

theorem settings_back : settingsArraysOf ppref (ppBack settings) = settings := by
  have hp : (tabl ppref.layers fun L => layerScales ((ppBack settings).kap L) L) =
      settings.perLayer := by
    refine (tabl_congr fun L hL => ?_).trans (array_eq settings.perLayer
        (valid_size hs)).symm
    have hL' : L < 48 := hL
    rw [kap_ppBack settings hL']
    exact layerScales_back (valid_rotary hs hL') (ranges_back (valid_mixture hs L)
        (valid_layer hs hL').1).2.2.2.2
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := valid_numbers hs
  unfold settingsArraysOf settingsArrays
  rw [hp]
  exact settings_eta settings h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

end ValidSettings

/-! ## 5. All weights -/

section ValidWeights
variable {settings : IntegerTransformer.Settings} {weights : IntegerTransformer.Weights}

theorem valid_wellFormed (hw : weightsAreValid settings weights = true) :
    IntegerTransformer.wellFormed settings lookupTables weights = true := by
  unfold weightsAreValid at hw
  exact andL hw

theorem valid_weights (hw : weightsAreValid settings weights = true) :
    weightsInRange settings weights = true := by
  unfold weightsAreValid at hw
  exact andR hw

variable (hs : settingsAreValid settings = true) (hw : weightsAreValid settings weights = true)
include hs hw

theorem valid_perLayer : weights.perLayer.size = 48 := by
  have h := valid_wellFormed hw
  unfold IntegerTransformer.wellFormed at h
  exact (beq_iff_eq.1 (andR (andL h))).trans (valid_numbers hs).2.1

theorem valid_layerFits {L : ℕ} (hL : L < 48) : LayerFits ppref L (weights.perLayer.entry L)
    := by
  obtain ⟨-, h2, h3, h4, h5, h6, h7, h8, h9, -, -⟩ := valid_numbers hs
  have hwf := valid_wellFormed hw
  unfold IntegerTransformer.wellFormed at hwf
  have hl := List.all_eq_true.1 (andR hwf) L (List.mem_range.2 (by rw [h2]; exact hL))
  have hr := List.all_eq_true.1 (andR (valid_weights hw)) L (List.mem_range.2 hL)
  unfold IntegerTransformer.layerWellFormed IntegerTransformer.Settings.queryWidth
      IntegerTransformer.Settings.keyValueWidth at hl
  unfold layerWeightsInRange at hr
  rw [h3, h4, h5, h6, h7, h8, h9] at hl
  have hlast := andR hl
  have hfront := andL (andL (andL (andL (andL (andL (andL
      (andL (andL (andL (andL (andL hl)))))))))))
  have hrlast := andR hr
  have hE : hasExperts L ↔ settings.isMixture L = true := (valid_mixture hs L).symm
  refine ⟨⟨andL (andL (andL hfront)), andL (andL (andL (andL (andL hr))))⟩,
      ⟨andR (andL (andL hfront)), andR (andL (andL (andL (andL hr))))⟩,
    ⟨andR (andL hfront), andR (andL (andL (andL hr)))⟩, ⟨andR hfront, andR (andL (andL hr))⟩,
        ⟨?_, andR (andL hr)⟩, fun h => ?_, fun h => ?_⟩
  · by_cases h : hasExperts L
    · rw [hE.1 h, if_pos rfl] at hlast
      rw [if_pos h]
      exact andL (andL (andL (andL (andL (andL hlast)))))
    · rw [Bool.eq_false_iff.2 fun a => h (hE.2 a), if_neg (by simp)] at hlast
      rw [if_neg h]
      exact hlast
  · rw [hE.1 h, if_pos rfl] at hlast hrlast
    have hsz : (weights.perLayer.entry L).routed.size = 128 := beq_iff_eq.1
        (andR (andL (andL (andL (andL hlast)))))
    refine ⟨⟨andR (andL (andL (andL (andL (andL hlast))))), andL hrlast⟩, hsz, fun e he => ?_⟩
    have hmem := entry_mem (weights.perLayer.entry L).routed (k := e) (by rw [hsz]; exact he)
    exact ⟨Array.all_eq_true_iff_forall_mem.1 (andR (andL (andL (andL hlast)))) _ hmem,
        Array.all_eq_true_iff_forall_mem.1 (andR hrlast) _ hmem⟩
  · rw [Bool.eq_false_iff.2 fun a => h (hE.2 a), if_neg (by simp)] at hrlast
    exact ⟨beq_iff_eq.1 (andL hrlast), beq_iff_eq.1 (andR hrlast)⟩

theorem valid_outer : (IntegerTransformer.hasSize ppref.V ppref.d weights.embedding = true ∧
    entriesWithin (-2155905152) 2139062143 weights.embedding = true) ∧
    (IntegerTransformer.hasSize ppref.d ppref.V weights.head = true ∧ entriesWithin (-4096)
        4095 weights.head = true) := by
  obtain ⟨-, -, h3, -, -, -, -, -, -, h10, -⟩ := valid_numbers hs
  have hwf := valid_wellFormed hw
  unfold IntegerTransformer.wellFormed at hwf
  have he := andR (andL (andL (andL (andL hwf))))
  have hh := andR (andL (andL (andL hwf)))
  rw [h3, h10] at he hh
  have hr := andL (valid_weights hw)
  exact ⟨⟨he, andL hr⟩, ⟨hh, andR hr⟩⟩

theorem weights_back : weightsArraysOf ppref (weightsTo weights) = weights := by
  have hp : (tabl ppref.layers fun L => layerArrays ppref ((weightsTo weights).layer L) L) =
      weights.perLayer :=
    (tabl_congr fun L hL => layerArrays_layerTo (valid_layerFits hs hw hL)).trans
        (array_eq weights.perLayer (valid_perLayer hs hw)).symm
  have he : mat ppref.V ppref.d (weightsTo weights).Emb = weights.embedding :=
      mat_entries (valid_outer hs hw).1.1
  have hh : mat ppref.d ppref.V (weightsTo weights).H = weights.head := mat_entries
      (valid_outer hs hw).2.1
  unfold weightsArraysOf
  rw [hp, he, hh]

theorem wf_weightsTo : (weightsTo weights).WF ppref := by
  refine ⟨fun L => ?_, box_entries (valid_outer hs hw).1.1 (valid_outer hs hw).1.2, two_entries
      (valid_outer hs hw).2.1 (valid_outer hs hw).2.2⟩
  by_cases hL : L < ppref.layers
  · rw [if_pos hL]
    exact wf_layerTo (valid_layerFits hs hw hL)
  · rw [if_neg hL]
    show (layerTo (weights.perLayer.entry L)).IsZero
    rw [entry_out weights.perLayer
      (by rw [(valid_perLayer hs hw)]; exact Nat.le_of_not_lt hL)]
    exact isZero_default

end ValidWeights

end Back

end VerifiableInference
