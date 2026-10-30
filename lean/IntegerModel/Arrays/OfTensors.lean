-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Arrays/OfTensors.lean

From the library's tables of parameters (`ScalesAndPolicy`, Inst/Model/ProgTests.lean) and weight tensors
(`Weights`, Inst/Model/Program.lean) to settings and weights as arrays
(`IntegerTransformer.Settings`, `.Weights`, IntegerModel/Model.lean), which
`IntegerTransformer.model` takes as arguments.
`settingsArraysOf` writes a table of parameters as settings. Besides the three numbers of its
acceptance policy, for which the settings have no field, a table has 72 numbers that the model does
not read: the router's shift and the routed expert's two shifts in each of the 24 dense layers
(layers without experts). The settings have fields for them, but `settingsAreValid` requires 0
there: `settingsArraysOf` writes 0, whatever the table has. So it is not injective (an argument; no
theorem states it).
`weightsArraysOf` writes weight tensors as arrays.
`settingsAreValid_arrays`, `weightsAreValid_arrays`: at the sizes `ppref`, the settings of every
lawful table (`Lawful`, Inst/Model/Scales.lean), and the arrays of all well-formed tensors
(`Weights.WF`, Inst/Model/Program.lean) at these settings, pass the tests
(VerifiableInference/ModelWeights.lean).
`lookupTables_eq`: the five tables are the library's.
`feeds_arrays`: for every `m : IntegerModel.Committed` (IntegerModel/Reply.lean), the arrays of m's
table and tensors, with the five tables, meet `Feeds m` (IntegerModel/Readable/Tie.lean).
-/
import VerifiableInference.ModelWeights
import IntegerModel.Readable.Exists

set_option autoImplicit false

/- No default table of scales here: `Scl.ref` (Inst/Model/Scl.lean) is off; each `Scl` is named. -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference

open Inst.Model IntegerModel.Readable IntegerModel.Runnable

/-! ## 1. The five tables are the library's -/

theorem packedEntry_eq (packed : Array ℕ) (bits index : ℕ) : packedEntry packed bits index = dec
    packed bits index := rfl

theorem refC_zero (i j : ℕ) : refC 0 i j = clamp 4096 ((dec Data.cos 14 (64 * i + j) : ℤ) - 4096) :=
    if_neg (by decide)

theorem refS_zero (i j : ℕ) : refS 0 i j = clamp 4096 ((dec Data.sin 14 (64 * i + j) : ℤ) - 4096) :=
    if_neg (by decide)

theorem sizes_ref : ppref.T = 1024 ∧ ppref.ch / 2 = 64 := ⟨rfl, rfl⟩

theorem cosineTable_eq : cosineTable = mat ppref.T (ppref.ch / 2) (refC 0) := by
  rewrite [sizes_ref.1, sizes_ref.2]
  unfold cosineTable mat
  rewrite [tabulate_eq]
  refine tabl_congr fun i _ => ?_
  rewrite [tabulate_eq]
  refine tabl_congr fun j _ => ?_
  rewrite [refC_zero, IntegerModel.Readable.clamp_eq, packedEntry_eq]
  generalize Data.cos = packed
  rfl

theorem sineTable_eq : sineTable = mat ppref.T (ppref.ch / 2) (refS 0) := by
  rewrite [sizes_ref.1, sizes_ref.2]
  unfold sineTable mat
  rewrite [tabulate_eq]
  refine tabl_congr fun i _ => ?_
  rewrite [tabulate_eq]
  refine tabl_congr fun j _ => ?_
  rewrite [refS_zero, IntegerModel.Readable.clamp_eq, packedEntry_eq]
  generalize Data.sin = packed
  rfl

theorem exponentialTable_eq : exponentialTable = tabl 2307 fun u => refExp (u : ℤ) := by
  unfold exponentialTable
  rewrite [tabulate_eq]
  refine tabl_congr fun u _ => ?_
  unfold refExp
  rewrite [Int.toNat_natCast, packedEntry_eq]
  generalize Data.exp = packed
  rfl

theorem siluTable_eq : siluTable = tabl 65536 fun k => refSILU ((k : ℤ) - 32768 + 2 ^ 15) := by
  unfold siluTable
  rewrite [tabulate_eq]
  refine tabl_congr fun k _ => ?_
  have a : (k : ℤ) - 32768 + 2 ^ 15 - 2 ^ 15 = (k : ℤ) - 32768 := by ring
  have b1 : (-2 ^ 14 : ℤ) = -16384 := by norm_num
  have b2 : (2 ^ 14 - 1 : ℤ) = 16383 := by norm_num
  have b3 : (2 ^ 14 : ℤ) = 16384 := by norm_num
  unfold refSILU
  rewrite [a, b1, b2, b3, IntegerModel.Readable.clamp_eq, packedEntry_eq]
  generalize Data.silu = packed
  rfl

theorem sigmoidTable_eq : sigmoidTable = tabl 32768 fun k => refSIGM ((k : ℤ) - 16384 + 2 ^ 15) :=
    by
  unfold sigmoidTable
  rewrite [tabulate_eq]
  refine tabl_congr fun k _ => ?_
  have a : (k : ℤ) - 16384 + 2 ^ 15 - 2 ^ 14 = (k : ℤ) := by ring
  unfold refSIGM
  rewrite [a, Int.toNat_natCast, packedEntry_eq]
  generalize Data.sigm = packed
  rfl

theorem lookupTables_eq : lookupTables = tablesArrays ppref := by
  unfold lookupTables tablesArrays
  rewrite [cosineTable_eq, sineTable_eq, exponentialTable_eq, siluTable_eq, sigmoidTable_eq]
  rfl

/-! ## 2. From tables and tensors to arrays. P is a variable in the lemmas, so that Lean does not
unfold the full-size numbers. -/

/-- The weights of one layer as arrays. A dense layer has no router and no routed experts. -/
def layerArrays (P : Params) (w : LayerW) (L : ℕ) : IntegerTransformer.LayerWeights :=
  if hasExperts L then layerWeightsOf P w L
      else { layerWeightsOf P w L with router := #[], routed := #[] }

/-- All weights as arrays. -/
def weightsArraysOf (P : Params) (w : Weights) : IntegerTransformer.Weights :=
  { embedding := mat P.V P.d w.Emb,
    perLayer := tabl P.layers fun L => layerArrays P (w.layer L) L,
    head := mat P.d P.V w.H }

/-- The quantization parameters of one layer. In a dense layer the router's shift and the routed
expert's two shifts, which the model does not read, are written as 0, as `settingsAreValid`
requires. -/
def layerScales (k : LayerScale) (L : ℕ) : IntegerTransformer.LayerSettings :=
  if hasExperts L then layerSettingsOf k L
      else { layerSettingsOf k L with routerShift := 0, routedGateShift := 0, routedUpShift := 0 }

/-- The sizes and all quantization parameters. -/
def settingsArraysOf (P : Params) (pp : ScalesAndPolicy) : IntegerTransformer.Settings :=
  { settingsArrays P pp with perLayer := tabl P.layers fun L => layerScales (pp.kap L) L }

theorem layerScales_get (P : Params) (pp : ScalesAndPolicy) {L : ℕ} (hL : L < P.layers) :
    ((settingsArraysOf P pp).perLayer.entry L) = layerScales (pp.kap L) L := tabl_entry _ hL

theorem sameScales_arrays (k : LayerScale) (L : ℕ) : SameScales L (layerScales k L) k := by
  unfold layerScales
  by_cases hE : hasExperts L
  · rw [if_pos hE]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _
        => rfl, fun _ => rfl⟩
  · rw [if_neg hE]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun a => absurd a
        hE, fun a => absurd a hE, fun a => absurd a hE⟩

theorem sameTables_arrays (P : Params) (pp : ScalesAndPolicy) (L : ℕ) : SameTables P P.T (settingsArraysOf P pp)
    (layerScales (pp.kap L) L) (tablesArrays P) tbRef L (pp.kap L).expRows := by
  have h := sameTables_of P pp L
  unfold layerScales
  by_cases hE : hasExperts L
  · rw [if_pos hE]
    exact ⟨h.cos, h.sin, h.rows, h.exp, h.silu, h.sigm⟩
  · rw [if_neg hE]
    exact ⟨h.cos, h.sin, h.rows, h.exp, h.silu, h.sigm⟩

theorem layerArrays_get (P : Params) (w : Weights) {L : ℕ} (hL : L < P.layers) :
    ((weightsArraysOf P w).perLayer.entry L) = layerArrays P (w.layer L) L := tabl_entry _ hL

theorem sameLayer_arrays (P : Params) (w : LayerW) (L : ℕ) : SameLayer P L (layerArrays P w L) w :=
    by
  unfold layerArrays
  by_cases hE : hasExperts L
  · rw [if_pos hE]
    exact sameLayer_of P w L
  · rw [if_neg hE]
    have h := sameLayer_of P w L
    exact ⟨h.Wq, h.Wk, h.Wv, h.Wo, h.Wg, h.Wu, h.Wd, fun a => absurd a hE, fun a => absurd a hE, fun
        a => absurd a hE, fun a => absurd a hE⟩

theorem same_arrays (P : Params) (pp : ScalesAndPolicy) (w : Weights) :
    Same P P.T pp.kap pp.nf (fun _ => tbRef) w (settingsArraysOf P pp) (tablesArrays P)
        (weightsArraysOf P w) := by
  have h := same_of P pp w
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun L hL => ?_, rfl, rfl, rfl, fun L
      hL => ?_, fun L hL => ?_, h.emb, h.head⟩
  · rw [layerScales_get P pp hL]
    exact sameScales_arrays _ L
  · rw [layerScales_get P pp hL]
    exact sameTables_arrays P pp L
  · rw [layerArrays_get P w hL]
    exact sameLayer_arrays P _ L

theorem isMixture_arrays (P : Params) (pp : ScalesAndPolicy) (L : ℕ) : (settingsArraysOf P pp).isMixture L =
    (settingsArrays P pp).isMixture L := rfl

theorem layerWellFormed_arrays (P : Params) (hn : 0 < P.nexp) (pp : ScalesAndPolicy) (k : LayerScale)
    (w : LayerW) (L : ℕ) :
    IntegerTransformer.layerWellFormed (settingsArraysOf P pp) (layerScales k L) (layerArrays P w L)
        ((settingsArraysOf P pp).isMixture L)
      = IntegerTransformer.layerWellFormed (settingsArrays P pp) (layerSettingsOf k L)
          (layerWeightsOf P w L) ((settingsArrays P pp).isMixture L) := by
  have hmix := isMixture_iff P L hn P.T (settingsArrays P pp)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [isMixture_arrays]
  unfold layerArrays layerScales
  by_cases hE : hasExperts L
  · rw [if_pos hE, if_pos hE]
    rfl
  · rw [if_neg hE, if_neg hE, Bool.eq_false_iff.2 fun a => hE (hmix.1 a)]
    unfold IntegerTransformer.layerWellFormed
    rw [if_neg (by simp), if_neg (by simp)]
    rfl

theorem wellFormed_arrays (P : Params) (hP : FineSizes P) (pp : ScalesAndPolicy) (hl : Lawful pp) (w : Weights) :
    IntegerTransformer.wellFormed (settingsArraysOf P pp) (tablesArrays P) (weightsArraysOf P w) =
        true := by
  have h := wellFormed_of P hP pp hl w
  have sz : (weightsArraysOf P w).perLayer.size = (weightsArrays P w).perLayer.size := by
    show (tabl P.layers fun L => layerArrays P (w.layer L) L).size =
        (tabl P.layers fun L => layerWeightsOf P (w.layer L) L).size
    rw [tabl_size, tabl_size]
  have sz2 : (settingsArraysOf P pp).perLayer.size = (settingsArrays P pp).perLayer.size := by
    show (tabl P.layers fun L => layerScales (pp.kap L) L).size =
        (tabl P.layers fun L => layerSettingsOf (pp.kap L) L).size
    rw [tabl_size, tabl_size]
  have al : ((List.range (settingsArraysOf P pp).layers).all fun l =>
      IntegerTransformer.layerWellFormed (settingsArraysOf P pp)
      ((settingsArraysOf P pp).perLayer.entry l) ((weightsArraysOf P w).perLayer.entry l)
      ((settingsArraysOf P pp).isMixture l))
      = ((List.range (settingsArrays P pp).layers).all fun l => IntegerTransformer.layerWellFormed
          (settingsArrays P pp) ((settingsArrays P pp).perLayer.entry l)
          ((weightsArrays P w).perLayer.entry l) ((settingsArrays P pp).isMixture l)) := by
    refine Bool.eq_iff_iff.2 ?_
    rw [List.all_eq_true, List.all_eq_true]
    constructor
    · intro a l hl'
      have hl2 : l < P.layers := List.mem_range.1 hl'
      have b := a l hl'
      rw [layerArrays_get P w hl2, layerScales_get P pp hl2, layerWellFormed_arrays P hP.nexp] at b
      rw [wlayer_get P w hl2, layer_get P pp hl2]
      exact b
    · intro a l hl'
      have hl2 : l < P.layers := List.mem_range.1 hl'
      have b := a l hl'
      rw [wlayer_get P w hl2, layer_get P pp hl2] at b
      rw [layerArrays_get P w hl2, layerScales_get P pp hl2, layerWellFormed_arrays P hP.nexp]
      exact b
  unfold IntegerTransformer.wellFormed at h ⊢
  rw [sz, sz2, al]
  exact h

theorem feeds_arrays (m : IntegerModel.Committed) : Feeds m (settingsArraysOf ppref m.settings)
    lookupTables (weightsArraysOf ppref m.weights.val) := by
  rw [lookupTables_eq]
  exact ⟨same_arrays ppref _ _, wellFormed_arrays ppref fine_ref _ m.lawful _⟩

/-! ## 3. The arrays of lawful tables and well-formed tensors pass the tests -/

theorem entriesWithin_mat {r c : ℕ} {low high : ℤ} {W : Mat} (h : Box r c low high W) :
    entriesWithin low high (mat r c W) = true := by
  unfold entriesWithin mat
  refine (tabl_all _ _ _).2 fun j hj => (tabl_all _ _ _).2 fun x hx => ?_
  have a := h j x
  rw [if_pos ⟨hj, hx⟩] at a
  rw [Bool.and_eq_true]
  exact ⟨decide_eq_true a.1, decide_eq_true a.2⟩

theorem twoWithin_mat {r c : ℕ} {W : Mat} (h : Two r c W) : entriesWithin (-4096) 4095 (mat r c W) =
    true := by
  have e1 : (-2 ^ 12 : ℤ) = -4096 := by norm_num
  have e2 : (2 ^ 12 - 1 : ℤ) = 4095 := by norm_num
  unfold Two at h
  rw [e1, e2] at h
  exact entriesWithin_mat h

theorem gatedWithin_of {d h : ℕ} {g u dn : Mat} (hg : Two d h g) (hu : Two d h u) (hd : Two h d dn)
    : gatedWithin (gatedOf d h g u dn) = true := by
  unfold gatedWithin gatedOf
  rw [twoWithin_mat hg, twoWithin_mat hu, twoWithin_mat hd]
  rfl

theorem layerWeightsInRange_arrays (P : Params) (w : LayerW) (L : ℕ) (h : w.WF P L) (mixture : Bool)
    (hmix : mixture = true ↔ hasExperts L) :
    layerWeightsInRange mixture (layerArrays P w L) = true := by
  obtain ⟨hq, hk, hv, ho, hr⟩ := h
  unfold layerArrays
  by_cases hE : hasExperts L
  · rw [if_pos hE] at hr ⊢
    obtain ⟨hg, hu, hd, hw, he⟩ := hr
    have m : mixture = true := hmix.2 hE
    have q1 : entriesWithin (-4096) 4095 (layerWeightsOf P w L).query = true := twoWithin_mat hq
    have q2 : entriesWithin (-4096) 4095 (layerWeightsOf P w L).key = true := twoWithin_mat hk
    have q3 : entriesWithin (-4096) 4095 (layerWeightsOf P w L).value = true := twoWithin_mat hv
    have q4 : entriesWithin (-4096) 4095 (layerWeightsOf P w L).output = true := twoWithin_mat ho
    have q5 : gatedWithin (layerWeightsOf P w L).shared = true := by
      show gatedWithin (gatedOf P.d (if hasExperts L then P.fe else P.f) w.Wg w.Wu w.Wd) = true
      rw [if_pos hE]
      exact gatedWithin_of hg hu hd
    have q6 : entriesWithin (-4096) 4095 (layerWeightsOf P w L).router = true := twoWithin_mat hw
    have q7 : (layerWeightsOf P w L).routed.all gatedWithin = true := by
      refine (tabl_all _ _ _).2 fun e hlt => ?_
      have a := he e
      rw [if_pos hlt] at a
      exact gatedWithin_of a.1 a.2.1 a.2.2
    unfold layerWeightsInRange
    rw [m, if_pos rfl, q1, q2, q3, q4, q5, q6, q7]
    rfl
  · rw [if_neg hE] at hr ⊢
    obtain ⟨hg, hu, hd, -, -⟩ := hr
    have m : mixture = false := Bool.eq_false_iff.2 fun a => hE (hmix.1 a)
    have q1 : entriesWithin (-4096) 4095 (layerWeightsOf P w L).query = true := twoWithin_mat hq
    have q2 : entriesWithin (-4096) 4095 (layerWeightsOf P w L).key = true := twoWithin_mat hk
    have q3 : entriesWithin (-4096) 4095 (layerWeightsOf P w L).value = true := twoWithin_mat hv
    have q4 : entriesWithin (-4096) 4095 (layerWeightsOf P w L).output = true := twoWithin_mat ho
    have q5 : gatedWithin (layerWeightsOf P w L).shared = true := by
      show gatedWithin (gatedOf P.d (if hasExperts L then P.fe else P.f) w.Wg w.Wu w.Wd) = true
      rw [if_neg hE]
      exact gatedWithin_of hg hu hd
    unfold layerWeightsInRange
    rw [m, if_neg (by simp)]
    show (entriesWithin (-4096) 4095 (layerWeightsOf P w L).query && entriesWithin (-4096) 4095
        (layerWeightsOf P w L).key && entriesWithin (-4096) 4095 (layerWeightsOf P w L).value
      && entriesWithin (-4096) 4095 (layerWeightsOf P w L).output && gatedWithin
          (layerWeightsOf P w L).shared && ((#[] : IntegerTransformer.Matrix).size == 0 &&
          (#[] : Array IntegerTransformer.GatedWeights).size == 0)) = true
    rw [q1, q2, q3, q4, q5]
    rfl

/-- Stated for variable sizes, so that a proof checker compares small terms. -/
theorem isMixture_of (P : Params) (hn : 0 < P.nexp) (pp : ScalesAndPolicy) (L : ℕ) :
    (settingsArraysOf P pp).isMixture L = true ↔ hasExperts L := by
  rw [isMixture_arrays]
  exact isMixture_iff P L hn P.T (settingsArrays P pp) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl⟩

theorem isMixture_ref (pp : ScalesAndPolicy) (L : ℕ) : (settingsArraysOf ppref pp).isMixture L = true ↔
    hasExperts L :=
  isMixture_of ppref fine_ref.nexp pp L

theorem weightsInRange_arrays (pp : ScalesAndPolicy) (w : Weights) (h : w.WF ppref) : weightsInRange
    (settingsArraysOf ppref pp) (weightsArraysOf ppref w) = true := by
  obtain ⟨hl, he, hh⟩ := h
  have a1 : entriesWithin (-2155905152) 2139062143 (weightsArraysOf ppref w).embedding = true :=
      entriesWithin_mat he
  have a2 : entriesWithin (-4096) 4095 (weightsArraysOf ppref w).head = true := twoWithin_mat hh
  have a3 : ((List.range 48).all fun layer => layerWeightsInRange
      ((settingsArraysOf ppref pp).isMixture layer) ((weightsArraysOf ppref w).perLayer.entry
      layer)) = true := by
    rw [List.all_eq_true]
    intro L hL
    have hL2 : L < ppref.layers := List.mem_range.1 hL
    rw [layerArrays_get ppref w hL2]
    have b := hl L
    rw [if_pos hL2] at b
    exact layerWeightsInRange_arrays ppref _ L b _ (isMixture_ref pp L)
  unfold weightsInRange
  rw [a1, a2, a3]
  rfl

theorem normInRange_of {np : NormPar} (h : np.OK) (hk : np.K ≤ np.M) : normInRange np.M np.K np.eps
    = true := by
  unfold NormPar.OK at h
  simp only [normInRange, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem layerSettingsInRange_of {k : LayerScale} (L : ℕ) (r : FFSeg.Ranges k)
    (hs : 4 ≤ k.sh ∧ k.sh ≤ 12) (h1 : k.n1.K ≤ k.n1.M) (h2 : k.n2.K ≤ k.n2.M)
    (mixture : Bool) (hmix : mixture = true ↔ hasExperts L) : layerSettingsInRange mixture
        (layerScales k L) = true := by
  have a1 := r.kq
  have a2 := r.kk
  have a3 := r.qk
  have a4 := r.kv
  have a5 := r.ko
  have a6 := r.kg
  have a7 := r.kg'
  have a8 := r.ku
  have a9 := r.ku'
  have a10 := r.kd
  have a11 := r.kr
  unfold layerScales
  by_cases hE : hasExperts L
  · have n1 : normInRange (layerSettingsOf k L).attentionBits (layerSettingsOf k L).attentionShift
      (layerSettingsOf k L).attentionEps = true := normInRange_of r.n1 h1
    have n2 : normInRange (layerSettingsOf k L).feedForwardBits
        (layerSettingsOf k L).feedForwardShift (layerSettingsOf k L).feedForwardEps = true :=
        normInRange_of r.n2 h2
    rw [if_pos hE, hmix.2 hE]
    unfold layerSettingsInRange
    rw [n1, n2, if_pos rfl]
    simp only [layerSettingsOf, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
        and_true]
    omega
  · have n1 : normInRange k.n1.M k.n1.K k.n1.eps = true := normInRange_of r.n1 h1
    have n2 : normInRange k.n2.M k.n2.K k.n2.eps = true := normInRange_of r.n2 h2
    rw [if_neg hE, Bool.eq_false_iff.2 fun a => hE (hmix.1 a)]
    unfold layerSettingsInRange
    rw [if_neg (by simp)]
    simp only [layerSettingsOf, n1, n2, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
        beq_iff_eq, and_true]
    omega

theorem softmaxShift_layerScales (k : LayerScale) (L : ℕ) : (layerScales k L).softmaxShift = k.sh :=
    by
  unfold layerScales
  by_cases hE : hasExperts L
  · rw [if_pos hE]; rfl
  · rw [if_neg hE]; rfl

theorem rotary_layerScales (k : LayerScale) (L : ℕ) : (layerScales k L).rotary = decide
    (¬ rotaryOff L) := by
  unfold layerScales
  by_cases hE : hasExperts L
  · rw [if_pos hE]; rfl
  · rw [if_neg hE]; rfl

theorem settingsInRange_arrays (pp : ScalesAndPolicy) (hl : Lawful pp) : settingsInRange
    (settingsArraysOf ppref pp) = true := by
  have f : normInRange (settingsArraysOf ppref pp).finalBits (settingsArraysOf ppref pp).finalShift
      (settingsArraysOf ppref pp).finalEps = true := normInRange_of hl.nf hl.km.2
  have a : ((List.range 48).all fun layer => layerSettingsInRange
      ((settingsArraysOf ppref pp).isMixture layer) ((settingsArraysOf ppref pp).perLayer.entry
      layer)
      && ((settingsArraysOf ppref pp).perLayer.entry layer).softmaxShift ==
          ((settingsArraysOf ppref pp).perLayer.entry (4 * (layer / 4))).softmaxShift) = true := by
    rw [List.all_eq_true]
    intro L hL
    have hL1 : L < 48 := List.mem_range.1 hL
    have hL2 : L < ppref.layers := hL1
    have hG : 4 * (L / 4) < ppref.layers := by show 4 * (L / 4) < 48; omega
    rw [layerScales_get ppref pp hL2, layerScales_get ppref pp hG, Bool.and_eq_true]
    refine ⟨?_, beq_iff_eq.2 ?_⟩
    · refine layerSettingsInRange_of L (by
        rw [kap_lt pp hL1]; exact hl.ff ⟨L, hL1⟩) ?_ ?_ ?_ _ (isMixture_ref pp L)
      · rw [kap_lt pp hL1]; exact hl.sh ⟨L, hL1⟩
      · rw [kap_lt pp hL1]; exact (hl.km.1 ⟨L, hL1⟩).1
      · rw [kap_lt pp hL1]; exact (hl.km.1 ⟨L, hL1⟩).2
    · rw [softmaxShift_layerScales, softmaxShift_layerScales]
      have o := hl.one ⟨L / 4, by omega⟩ ⟨L % 4, by omega⟩
      have e : 4 * (L / 4) + L % 4 = L := Nat.div_add_mod L 4
      simp only at o
      rw [e] at o
      exact o
  unfold settingsInRange
  rw [f, a]
  rfl

theorem hasModelSizes_arrays (pp : ScalesAndPolicy) : hasModelSizes (settingsArraysOf ppref pp) = true :=
    by
  have a : ((List.range 48).all fun layer => ((settingsArraysOf ppref pp).perLayer.entry
      layer).rotary == (layer % 4 != 3)) = true := by
    rw [List.all_eq_true]
    intro L hL
    have hL2 : L < ppref.layers := List.mem_range.1 hL
    rw [layerScales_get ppref pp hL2, rotary_layerScales]
    unfold rotaryOff
    by_cases h : L % 4 = 3 <;> simp [h]
  unfold hasModelSizes
  rw [a]
  rfl

/-- The settings of every lawful table pass the test. -/
theorem settingsAreValid_arrays (pp : ScalesAndPolicy) (hl : Lawful pp) :
    settingsAreValid (settingsArraysOf ppref pp) = true := by
  have a1 : hasModelSizes (settingsArraysOf ppref pp) = true := hasModelSizes_arrays pp
  have a2 : settingsInRange (settingsArraysOf ppref pp) = true := settingsInRange_arrays pp hl
  have a3 : ((settingsArraysOf ppref pp).perLayer.size == (settingsArraysOf ppref pp).layers)
      = true := by
    show ((tabl ppref.layers fun L => layerScales (pp.kap L) L).size == ppref.layers) = true
    rw [tabl_size]
    exact beq_self_eq_true _
  unfold settingsAreValid
  rw [a1, a2, a3]
  rfl

/-- The arrays of all well-formed tensors pass the test, at the settings of every lawful table. -/
theorem weightsAreValid_arrays (pp : ScalesAndPolicy) (hl : Lawful pp) (w : Weights) (h : w.WF ppref) :
    weightsAreValid (settingsArraysOf ppref pp) (weightsArraysOf ppref w) = true := by
  have a1 : IntegerTransformer.wellFormed (settingsArraysOf ppref pp) lookupTables
      (weightsArraysOf ppref w) = true := by
    rw [lookupTables_eq]
    exact wellFormed_arrays ppref fine_ref pp hl w
  have a2 : weightsInRange (settingsArraysOf ppref pp) (weightsArraysOf ppref w) = true :=
    weightsInRange_arrays pp w h
  unfold weightsAreValid
  rw [a1, a2]
  rfl

end VerifiableInference
