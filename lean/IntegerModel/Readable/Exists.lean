-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Readable/Exists.lean

The arguments of `IntegerTransformer.model` for `m : IntegerModel.Committed` (lawful settings and
integer weights): `settingsArrays`,
`tablesArrays` and `weightsArrays` write the settings of `m`, the five fixed tables and the weights
of `m` as arrays.
Proved, for every `m`: these arrays contain the numbers of `m` and pass the model's test
`wellFormed` (`feeds_of`). So the hypothesis `Feeds` of IntegerModel/Readable/Tie.lean can always be
met.
-/
import IntegerModel.Readable.Tie
import IntegerModel.Runnable.Lawful

set_option autoImplicit false

namespace IntegerModel.Readable

open Inst.Model IntegerModel.Runnable

/-! ## Functions as arrays -/

/-- The r × c matrix of `f`, as the array of its rows. -/
def mat (r c : ℕ) (f : Mat) : Array (Array ℤ) := tabl r fun j => tabl c (f j)

theorem mat_get {r c : ℕ} (f : Mat) {j k : ℕ} (hj : j < r) (hk : k < c) :
    ((((mat r c f).entry j)).entry k) = f j k := by
  unfold mat
  rw [tabl_entry _ hj, tabl_entry _ hk]

theorem hasSize_mat (r c : ℕ) (f : Mat) : IntegerTransformer.hasSize r c (mat r c f) = true := by
  unfold IntegerTransformer.hasSize mat
  rw [Bool.and_eq_true, tabl_all, tabl_size]
  exact ⟨beq_self_eq_true r, fun i _ => by rw [tabl_size]; exact beq_self_eq_true c⟩

/-! ## The arguments, from sizes P, scales pp and weights w. P is a variable, so that Lean does not
unfold the full-size numbers. -/

/-- The scales of layer L. Layer L has the rotary step unless L mod 4 = 3. -/
def layerSettingsOf (k : LayerScale) (L : ℕ) : IntegerTransformer.LayerSettings :=
  { attentionBits := k.n1.M, attentionShift := k.n1.K, attentionEps := k.n1.eps, queryShift := k.kq,
    keyShift := k.kk, valueShift := k.kv, rotary := decide (¬ rotaryOff L), softmaxShift := k.sh,
    outputShift := k.ko, feedForwardBits := k.n2.M, feedForwardShift := k.n2.K,
    feedForwardEps := k.n2.eps, gateShift := k.kg, upShift := k.ku, downShift := k.kd,
    routerShift := k.kr, routedGateShift := k.kg', routedUpShift := k.ku' }

/-- The sizes and all scales, as the model's `Settings`. -/
def settingsArrays (P : Params) (pp : ScalesAndPolicy) : IntegerTransformer.Settings :=
  { positions := P.T, layers := P.layers, width := P.d, queryHeads := P.nq, keyValueHeads := P.nkv,
    headDim := P.ch, hidden := P.f, expertHidden := P.fe, experts := P.nexp, vocabulary := P.V,
    rotaryScale := 12, finalEps := pp.nf.eps, finalBits := pp.nf.M, finalShift := pp.nf.K,
    perLayer := tabl P.layers fun L => layerSettingsOf (pp.kap L) L }

/-- The five fixed tables as arrays. `refC` and `refS` take the layer first and return 2^12 and 0 in
a layer without rotary step; layer 0 has the step, so `refC 0` and `refS 0` are the entries of the
cosine and sine tables (and `rotaryScale` is 12 in `settingsArrays`).
The exponential has 2,307 rows in use. SiLU and the sigmoid cover the key ranges that `wellFormed`
requires: 65,536 keys from -32,768, and 32,768 keys from -16,384; the library reads both at key +
2^15. -/
def tablesArrays (P : Params) : IntegerTransformer.Tables :=
  { cosine := mat P.T (P.ch / 2) (refC 0), sine := mat P.T (P.ch / 2) (refS 0),
    exponential := tabl 2307 fun u => refExp (u : ℤ),
    silu :=
      { lowestKey := -32768, entries := tabl 65536 fun k => refSILU ((k : ℤ) - 32768 + 2 ^ 15) },
    sigmoid :=
      { lowestKey := -16384, entries := tabl 32768 fun k => refSIGM ((k : ℤ) - 16384 + 2 ^ 15) } }

/-- The three matrices of a gated feed-forward block. -/
def gatedOf (d h : ℕ) (g u dn : Mat) : IntegerTransformer.GatedWeights :=
  { gate := mat d h g, up := mat d h u, down := mat h d dn }

/-- The weights of layer L. In a dense layer `router` and `routed` are filled in as well (with
zeros, for well-formed weights); the model does not read or test them there. -/
def layerWeightsOf (P : Params) (w : LayerW) (L : ℕ) : IntegerTransformer.LayerWeights :=
  { query := mat P.d (P.nq * P.ch) w.Wq, key := mat P.d (P.nkv * P.ch) w.Wk,
    value := mat P.d (P.nkv * P.ch) w.Wv, output := mat (P.nq * P.ch) P.d w.Wo,
    shared := gatedOf P.d (if hasExperts L then P.fe else P.f) w.Wg w.Wu w.Wd,
    router := mat P.d P.nexp w.Wr,
    routed := tabl P.nexp fun e => gatedOf P.d P.fe (w.Eg e) (w.Eu e) (w.Ed e) }

/-- All weights, as the model's `Weights`. -/
def weightsArrays (P : Params) (w : Inst.Model.Weights) : IntegerTransformer.Weights :=
  { embedding := mat P.V P.d w.Emb,
    perLayer := tabl P.layers fun L => layerWeightsOf P (w.layer L) L, head := mat P.d P.V w.H }

/-! ## The arrays contain the library's numbers -/

theorem read_silu (P : Params) (key : ℤ) (h1 : -32768 ≤ key) (h2 : key ≤ 32767) :
    (tablesArrays P).silu.read key = refSILU (key + 2 ^ 15) := by
  show (if (-32768 : ℤ) ≤ key then
        (tabl 65536 fun k => refSILU ((k : ℤ) - 32768 + 2 ^ 15)).entry (key - -32768).toNat
      else 0) = _
  rw [if_pos h1, tabl_entry _ (by omega)]
  congr 1
  omega

theorem read_sigm (P : Params) (key : ℤ) (h1 : -16384 ≤ key) (h2 : key ≤ 16383) :
    (tablesArrays P).sigmoid.read key = refSIGM (key + 2 ^ 15) := by
  show (if (-16384 : ℤ) ≤ key then
        (tabl 32768 fun k => refSIGM ((k : ℤ) - 16384 + 2 ^ 15)).entry (key - -16384).toNat
      else 0) = _
  rw [if_pos h1, tabl_entry _ (by omega)]
  congr 1
  omega

theorem sameTables_of (P : Params) (pp : ScalesAndPolicy) (L : ℕ) :
    SameTables P P.T (settingsArrays P pp) (layerSettingsOf (pp.kap L) L) (tablesArrays P)
      tbRef L (pp.kap L).expRows where
  cos i hi j hj := by
    have h := (tabRel_ref pp L).cos i j
    rw [← h]
    show (if decide (¬ rotaryOff L) = true then ((((mat P.T (P.ch / 2) (refC 0)).entry i)).entry j)
        else 2 ^ 12) =
      if ArrayProgram.hasRotary L = true then refC 0 i j else 2 ^ 12
    rw [mat_get _ hi hj]
    by_cases hr : rotaryOff L
    · rw [if_neg (by simpa using hr), if_neg fun a => (hasRotary_iff L).1 a hr]
    · rw [if_pos (by simpa using hr), if_pos ((hasRotary_iff L).2 hr)]
  sin i hi j hj := by
    have h := (tabRel_ref pp L).sin i j
    rw [← h]
    show (if decide (¬ rotaryOff L) = true then ((((mat P.T (P.ch / 2) (refS 0)).entry i)).entry j)
        else 0) =
      if ArrayProgram.hasRotary L = true then refS 0 i j else 0
    rw [mat_get _ hi hj]
    by_cases hr : rotaryOff L
    · rw [if_neg (by simpa using hr), if_neg fun a => (hasRotary_iff L).1 a hr]
    · rw [if_pos (by simpa using hr), if_pos ((hasRotary_iff L).2 hr)]
  rows := by
    rw [← (tabRel_ref pp L).rows]
    show (((tabl 2307 fun u => refExp (u : ℤ)).size : ℕ) : ℤ) = 2307
    rw [tabl_size]
    rfl
  exp u hu := by
    have hu' : u < 2307 := by
      have : (tabl 2307 fun u => refExp (u : ℤ)).size = 2307 := tabl_size _ _
      exact this ▸ hu
    exact tabl_entry _ hu'
  silu key h1 h2 := read_silu P key (by omega) (by omega)
  sigm key h1 h2 := read_sigm P key (by omega) (by omega)

theorem sameLayer_of (P : Params) (w : LayerW) (L : ℕ) :
    SameLayer P L (layerWeightsOf P w L) w where
  Wq _ hj _ hc := mat_get _ hj hc
  Wk _ hj _ hc := mat_get _ hj hc
  Wv _ hj _ hc := mat_get _ hj hc
  Wo _ hj _ hc := mat_get _ hj hc
  Wg _ hj _ hc := mat_get _ hj hc
  Wu _ hj _ hc := mat_get _ hj hc
  Wd _ hj _ hc := mat_get _ hj hc
  Wr _ _ hj _ he := mat_get _ hj he
  Eg _ e he j hj c hc := by
    show ((((((tabl P.nexp fun e => gatedOf P.d P.fe (w.Eg e) (w.Eu e) (w.Ed e)).entry
          e)).gate.entry j)).entry c) = _
    rw [tabl_entry _ he]
    exact mat_get _ hj hc
  Eu _ e he j hj c hc := by
    show ((((((tabl P.nexp fun e => gatedOf P.d P.fe (w.Eg e) (w.Eu e) (w.Ed e)).entry e)).up.entry
        j)).entry c) = _
    rw [tabl_entry _ he]
    exact mat_get _ hj hc
  Ed _ e he j hj c hc := by
    show ((((((tabl P.nexp fun e => gatedOf P.d P.fe (w.Eg e) (w.Eu e) (w.Ed e)).entry
          e)).down.entry j)).entry c) = _
    rw [tabl_entry _ he]
    exact mat_get _ hj hc

theorem layer_get (P : Params) (pp : ScalesAndPolicy) {L : ℕ} (hL : L < P.layers) :
    ((settingsArrays P pp).perLayer.entry L) = layerSettingsOf (pp.kap L) L := tabl_entry _ hL
theorem wlayer_get (P : Params) (w : Inst.Model.Weights) {L : ℕ} (hL : L < P.layers) :
    ((weightsArrays P w).perLayer.entry L) = layerWeightsOf P (w.layer L) L := tabl_entry _ hL

theorem same_of (P : Params) (pp : ScalesAndPolicy) (w : Inst.Model.Weights) :
    Same P P.T pp.kap pp.nf (fun _ => tbRef) w (settingsArrays P pp)
      (tablesArrays P) (weightsArrays P w) where
  sizes := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  scales L hL := by
    rw [layer_get P pp hL]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl,
      fun _ => rfl, fun _ => rfl⟩
  finalBits := rfl
  finalShift := rfl
  finalEps := rfl
  tables L hL := by
    rw [layer_get P pp hL]
    exact sameTables_of P pp L
  layer L hL := by
    rw [wlayer_get P w hL]
    exact sameLayer_of P _ L
  emb a ha := tabl_entry _ ha
  head _ hj _ hv := mat_get _ hj hv

/-! ## The arrays pass `wellFormed`, for sizes with `FineSizes` and lawful scales -/

theorem hasSizes_gated (d h : ℕ) (g u dn : Mat) : (gatedOf d h g u dn).hasSizes d h = true := by
  unfold IntegerTransformer.GatedWeights.hasSizes gatedOf
  rw [hasSize_mat, hasSize_mat, hasSize_mat]
  rfl

theorem layerWellFormed_of (P : Params) (hn : 0 < P.nexp) (pp : ScalesAndPolicy) (hl : Lawful pp)
    (w : LayerW) {L : ℕ} (hL : L < 48) :
    IntegerTransformer.layerWellFormed (settingsArrays P pp) (layerSettingsOf (pp.kap L) L)
        (layerWeightsOf P w L) ((settingsArrays P pp).isMixture L) = true := by
  have hr : FFSeg.Ranges (pp.kap L) := by rw [kap_lt pp hL]; exact hl.ff ⟨L, hL⟩
  obtain ⟨-, -, -, -, a1, -, -⟩ := hr.n1
  obtain ⟨-, -, -, -, a2, -, -⟩ := hr.n2
  have q1 : IntegerTransformer.hasSize
        (settingsArrays P pp).width (settingsArrays P pp).queryWidth (layerWeightsOf P w L).query =
      true :=
    hasSize_mat _ _ _
  have q2 : IntegerTransformer.hasSize
        (settingsArrays P pp).width (settingsArrays P pp).keyValueWidth (layerWeightsOf P w L).key =
      true :=
    hasSize_mat _ _ _
  have q3 : IntegerTransformer.hasSize (settingsArrays P pp).width
        (settingsArrays P pp).keyValueWidth (layerWeightsOf P w L).value = true :=
    hasSize_mat _ _ _
  have q4 : IntegerTransformer.hasSize
        (settingsArrays P pp).queryWidth (settingsArrays P pp).width (layerWeightsOf P w L).output =
      true :=
    hasSize_mat _ _ _
  have z1 : decide (1 ≤ (layerSettingsOf (pp.kap L) L).attentionEps) = true :=
    decide_eq_true hr.n1.1
  have z2 : decide (1 ≤ (layerSettingsOf (pp.kap L) L).feedForwardEps) = true :=
    decide_eq_true hr.n2.1
  have s1 : decide (1 ≤ (layerSettingsOf (pp.kap L) L).attentionShift) = true :=
    decide_eq_true (show 1 ≤ (pp.kap L).n1.K by omega)
  have s2 : decide (1 ≤ (layerSettingsOf (pp.kap L) L).queryShift) = true :=
    decide_eq_true (show 1 ≤ (pp.kap L).kq by have := hr.kq; omega)
  have s3 : decide (1 ≤ (layerSettingsOf (pp.kap L) L).keyShift) = true :=
    decide_eq_true (show 1 ≤ (pp.kap L).kk by have := hr.kk; omega)
  have s4 : decide (1 ≤ (layerSettingsOf (pp.kap L) L).valueShift) = true := decide_eq_true hr.kv.1
  have s5 : decide (1 ≤ (layerSettingsOf (pp.kap L) L).outputShift) = true := decide_eq_true hr.ko.1
  have s6 : decide (1 ≤ (layerSettingsOf (pp.kap L) L).feedForwardShift) = true :=
    decide_eq_true (show 1 ≤ (pp.kap L).n2.K by omega)
  have s7 : decide (1 ≤ (layerSettingsOf (pp.kap L) L).gateShift) = true := decide_eq_true hr.kg.1
  have s8 : decide (1 ≤ (layerSettingsOf (pp.kap L) L).upShift) = true := decide_eq_true hr.ku.1
  have s9 : decide (1 ≤ (layerSettingsOf (pp.kap L) L).downShift) = true :=
    decide_eq_true (show 1 ≤ (pp.kap L).kd by have := hr.kd; omega)
  have s10 : decide (1 ≤ (layerSettingsOf (pp.kap L) L).routerShift) = true :=
    decide_eq_true (show 1 ≤ (pp.kap L).kr by have := hr.kr; omega)
  have s11 : decide (1 ≤ (layerSettingsOf (pp.kap L) L).routedGateShift) = true :=
    decide_eq_true hr.kg'.1
  have s12 : decide (1 ≤ (layerSettingsOf (pp.kap L) L).routedUpShift) = true :=
    decide_eq_true hr.ku'.1
  have hmix := isMixture_iff
    P L hn P.T (settingsArrays P pp) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold IntegerTransformer.layerWellFormed
  rw [q1, q2, q3, q4, z1, z2, s1, s2, s3, s4, s5, s6, s7, s8, s9]
  by_cases hE : hasExperts L
  · rw [hmix.2 hE, if_pos rfl, s10, s11, s12]
    have g1 : (layerWeightsOf P w L).shared.hasSizes
          (settingsArrays P pp).width (settingsArrays P pp).expertHidden = true := by
      show (gatedOf P.d (if hasExperts L then P.fe else P.f) w.Wg w.Wu w.Wd).hasSizes P.d P.fe =
        true
      rw [if_pos hE]
      exact hasSizes_gated _ _ _ _ _
    have g2 : IntegerTransformer.hasSize
          (settingsArrays P pp).width (settingsArrays P pp).experts (layerWeightsOf P w L).router =
        true :=
      hasSize_mat _ _ _
    have g3 : ((layerWeightsOf P w L).routed.size == (settingsArrays P pp).experts) = true := by
      show ((tabl P.nexp fun e => gatedOf P.d P.fe (w.Eg e) (w.Eu e) (w.Ed e)).size == P.nexp) =
        true
      rw [tabl_size]
      exact beq_self_eq_true _
    have g4 : ((layerWeightsOf P w L).routed.all fun expert =>
          expert.hasSizes (settingsArrays P pp).width (settingsArrays P pp).expertHidden) = true :=
      (tabl_all _ _ _).2 fun e _ => hasSizes_gated _ _ _ _ _
    rw [g1, g2, g3, g4]
    rfl
  · rw [Bool.eq_false_iff.2 fun a => hE (hmix.1 a), if_neg (by simp)]
    have g1 : (layerWeightsOf P w L).shared.hasSizes
          (settingsArrays P pp).width (settingsArrays P pp).hidden = true := by
      show (gatedOf P.d (if hasExperts L then P.fe else P.f) w.Wg w.Wu w.Wd).hasSizes P.d P.f = true
      rw [if_neg hE]
      exact hasSizes_gated _ _ _ _ _
    rw [g1]
    rfl

/-- The facts about the sizes that are used. The first seven are tests of `wellFormed`; `0 < nexp`
is required by `isMixture_iff` (IntegerModel/Readable/FeedForward.lean); a table of scales has 48
layers. -/
structure FineSizes (P : Params) : Prop where
  nkv : 0 < P.nkv
  nq : 0 < P.nq
  div : P.nq % P.nkv = 0
  ch : 0 < P.ch
  even : P.ch % 2 = 0
  V : 0 < P.V
  f : P.f = 2 * P.fe
  nexp : 0 < P.nexp
  layers : P.layers ≤ 48

theorem wellFormed_of (P : Params) (hP : FineSizes P) (pp : ScalesAndPolicy)
    (hl : Lawful pp) (w : Inst.Model.Weights) :
    IntegerTransformer.wellFormed (settingsArrays P pp) (tablesArrays P) (weightsArrays P w) =
      true := by
  have e3 : decide (1 ≤ (settingsArrays P pp).finalEps) = true := decide_eq_true hl.nf.1
  have e4 : decide (1 ≤ (settingsArrays P pp).finalShift) = true :=
    decide_eq_true (show 1 ≤ pp.nf.K by obtain ⟨-, -, -, -, a, -, -⟩ := hl.nf; omega)
  have t1 : IntegerTransformer.hasSize (settingsArrays P pp).positions
        ((settingsArrays P pp).headDim / 2) (tablesArrays P).cosine = true :=
    hasSize_mat _ _ _
  have t2 : IntegerTransformer.hasSize
        (settingsArrays P pp).positions ((settingsArrays P pp).headDim / 2) (tablesArrays P).sine =
      true :=
    hasSize_mat _ _ _
  have t3 : decide (0 < (tablesArrays P).exponential.size) = true :=
    decide_eq_true (by show 0 < (tabl 2307 fun u => refExp (u : ℤ)).size; rw [tabl_size]; norm_num)
  have t4 : decide (0 < ((tablesArrays P).exponential.entry 0)) = true := decide_eq_true (by
    show 0 < ((tabl 2307 fun u => refExp (u : ℤ)).entry 0)
    rw [tabl_entry _ (by norm_num)]
    show 0 < refExp 0
    rw [refExp_zero]
    norm_num)
  have t5 : ((tablesArrays P).exponential.all fun e => decide (0 ≤ e)) = true :=
    (tabl_all _ _ _).2 fun u _ => decide_eq_true (le_trans (by norm_num) (le_max_left (1 : ℤ) _))
  have t6 : (tablesArrays P).silu.covers (-32768) 32767 = true := by
    show (decide ((-32768 : ℤ) ≤ -32768) &&
        decide ((32767 : ℤ) <
            -32768 + ((tabl 65536 fun k => refSILU ((k : ℤ) - 32768 + 2 ^ 15)).size : ℕ))) = true
    rw [tabl_size]
    decide
  have t7 : (tablesArrays P).sigmoid.covers (-16384) 16383 = true := by
    show (decide ((-16384 : ℤ) ≤ -16384) &&
        decide ((16383 : ℤ) <
            -16384 + ((tabl 32768 fun k => refSIGM ((k : ℤ) - 16384 + 2 ^ 15)).size : ℕ))) = true
    rw [tabl_size]
    decide
  have w1 : IntegerTransformer.hasSize
        (settingsArrays P pp).vocabulary (settingsArrays P pp).width (weightsArrays P w).embedding =
      true :=
    hasSize_mat _ _ _
  have w2 : IntegerTransformer.hasSize
        (settingsArrays P pp).width (settingsArrays P pp).vocabulary (weightsArrays P w).head =
      true :=
    hasSize_mat _ _ _
  have l1 : ((settingsArrays P pp).perLayer.size == (settingsArrays P pp).layers) = true := by
    show ((tabl P.layers fun L => layerSettingsOf (pp.kap L) L).size == P.layers) = true
    rw [tabl_size]; exact beq_self_eq_true _
  have l2 : ((weightsArrays P w).perLayer.size == (settingsArrays P pp).layers) = true := by
    show ((tabl P.layers fun L => layerWeightsOf P (w.layer L) L).size == P.layers) = true
    rw [tabl_size]; exact beq_self_eq_true _
  have l3 : ((List.range (settingsArrays P pp).layers).all fun l =>
        IntegerTransformer.layerWellFormed (settingsArrays P pp)
          ((settingsArrays P pp).perLayer.entry l)
          ((weightsArrays P w).perLayer.entry l) ((settingsArrays P pp).isMixture l)) = true := by
    rw [List.all_eq_true]
    intro l hl'
    have hl2 : l < P.layers := List.mem_range.1 hl'
    rw [layer_get P pp hl2, wlayer_get P w hl2]
    exact layerWellFormed_of P hP.nexp pp hl _ (Nat.lt_of_lt_of_le hl2 hP.layers)
  have n1 : decide (0 < (settingsArrays P pp).keyValueHeads) = true := decide_eq_true hP.nkv
  have n2 : decide (0 < (settingsArrays P pp).queryHeads) = true := decide_eq_true hP.nq
  have n3 : ((settingsArrays P pp).queryHeads % (settingsArrays P pp).keyValueHeads == 0) = true :=
    beq_iff_eq.2 hP.div
  have n4 : decide (0 < (settingsArrays P pp).headDim) = true := decide_eq_true hP.ch
  have n5 : ((settingsArrays P pp).headDim % 2 == 0) = true := beq_iff_eq.2 hP.even
  have n6 : decide (0 < (settingsArrays P pp).vocabulary) = true := decide_eq_true hP.V
  have n7 : ((settingsArrays P pp).hidden == 2 * (settingsArrays P pp).expertHidden) = true :=
    beq_iff_eq.2 hP.f
  unfold IntegerTransformer.wellFormed
  rw [n1, n2, n3, n4, n5, n6, n7, e3, e4, t1, t2, t3, t4, t5, t6, t7, w1, w2,
    l1, l2, l3, Bool.or_true]
  rfl

theorem fine_ref : FineSizes ppref :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

/-- For every `m` the arrays satisfy `Feeds m`, so that hypothesis can be met for every `m`. -/
theorem feeds_of (m : IntegerModel.Committed) :
    Feeds m (settingsArrays ppref m.settings)
      (tablesArrays ppref) (weightsArrays ppref m.weights.val) :=
  ⟨same_of ppref _ _, wellFormed_of ppref fine_ref _ m.lawful _⟩

end IntegerModel.Readable
