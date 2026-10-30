-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Readable/Attention.lean: the attention of IntegerModel/Model.lean (its part 4, and the
conditions of part 7 on it) shown equal to Att.* of Inst/Model/Program.lean, under the hypotheses of
the statements: att_out (the stream after attention), attentionOk_iff (the range conditions).
-/
import IntegerModel.Readable.Helpers

set_option autoImplicit false

namespace IntegerModel.Readable

open Inst.Model IntegerModel.Runnable

section Block
variable (P : Params) (hP : IntegerModel.Runnable.Good P) (Tmax : ℕ) (tb : Tables)
  (w : LayerW) (L : ℕ) (x : ℕ → Vec)

/-- the library's queries, keys and values of one position, as the model's record -/
def projRec (t : ℕ) : IntegerTransformer.Projections :=
  { queryProducts := tabl (Att.dq P) (Att.Aq P w x t),
    keyProducts := tabl (P.nkv * P.ch) (Att.Ak P w x t),
    rotatedQuery := tabl (Att.dq P) (Att.Y' P tb w L x t),
    rotatedKey := tabl (P.nkv * P.ch) fun c => Att.Y' P tb w L x t (Att.dq P + c),
    wideQuery := tabl (Att.dq P) (Att.qkw P tb w L x t),
    wideKey := tabl (P.nkv * P.ch) fun c => Att.qkw P tb w L x t (Att.dq P + c),
    query := tabl (Att.dq P) (Att.q P tb w L x t), key := tabl (P.nkv * P.ch) (Att.kx P tb w L x t),
    wideValue := tabl (P.nkv * P.ch) (Att.vw P w x t),
    value := tabl (P.nkv * P.ch) (Att.v P w x t) }

variable (s : IntegerTransformer.Settings) (hs : SameSizes P Tmax s)
  (p : IntegerTransformer.LayerSettings) (hp : SameScales L p P.scale)
  (tables : IntegerTransformer.Tables) (hT : SameTables P Tmax s p tables tb L P.expRows)
  (W : IntegerTransformer.LayerWeights) (hW : SameLayer P L W w)

include hs in
theorem queryWidth_eq : s.queryWidth = Att.dq P := by
  unfold IntegerTransformer.Settings.queryWidth Att.dq
  rw [hs.queryHeads, hs.headDim]
include hs in
theorem keyValueWidth_eq : s.keyValueWidth = P.nkv * P.ch := by
  unfold IntegerTransformer.Settings.keyValueWidth
  rw [hs.keyValueHeads, hs.headDim]

include hP hs hp hT hW in
theorem projections_eq {t : ℕ} (ht : t < Tmax) :
    IntegerTransformer.projections s p tables W t (tabl P.d (Att.a P x t)) =
      projRec P tb w L x t := by
  have hC : ∀ j < P.ch / 2,
      ((if p.rotary = true then (tables.cosine.entry t)
          else IntegerTransformer.tabulate (P.ch / 2) fun _ => 2 ^ s.rotaryScale).entry j) =
        tb.C L t j := by
    intro j hj
    rw [← hT.cos t ht j hj]
    by_cases hr : p.rotary = true
    · rw [if_pos hr, if_pos hr]
    · rw [if_neg hr, if_neg hr, tabulate_eq, tabl_entry _ hj]
  have hS : ∀ j < P.ch / 2,
      ((if p.rotary = true then (tables.sine.entry t)
          else IntegerTransformer.tabulate (P.ch / 2) fun _ => 0).entry j) = tb.S L t j := by
    intro j hj
    rw [← hT.sin t ht j hj]
    by_cases hr : p.rotary = true
    · rw [if_pos hr, if_pos hr]
    · rw [if_neg hr, if_neg hr, tabulate_eq, tabl_entry _ hj]
  have e1 : IntegerTransformer.product (tabl P.d (Att.a P x t)) W.query (Att.dq P) =
      tabl (Att.dq P) (Att.Aq P w x t) :=
    product_same _ _ _ _ w.Wq hW.Wq
  have e2 : IntegerTransformer.product (tabl P.d (Att.a P x t)) W.key (P.nkv * P.ch) =
      tabl (P.nkv * P.ch) (Att.Ak P w x t) :=
    product_same _ _ _ _ w.Wk hW.Wk
  have e3 : IntegerTransformer.product (tabl P.d (Att.a P x t)) W.value (P.nkv * P.ch) =
      tabl (P.nkv * P.ch) (Att.Av P w x t) :=
    product_same _ _ _ _ w.Wv hW.Wv
  have r1 := (rotate_tabl _ _ P.ch (Att.dq P) hP.ch ⟨P.nq, Nat.mul_comm _ _⟩ (Att.Aq P w x t)
      (tb.C L t) (tb.S L t) hC hS).trans
    (tabl_congr fun c hc => (Y'_q P hP tb w L x hc).symm)
  have r2 := (rotate_tabl _ _ P.ch (P.nkv * P.ch) hP.ch ⟨P.nkv, Nat.mul_comm _ _⟩ (Att.Ak P w x t)
      (tb.C L t) (tb.S L t) hC hS).trans
    (tabl_congr fun c _ => (Y'_k P tb w L x t c).symm)
  have w1 : (tabl (Att.dq P) (Att.Y' P tb w L x t)).map
        (fun e => IntegerTransformer.roundShift e p.queryShift) =
      tabl (Att.dq P) (Att.qkw P tb w L x t) := by
    rw [tabl_map, hp.kq]
    exact tabl_congr fun c hc => by unfold Att.qkw; rw [if_pos hc]; rfl
  have w2 : (tabl (P.nkv * P.ch) fun c => Att.Y' P tb w L x t (Att.dq P + c)).map
        (fun e => IntegerTransformer.roundShift e p.keyShift) =
      tabl (P.nkv * P.ch) fun c => Att.qkw P tb w L x t (Att.dq P + c) := by
    rw [tabl_map, hp.kk]
    exact tabl_congr fun c _ => by
      unfold Att.qkw; rw [if_neg (show ¬ Att.dq P + c < Att.dq P by omega)]; rfl
  have w3 : (tabl (P.nkv * P.ch) (Att.Av P w x t)).map
        (fun e => IntegerTransformer.roundShift e p.valueShift) =
      tabl (P.nkv * P.ch) (Att.vw P w x t) := by
    rw [tabl_map, hp.kv]; rfl
  unfold IntegerTransformer.projections projRec
  simp only [queryWidth_eq P Tmax s hs, keyValueWidth_eq P Tmax s hs, hs.headDim, e1, e2, e3, r1,
    r2, w1, w2, w3, tabl_map]
  rfl

include hP hs hp hT in
/-- one head at one position: its result -/
theorem head_out {i h : ℕ} (hi : i < P.T) (hh : h < P.nq) :
    (IntegerTransformer.attendHead s p tables (tabl P.T (projRec P tb w L x)) i h).out =
      tabl P.ch fun n =>
        (2 * Att.ac P tb w L x h i n + Att.den P tb w L x h i) / (2 * Att.den P tb w L x h i) := by
  have hg := kv_lt hP hh
  have hrec : ∀ j, j < i + 1 → ((tabl P.T (projRec P tb w L x)).entry j) = projRec P tb w L x j :=
    fun j hj => tabl_entry _ (Nat.lt_of_lt_of_le hj hi)
  have eS : IntegerTransformer.tabulate (i + 1) (fun j =>
        IntegerTransformer.sumOver P.ch fun c =>
          (((tabl P.T (projRec P tb w L x)).entry i).query.entry (h * P.ch + c)) *
            (((tabl P.T (projRec P tb w L x)).entry j).key.entry (h / (P.nq / P.nkv) * P.ch + c))) =
      tabl (i + 1) (Att.sc P tb w L x h i) := by
    rw [tabulate_eq]
    refine tabl_congr fun j hj => ?_
    rw [sumOver_eq, hrec i (Nat.lt_succ_self i), hrec j hj]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' := Finset.mem_range.1 hn
    show ((tabl (Att.dq P) (Att.q P tb w L x i)).entry (h * P.ch + n)) *
        ((tabl (P.nkv * P.ch) (Att.kx P tb w L x j)).entry (Att.kvOf P h * P.ch + n)) = _
    rw [Nat.mul_comm h, Nat.mul_comm (Att.kvOf P h),
      tabl_entry (n := Att.dq P) _ (idx_lt hh hn'), tabl_entry _ (idx_lt hg hn')]
  have eT : IntegerTransformer.maxUpTo
        (fun j => ((tabl (i + 1) (Att.sc P tb w L x h i)).entry j)) i =
      Att.mx P tb w L x h i := by
    rw [maxUpTo_eq]
    exact maxTo_congr' i fun j hj => tabl_entry _ (Nat.lt_succ_of_le hj)
  have eD : (tabl (i + 1) (Att.sc P tb w L x h i)).map
        (fun sj => (Att.mx P tb w L x h i - sj) / 2 ^ p.softmaxShift) =
      tabl (i + 1) (Att.u P tb w L x h i) := by
    rw [tabl_map, hp.sh]; rfl
  have eW : (tabl (i + 1) (Att.u P tb w L x h i)).map (fun (u : ℤ) =>
        if u < (tables.exponential.size : ℤ) then (tables.exponential.entry u.toNat) else 0) =
      tabl (i + 1) (Att.wt P tb w L x h i) := by
    rw [tabl_map]
    refine tabl_congr fun j hj => ?_
    have h0 : 0 ≤ Att.u P tb w L x h i j :=
      Int.ediv_nonneg (sub_nonneg.2
          ((maxTo_spec (Att.sc P tb w L x h i) i).1 j (Nat.le_of_lt_succ hj))) (by positivity)
    unfold Att.wt
    rw [hT.rows]
    by_cases hu : Att.u P tb w L x h i j < P.expRows
    · rw [if_pos hu, if_pos hu, hT.exp _ (by have := hT.rows; omega), Int.toNat_of_nonneg h0]
    · rw [if_neg hu, if_neg hu]
  have eZ : IntegerTransformer.sumOver
        (i + 1) (fun j => ((tabl (i + 1) (Att.wt P tb w L x h i)).entry j)) =
      Att.den P tb w L x h i := by
    rw [sumOver_eq]
    exact Finset.sum_congr rfl fun j hj => tabl_entry _ (Finset.mem_range.1 hj)
  have eM : IntegerTransformer.tabulate P.ch (fun c =>
        IntegerTransformer.sumOver (i + 1) fun j =>
          ((tabl (i + 1) (Att.wt P tb w L x h i)).entry j) *
            (((tabl P.T (projRec P tb w L x)).entry j).value.entry
              (h / (P.nq / P.nkv) * P.ch + c))) =
      tabl P.ch (Att.ac P tb w L x h i) := by
    rw [tabulate_eq]
    refine tabl_congr fun n hn => ?_
    rw [sumOver_eq]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [tabl_entry _ hj', hrec j hj']
    show _ * ((tabl (P.nkv * P.ch) (Att.v P w x j)).entry (Att.kvOf P h * P.ch + n)) = _
    rw [Nat.mul_comm (Att.kvOf P h), tabl_entry _ (idx_lt hg hn)]
  unfold IntegerTransformer.attendHead
  simp only [hs.headDim, hs.queryHeads, hs.keyValueHeads, eS, eT, eD, eW, eZ, eM, tabl_map]

/-- the stream as the model takes it -/
abbrev rows (T d : ℕ) (x : ℕ → Vec) : Array (Array ℤ) := tabl T fun t => tabl d (x t)

include hp in
theorem att_norm :
    (IntegerTransformer.attention s p tables W (rows P.T P.d x)).norm =
      tabl P.T fun t => normRec P.n1 P.d (x t) := by
  show (rows P.T P.d x).map
      (fun row => IntegerTransformer.rmsNorm p.attentionBits p.attentionShift p.attentionEps row) =
    _
  rw [tabl_map]
  exact tabl_congr fun t _ => rmsNorm_eq P.n1 P.d (x t) hp.M1 hp.K1 hp.eps1

include hP hs hp hT hW in
theorem att_projected (hTm : P.T ≤ Tmax) :
    (IntegerTransformer.attention s p tables W (rows P.T P.d x)).projected =
      tabl P.T (projRec P tb w L x) := by
  show IntegerTransformer.tabulate (rows P.T P.d x).size (fun t =>
      IntegerTransformer.projections s p tables W t
        ((IntegerTransformer.attention s p tables W (rows P.T P.d x)).norm.entry t).out) = _
  rw [tabulate_eq, tabl_size, att_norm P L x s p hp tables W]
  refine tabl_congr fun t ht => ?_
  rw [tabl_entry _ ht]
  exact projections_eq P hP Tmax tb w L x s hs p hp tables hT W hW (Nat.lt_of_lt_of_le ht hTm)

include hP hs hp hT hW in
theorem att_out (hTm : P.T ≤ Tmax) :
    (IntegerTransformer.attention s p tables W (rows P.T P.d x)).out =
      rows P.T P.d (Att.x' P tb w L x) := by
  have hpr := att_projected P hP Tmax tb w L x s hs p hp tables hT W hW hTm
  have hheads : IntegerTransformer.tabulate (rows P.T P.d x).size (fun i =>
    IntegerTransformer.tabulate s.queryHeads fun h =>
      IntegerTransformer.attendHead
        s p tables (IntegerTransformer.attention s p tables W (rows P.T P.d x)).projected i h)
      = tabl P.T fun i =>
          tabl P.nq fun h =>
              IntegerTransformer.attendHead s p tables (tabl P.T (projRec P tb w L x)) i h := by
    rw [tabulate_eq, tabl_size, hpr, hs.queryHeads]
    exact tabl_congr fun i _ => tabulate_eq _ _
  have hmixed : IntegerTransformer.tabulate (rows P.T P.d x).size (fun i =>
    IntegerTransformer.tabulate s.queryWidth fun j =>
      (((((tabl P.T fun i =>
            tabl P.nq fun h =>
              IntegerTransformer.attendHead
                s p tables (tabl P.T (projRec P tb w L x)) i h).entry i)).entry
          (j / s.headDim)).out.entry
        (j % s.headDim)))
      = tabl P.T fun i => tabl (Att.dq P) (Att.o P tb w L x i) := by
    rw [tabulate_eq, tabl_size, queryWidth_eq P Tmax s hs, hs.headDim]
    refine tabl_congr fun i hi => ?_
    rw [tabulate_eq]
    refine tabl_congr fun j hj => ?_
    have hch : 0 < P.ch := by
      rcases Nat.eq_zero_or_pos P.ch with h | h
      · unfold Att.dq at hj; rw [h] at hj; simp at hj
      · exact h
    have hh : j / P.ch < P.nq := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj)
    rw [tabl_entry _ hi, tabl_entry _ hh,
      head_out P hP Tmax tb w L x s hs p hp tables hT hi hh, tabl_entry _ (Nat.mod_lt j hch)]
    rfl
  have hadd : (tabl P.T fun i => tabl (Att.dq P) (Att.o P tb w L x i)).map
        (fun o =>
          (IntegerTransformer.product o W.output s.width).map fun e =>
            IntegerTransformer.roundShift e p.outputShift) =
      tabl P.T fun i =>
        tabl P.d fun c => rhu (dot (Att.dq P) (Att.o P tb w L x i) fun j => w.Wo j c) P.ko := by
    rw [tabl_map, hs.width, hp.ko]
    refine tabl_congr fun i _ => ?_
    rw [product_same (Att.dq P) _ _ _ w.Wo hW.Wo, tabl_map]
    rfl
  show IntegerTransformer.tabulate (rows P.T P.d x).size (fun t =>
      IntegerTransformer.addVectors ((rows P.T P.d x).entry t)
        (((IntegerTransformer.tabulate (rows P.T P.d x).size (fun i =>
            IntegerTransformer.tabulate s.queryWidth fun j =>
              (((((IntegerTransformer.tabulate (rows P.T P.d x).size (fun i =>
                    IntegerTransformer.tabulate s.queryHeads fun h =>
                      IntegerTransformer.attendHead s p tables
                        (IntegerTransformer.attention s p tables W (rows P.T P.d x)).projected
                        i h)).entry i)).entry
                  (j / s.headDim)).out.entry
                (j % s.headDim)))).map
          (fun o =>
            (IntegerTransformer.product o W.output s.width).map fun e =>
              IntegerTransformer.roundShift e p.outputShift)).entry t)) = _
  rw [hheads, hmixed, hadd, tabulate_eq, tabl_size]
  refine tabl_congr fun t ht => ?_
  rw [tabl_entry _ ht, tabl_entry _ ht, addVec_tabl]
  rfl

include hP hs hp hT hW in
/-- the conditions of the layer's attention at position t -/
theorem attentionOk_iff (hTm : P.T ≤ Tmax) {t : ℕ} (ht : t < P.T) :
    IntegerTransformer.attentionOk
        p (IntegerTransformer.attention s p tables W (rows P.T P.d x)) t = true ↔
    NORM.OK P.n1 P.d (x t) ∧
    (∀ c < Att.dq P + P.nkv * P.ch, Fits16 (Att.qkw P tb w L x t c)) ∧
    ∀ c < P.nkv * P.ch, Fits16 (Att.vw P w x t c) := by
  unfold IntegerTransformer.attentionOk
  rw [att_norm P L x s p hp tables W, att_projected P hP Tmax tb w L x s hs p hp tables hT W hW hTm,
    tabl_entry _ ht, tabl_entry _ ht]
  simp only [Bool.and_eq_true]
  rw [normOk_iff P.n1 P.d (x t) hp.eps1]
  show ((_ ∧ IntegerTransformer.fits16 (tabl (Att.dq P) (Att.qkw P tb w L x t)) = true) ∧
        IntegerTransformer.fits16
            (tabl (P.nkv * P.ch) fun c => Att.qkw P tb w L x t (Att.dq P + c)) = true) ∧
      IntegerTransformer.fits16 (tabl (P.nkv * P.ch) (Att.vw P w x t)) = true ↔
    _
  rw [fits16_tabl, fits16_tabl, fits16_tabl]
  constructor
  · rintro ⟨⟨⟨a, b⟩, c⟩, d⟩
    refine ⟨a, fun e he => ?_, d⟩
    by_cases hlt : e < Att.dq P
    · exact b e hlt
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hlt)
      exact c k (by omega)
  · rintro ⟨a, b, d⟩
    exact ⟨⟨⟨a, fun e he => b e (by omega)⟩, fun e he => b _ (by omega)⟩, d⟩

end Block

end IntegerModel.Readable
