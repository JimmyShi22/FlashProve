-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Readable/Main.lean: the equations between IntegerTransformer.model
(IntegerModel/Model.lean) and the library's program (XK, lgK, RunsK: Inst/Model/Program.lean):
layers, embedding, head, the range conditions, the model; for all sizes with the three side
conditions of Good P (IntegerModel/Runnable/Defs.lean), under hypotheses (see the statements).
-/
import IntegerModel.Readable.Attention
import IntegerModel.Readable.FeedForward
import IntegerModel.Runnable.Main

set_option autoImplicit false

namespace IntegerModel.Readable

open Inst.Model IntegerModel.Runnable

theorem tabl_succ {α : Type} (n : ℕ) (f : ℕ → α) : tabl (n + 1) f = (tabl n f).push (f n) := by
  simp [tabl, Array.range_succ]

section General
variable (P : Params) (hP : IntegerModel.Runnable.Good P) (Tmax : ℕ) (hTm : P.T ≤ Tmax)
  (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) (w : Weights)
  (s : IntegerTransformer.Settings) (tables : IntegerTransformer.Tables)
  (weights : IntegerTransformer.Weights) (h : Same P Tmax κ nf tbs w s tables weights)

section Layer
variable {L : ℕ} (hL : L < P.layers) (x : ℕ → Vec)
include hP hTm h hL

theorem layer_ff :
    (IntegerTransformer.layer s tables weights L (rows P.T P.d x)).feedForward =
      tabl P.T fun t =>
        IntegerTransformer.feedForward s (s.perLayer.entry L) tables (weights.perLayer.entry L)
            (s.isMixture L) (tabl P.d (Att.x' (P.at (κ L)) (tbs L) (w.layer L) L x t)) := by
  show (IntegerTransformer.attention
      s (s.perLayer.entry L) tables (weights.perLayer.entry L) (rows P.T P.d x)).out.map _ = _
  have e : (IntegerTransformer.attention
        s (s.perLayer.entry L) tables (weights.perLayer.entry L) (rows P.T P.d x)).out =
      rows P.T P.d (Att.x' (P.at (κ L)) (tbs L) (w.layer L) L x) :=
    att_out (P.at (κ L)) ⟨hP.ch, hP.kv, hP.nexp⟩ Tmax (tbs L) (w.layer L) L x s (h.sizes.at _)
      (s.perLayer.entry L) (h.scales L hL) tables ((h.tables L hL).at _) (weights.perLayer.entry L)
      ((h.layer L hL).at _) hTm
  rw [e]
  exact tabl_map _ _ _

theorem layer_out :
    (IntegerTransformer.layer s tables weights L (rows P.T P.d x)).out =
      rows P.T P.d
        (FF.x'' (P.at (κ L)) (tbs L) (w.layer L) L
          (Att.x' (P.at (κ L)) (tbs L) (w.layer L) L x)) := by
  show (IntegerTransformer.layer s tables weights L (rows P.T P.d x)).feedForward.map
      (fun ff => ff.out) = _
  rw [layer_ff P hP Tmax hTm κ nf tbs w s tables weights h hL x, tabl_map]
  exact tabl_congr fun t _ =>
    ff_out (P.at (κ L)) (tbs L) (w.layer L) L _ t hP.nexp Tmax s (h.sizes.at _) (s.perLayer.entry L)
      (h.scales L hL) tables ((h.tables L hL).at _) (weights.perLayer.entry L) ((h.layer L hL).at _)

end Layer

variable (prompt : Fin P.T → Fin P.V)

include h in
theorem embedded_eq :
    ((Array.ofFn fun i => (prompt i).val).map fun token => (weights.embedding.entry token)) =
      rows P.T P.d (XK P κ tbs w prompt 0) := by
  apply Array.ext
  · simp
  · intro i h1 _
    have hi : i < P.T := by simpa using h1
    simp only [Array.getElem_map, Array.getElem_ofFn, Array.getElem_range]
    rw [h.emb _ (prompt ⟨i, hi⟩).isLt]
    refine tabl_congr fun j _ => ?_
    show _ = if h : i < P.T then w.Emb (prompt ⟨i, h⟩) j else 0
    rw [dif_pos hi]

include hP hTm h in
/-- the first n layers, and the stream above them -/
theorem firstLayers_eq :
    ∀ n ≤ P.layers,
      IntegerTransformer.firstLayers s tables weights (rows P.T P.d (XK P κ tbs w prompt 0)) n =
        (tabl n fun l =>
          IntegerTransformer.layer s tables weights l
            (rows P.T P.d (XK P κ tbs w prompt (2 * l)))) ∧
      IntegerTransformer.streamAbove (rows P.T P.d (XK P κ tbs w prompt 0))
          (IntegerTransformer.firstLayers
            s tables weights (rows P.T P.d (XK P κ tbs w prompt 0)) n) =
        rows P.T P.d (XK P κ tbs w prompt (2 * n))
  | 0, _ => ⟨by simp [IntegerTransformer.firstLayers, tabl], rfl⟩
  | n + 1, hn => by
      obtain ⟨a, b⟩ := firstLayers_eq n (Nat.le_of_succ_le hn)
      have e : IntegerTransformer.firstLayers
            s tables weights (rows P.T P.d (XK P κ tbs w prompt 0)) (n + 1) =
          (tabl n fun l =>
              IntegerTransformer.layer s tables weights l
                (rows P.T P.d (XK P κ tbs w prompt (2 * l)))).push
            (IntegerTransformer.layer s tables weights n
              (rows P.T P.d (XK P κ tbs w prompt (2 * n)))) := by
        show (IntegerTransformer.firstLayers s tables weights _ n).push
            (IntegerTransformer.layer s tables weights n
              (IntegerTransformer.streamAbove
                _ (IntegerTransformer.firstLayers s tables weights _ n))) = _
        rw [b, a]
      refine ⟨e.trans (tabl_succ n _).symm, ?_⟩
      rw [e]
      unfold IntegerTransformer.streamAbove
      rw [Array.back?_push]
      show (IntegerTransformer.layer
          s tables weights n (rows P.T P.d (XK P κ tbs w prompt (2 * n)))).out = _
      rw [layer_out P hP Tmax hTm κ nf tbs w s tables weights h (Nat.lt_of_succ_le hn), ← XK_att,
        ← XK_ff]

/-- the prompt as the model takes it -/
abbrev toks : Array ℕ := Array.ofFn fun i => (prompt i).val

include hP hTm h

theorem trace_layer :
    (IntegerTransformer.trace s tables weights (toks P prompt)).layer =
      tabl P.layers fun l =>
        IntegerTransformer.layer s tables weights l
            (rows P.T P.d (XK P κ tbs w prompt (2 * l))) := by
  show IntegerTransformer.firstLayers
      s tables weights ((toks P prompt).map fun token => (weights.embedding.entry token)) s.layers =
    _
  rw [embedded_eq P Tmax κ nf tbs w s tables weights h prompt, h.sizes.layers]
  exact (firstLayers_eq P hP Tmax hTm κ nf tbs w s tables weights h prompt P.layers le_rfl).1

theorem trace_finalNorm :
    (IntegerTransformer.trace s tables weights (toks P prompt)).finalNorm =
      tabl P.T fun t => normRec nf P.d (XK P κ tbs w prompt (2 * P.layers) t) := by
  show (IntegerTransformer.streamAbove
      ((toks P prompt).map fun token => (weights.embedding.entry token))
      (IntegerTransformer.firstLayers s tables weights
        ((toks P prompt).map fun token => (weights.embedding.entry token)) s.layers)).map _ = _
  rw [embedded_eq P Tmax κ nf tbs w s tables weights h prompt, h.sizes.layers,
    (firstLayers_eq P hP Tmax hTm κ nf tbs w s tables weights h prompt P.layers le_rfl).2, tabl_map]
  exact tabl_congr fun t _ => rmsNorm_eq nf P.d _ h.finalBits h.finalShift h.finalEps

theorem trace_choices :
    (IntegerTransformer.trace s tables weights (toks P prompt)).choices =
      tabl P.T fun t => argTo (lgK P κ nf tbs w prompt t) (P.V - 1) := by
  show (((IntegerTransformer.trace s tables weights (toks P prompt)).finalNorm.map
        fun n => IntegerTransformer.product n.out weights.head s.vocabulary).map
      fun lam => IntegerTransformer.firstArgmax (fun v => (lam.entry v)) s.vocabulary) = _
  rw [trace_finalNorm P hP Tmax hTm κ nf tbs w s tables weights h prompt, tabl_map,
    tabl_map, h.sizes.vocabulary]
  refine tabl_congr fun t _ => ?_
  show IntegerTransformer.firstArgmax
      (fun v =>
        ((IntegerTransformer.product
          (tabl P.d (NORM.out nf P.d (XK P κ tbs w prompt (2 * P.layers) t)))
          weights.head P.V).entry v)) P.V = _
  rw [product_same _ _ _ _ w.H h.head, firstArgmax_eq]
  cases hV : P.V with
  | zero => rfl
  | succ n => exact argTo_congr n fun j hj => tabl_entry _ (Nat.lt_succ_of_le hj)

/-- Under hP, hTm and h (the variable lines above), on the trace of the prompt: the model's one Bool
for all range conditions is the library's RunsK. -/
theorem allConditionsHold_iff :
    IntegerTransformer.allConditionsHold
        s (IntegerTransformer.trace s tables weights (toks P prompt)) = true ↔
    RunsK P κ nf tbs w prompt := by
  have hsz : (IntegerTransformer.trace s tables weights (toks P prompt)).embedded.size = P.T := by
    show ((toks P prompt).map _).size = P.T
    simp
  unfold IntegerTransformer.allConditionsHold
  rw [hsz, h.sizes.layers, trace_layer P hP Tmax hTm κ nf tbs w s tables weights h prompt,
    trace_finalNorm P hP Tmax hTm κ nf tbs w s tables weights h prompt]
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true]
  have key : ∀ t < P.T, ∀ l < P.layers,
      (IntegerTransformer.attentionOk (s.perLayer.entry l)
            ((tabl P.layers fun l =>
                IntegerTransformer.layer s tables weights l
                  (rows P.T P.d (XK P κ tbs w prompt (2 * l)))).entry l).attention t = true ∧
        IntegerTransformer.feedForwardOk (s.perLayer.entry l)
            (((tabl P.layers fun l =>
                IntegerTransformer.layer s tables weights l
                  (rows P.T P.d (XK P κ tbs w prompt (2 * l)))).entry
              l).feedForward.entry t) = true) ↔
      ((NORM.OK (P.at (κ l)).n1 P.d (XK P κ tbs w prompt (2 * l) t) ∧
          (∀ c < Att.dq (P.at (κ l)) + P.nkv * P.ch,
            Fits16 (Att.qkw (P.at (κ l)) (tbs l) (w.layer l) l (XK P κ tbs w prompt (2 * l)) t c)) ∧
          ∀ c < P.nkv * P.ch,
            Fits16 (Att.vw (P.at (κ l)) (w.layer l) (XK P κ tbs w prompt (2 * l)) t c)) ∧
        (NORM.OK (P.at (κ l)).n2 P.d (XK P κ tbs w prompt (2 * l + 1) t) ∧
          (hasExperts l →
            ∀ e < P.nexp,
              Fits16 (FF.ly (P.at (κ l)) (w.layer l) (XK P κ tbs w prompt (2 * l + 1)) t e)) ∧
          ∀ j < FF.units (P.at (κ l)) l,
            UNIT.OK P.d
              (FF.z (P.at (κ l)) (tbs l) (w.layer l) l (XK P κ tbs w prompt (2 * l + 1)) t j)
              (FF.wg (P.at (κ l)) (w.layer l) l (XK P κ tbs w prompt (2 * l + 1)) t j)
              (FF.wu (P.at (κ l)) (w.layer l) l (XK P κ tbs w prompt (2 * l + 1)) t j)
              (FF.kG (P.at (κ l)) l j) (FF.kU (P.at (κ l)) l j))) := by
    intro t ht l hl
    rw [tabl_entry _ hl, layer_ff P hP Tmax hTm κ nf tbs w s tables weights h hl,
      tabl_entry _ ht, ← XK_att]
    exact and_congr
      (attentionOk_iff (P.at (κ l)) ⟨hP.ch, hP.kv, hP.nexp⟩ Tmax (tbs l) (w.layer l) l _ s
        (h.sizes.at _) (s.perLayer.entry l) (h.scales l hl) tables ((h.tables l hl).at _)
        (weights.perLayer.entry l) ((h.layer l hl).at _) hTm ht)
      (feedForwardOk_iff (P.at (κ l)) (tbs l) (w.layer l) l _ t hP.nexp Tmax s (h.sizes.at _)
        (s.perLayer.entry l) (h.scales l hl) tables ((h.tables l hl).at _)
        (weights.perLayer.entry l) ((h.layer l hl).at _))
  constructor
  · intro a
    refine ⟨fun l hl =>
        ⟨fun t ht => ((key t ht l hl).1 ((a t ht).1 l hl)).1,
          fun t ht => ((key t ht l hl).1 ((a t ht).1 l hl)).2⟩,
      fun t ht => ?_⟩
    have := (a t ht).2
    rw [tabl_entry _ ht] at this
    exact (normOk_iff nf P.d _ h.finalEps).1 this
  · rintro ⟨a, b⟩ t ht
    refine ⟨fun l hl => (key t ht l hl).2 ⟨(a l hl).1 t ht, (a l hl).2 t ht⟩, ?_⟩
    rw [tabl_entry _ ht]
    exact (normOk_iff nf P.d _ h.finalEps).2 (b t ht)

end General

section Model
variable (P : Params) (hP : IntegerModel.Runnable.Good P) (Tmax : ℕ) (κ : ℕ → LayerScale)
  (nf : NormPar) (tbs : ℕ → Tables) (w : Weights) (s : IntegerTransformer.Settings)
  (tables : IntegerTransformer.Tables) (weights : IntegerTransformer.Weights)
  (h : Same P Tmax κ nf tbs w s tables weights) (prompt : Fin P.T → Fin P.V)
include hP h

omit hP in
theorem isPrompt_iff :
    IntegerTransformer.isPrompt s (toks P prompt) = true ↔ 0 < P.T ∧ P.T ≤ Tmax := by
  have hall : ((toks P prompt).all fun token => decide (token < s.vocabulary)) = true := by
    rw [← Array.all_toList, List.all_eq_true]
    intro a ha
    obtain ⟨i, rfl⟩ : ∃ i, (prompt i).val = a := by simpa [List.mem_ofFn] using ha
    rw [h.sizes.vocabulary]
    exact decide_eq_true (prompt i).isLt
  unfold IntegerTransformer.isPrompt
  rw [hall, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    Array.size_ofFn, h.sizes.positions]

theorem model_is :
    Is (IntegerTransformer.model s tables weights (toks P prompt))
      (IntegerTransformer.wellFormed s tables weights = true ∧
        0 < P.T ∧ P.T ≤ Tmax ∧ RunsK P κ nf tbs w prompt)
      (argTo (lgK P κ nf tbs w prompt (P.T - 1)) (P.V - 1)) := by
  unfold IntegerTransformer.model
  by_cases hg : IntegerTransformer.wellFormed s tables weights = true ∧ 0 < P.T ∧ P.T ≤ Tmax
  · have hp := (isPrompt_iff P Tmax κ nf tbs w s tables weights h prompt).2 hg.2
    rw [if_pos (by rw [hg.1, hp]; rfl)]
    have hr := allConditionsHold_iff P hP Tmax hg.2.2 κ nf tbs w s tables weights h prompt
    by_cases hR : RunsK P κ nf tbs w prompt
    · refine ⟨fun _ => ?_, fun a => absurd ⟨hg.1, hg.2.1, hg.2.2, hR⟩ a⟩
      show (if IntegerTransformer.allConditionsHold
                s (IntegerTransformer.trace s tables weights (toks P prompt)) = true then
            some ((IntegerTransformer.trace s tables weights (toks P prompt)).choices.entry
                ((toks P prompt).size - 1))
          else none) = _
      rw [if_pos (hr.2 hR), trace_choices P hP Tmax hg.2.2 κ nf tbs w s tables weights h prompt,
        Array.size_ofFn, tabl_entry _ (by omega : P.T - 1 < P.T)]
    · refine ⟨fun a => absurd a.2.2.2 hR, fun _ => ?_⟩
      show (if IntegerTransformer.allConditionsHold
                s (IntegerTransformer.trace s tables weights (toks P prompt)) = true then _
          else none) = none
      rw [if_neg fun a => hR (hr.1 a)]
  · refine ⟨fun a => absurd ⟨a.1, a.2.1, a.2.2.1⟩ hg, fun _ => ?_⟩
    rw [if_neg]
    intro a
    rw [Bool.and_eq_true] at a
    exact hg ⟨a.1, (isPrompt_iff P Tmax κ nf tbs w s tables weights h prompt).1 a.2⟩

/-- For all sizes with Good P (a head's size is even; there is a key/value head, and their number
divides the query heads'; there is an expert) and under h : Same ..
(IntegerModel/Readable/Defs.lean): the model of IntegerModel/Model.lean on a prompt of P.T tokens is
the library's program (argTo of lgK at the last position) at P, κ, nf, tbs, w. It is none unless its
own test wellFormed is true, the prompt has 1 .. Tmax tokens, and no range condition fails. -/
theorem model_eq [Decidable (RunsK P κ nf tbs w prompt)] :
    IntegerTransformer.model s tables weights (Array.ofFn fun i => (prompt i).val) =
      if IntegerTransformer.wellFormed s tables weights = true ∧ 0 < P.T ∧
          P.T ≤ Tmax ∧ RunsK P κ nf tbs w prompt then
        some (argTo (lgK P κ nf tbs w prompt (P.T - 1)) (P.V - 1))
      else none :=
  (model_is P hP Tmax κ nf tbs w s tables weights h prompt).eq_ite

end Model

end IntegerModel.Readable
