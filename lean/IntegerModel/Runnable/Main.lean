-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Runnable/Main.lean: the runnable model is the library's integer program.
Left side: ArrayProgram (IntegerModel/Runnable/ArrayModel.lean, ArrayNext.lean), a program on arrays
and Option, in core Lean only, so that it can be compiled and run. It has not
been run at Maverick's sizes; no file of this library runs it at any size.
Right side: the library's XK, lgK, RunsK (Inst/Model/Program.lean). At Maverick's sizes
(ArrayProgram.modelShape: Llama 4 Maverick, window 1,024): IntegerModel/Runnable/AtModelSizes.lean.
  logits_eq, model_eq, next_eq   on P.T tokens below P.V: some (the library's value) if RunsK holds,
                                 else none (next: none too unless 0 < P.T ≤ Tmax, the program's
                                 window limit). For all sizes P with Good P, all scales, all
                                 weights, all tables with TabRel (which ties every layer's expRows
                                 to the program's); the program's settings st and weights W need to
                                 agree with the library's only inside the shapes (SameSettings,
                                 SameWeights)
  next_of_Model                  under the same hypotheses: if 0 < P.T ≤ Tmax, ArrayProgram.next is
                                 the last entry of ArrayProgram.Model; otherwise none
-/
import IntegerModel.Runnable.Attention
import IntegerModel.Runnable.FeedForward

set_option autoImplicit false

namespace IntegerModel.Runnable

open Inst.Model

theorem bind_bind_some {α β γ : Type} (s : Option α) (f : α → Option β) (g : β → γ) :
    (s.bind fun x => (f x).bind fun n => some (g n)) = (s.bind f).map g := by
  cases s with
  | none => rfl
  | some x => cases h : f x <;> simp [h]

section General
variable (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables)
  (w : Weights) (prompt : Fin P.T → Fin P.V)

theorem XK_att (L : ℕ) :
    XK P κ tbs w prompt (2 * L + 1) =
      Att.x' (P.at (κ L)) (tbs L) (w.layer L) L (XK P κ tbs w prompt (2 * L)) := by
  show (if (2 * L) % 2 = 0 then
        Att.x' (P.at (κ (2 * L / 2))) (tbs (2 * L / 2)) (w.layer (2 * L / 2))
          (2 * L / 2) (XK P κ tbs w prompt (2 * L))
      else _) = _
  rw [if_pos (by omega), Nat.mul_div_cancel_left L (by norm_num)]

theorem XK_ff (L : ℕ) :
    XK P κ tbs w prompt (2 * (L + 1)) =
      FF.x'' (P.at (κ L)) (tbs L) (w.layer L) L (XK P κ tbs w prompt (2 * L + 1)) := by
  show (if (2 * L + 1) % 2 = 0 then _
      else
        FF.x'' (P.at (κ ((2 * L + 1) / 2))) (tbs ((2 * L + 1) / 2)) (w.layer ((2 * L + 1) / 2))
          ((2 * L + 1) / 2) (XK P κ tbs w prompt (2 * L + 1))) = _
  rw [if_neg (by omega), show (2 * L + 1) / 2 = L by omega]

/-- the embedding rows -/
theorem X0_eq (W : ArrayProgram.Weights) (hW : SameWeights P W w) :
    ((Array.ofFn fun i => (prompt i).val).map fun a => ArrayProgram.row P.d (W.embedding a)) =
      tabl P.T fun i => tabl P.d (XK P κ tbs w prompt 0 i) := by
  apply Array.ext
  · simp
  · intro i h1 _
    have hi : i < P.T := by simpa using h1
    simp only [Array.getElem_map, Array.getElem_ofFn, Array.getElem_range]
    refine tabl_congr fun j hj => ?_
    show _ = if h : i < P.T then w.Emb (prompt ⟨i, h⟩) j else 0
    rw [dif_pos hi]
    exact hW.emb _ (prompt ⟨i, hi⟩).isLt j hj

variable (hP : Good P) (Tmax : ℕ) (t : ArrayProgram.Tables)
  (hT : ∀ L < P.layers, TabRel t (tbs L) L (κ L).expRows) (st : ArrayProgram.Settings)
  (hst : SameSettings P st κ nf) (W : ArrayProgram.Weights) (hW : SameWeights P W w)

section Proofs
include hP hT hW

/-- one layer -/
theorem layer_is {L : ℕ} (hL : L < P.layers) (x : ℕ → Vec) :
    Is ((ArrayProgram.attention (shapeOf P Tmax) t (scalesOf (κ L)) (W.layer L) L
          (tabl P.T fun i => tabl P.d (x i))).bind
        (ArrayProgram.feedForward (shapeOf P Tmax) t (scalesOf (κ L)) (W.layer L) L))
      (Att.OK (P.at (κ L)) (tbs L) (w.layer L) L x ∧
        FF.OK (P.at (κ L)) (tbs L) (w.layer L) L (Att.x' (P.at (κ L)) (tbs L) (w.layer L) L x))
      (tabl P.T fun i =>
        tabl P.d (FF.x'' (P.at (κ L)) (tbs L) (w.layer L) L
              (Att.x' (P.at (κ L)) (tbs L) (w.layer L) L x) i)) :=
  Is.bind (attention_is (P.at (κ L)) ⟨hP.ch, hP.kv, hP.nexp⟩ (tbs L) (w.layer L) L x Tmax t
      (hT L hL) (W.layer L) ((hW.layer L hL).at _))
    (feedForward_is (P.at (κ L)) (tbs L) (w.layer L) L _ Tmax t (κ L).expRows (hT L hL) (W.layer L)
      ((hW.layer L hL).at _) hP.nexp)

include hst

/-- the first n layers -/
theorem layers_is :
    ∀ n ≤ P.layers,
      Is ((List.range n).foldlM
          (fun x L =>
            ArrayProgram.attention (shapeOf P Tmax) t (st.layer L) (W.layer L) L x >>=
              ArrayProgram.feedForward (shapeOf P Tmax) t (st.layer L) (W.layer L) L)
          (tabl P.T fun i => tabl P.d (XK P κ tbs w prompt 0 i)))
        (∀ L < n,
          Att.OK (P.at (κ L)) (tbs L) (w.layer L) L (XK P κ tbs w prompt (2 * L)) ∧
          FF.OK (P.at (κ L)) (tbs L) (w.layer L) L (XK P κ tbs w prompt (2 * L + 1)))
        (tabl P.T fun i => tabl P.d (XK P κ tbs w prompt (2 * n) i))
  | 0, _ => (Is.pure _).iff ⟨fun _ L hL => absurd hL (Nat.not_lt_zero L), fun _ => trivial⟩
  | n + 1, hn => by
      rw [List.range_succ, List.foldlM_append]
      simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
      have h :=
        layer_is P κ tbs w hP Tmax t hT W hW (Nat.lt_of_succ_le hn) (XK P κ tbs w prompt (2 * n))
      have hs := hst.layer n (Nat.lt_of_succ_le hn)
      rw [← XK_att, ← XK_ff,
        ← attention_scales _ _ (st.layer n) _ _ (scalesOf (κ n))
          hs.norm1 hs.kq hs.kk hs.kv hs.sh hs.ko,
        ← feedForward_scales _ _ (st.layer n) _ n (scalesOf (κ n))
          hs.norm2 hs.kg hs.ku hs.kd fun hE =>
            ⟨hs.kr ((hasExperts_iff n).1 hE),
              hs.kgR ((hasExperts_iff n).1 hE),
              hs.kuR ((hasExperts_iff n).1 hE)⟩] at h
      refine Is.of ?_ (fun _ => rfl) (Is.bind (layers_is n (Nat.le_of_succ_le hn)) h)
      constructor
      · rintro ⟨a, b⟩ L hL
        rcases Nat.lt_succ_iff_lt_or_eq.1 hL with h1 | rfl
        · exact a L h1
        · exact b
      · intro a
        exact ⟨fun L hL => a L (Nat.lt_succ_of_lt hL), a n (Nat.lt_succ_self n)⟩

/-- the residual stream after all layers -/
theorem stream_is :
    Is (ArrayProgram.stream (shapeOf P Tmax) t st W (Array.ofFn fun i => (prompt i).val))
      (∀ L < P.layers,
        Att.OK (P.at (κ L)) (tbs L) (w.layer L) L (XK P κ tbs w prompt (2 * L)) ∧
        FF.OK (P.at (κ L)) (tbs L) (w.layer L) L (XK P κ tbs w prompt (2 * L + 1)))
      (tabl P.T fun i => tabl P.d (XK P κ tbs w prompt (2 * P.layers) i)) := by
  have h := layers_is P κ nf tbs w prompt hP Tmax t hT st hst W hW P.layers le_rfl
  rw [← X0_eq P κ tbs w prompt W hW] at h
  exact h

/-- the final norm at all positions -/
theorem final_is :
    Is ((ArrayProgram.stream (shapeOf P Tmax) t st W (Array.ofFn fun i => (prompt i).val)).bind
        fun x => x.mapM (ArrayProgram.rmsNorm st.final))
      (RunsK P κ nf tbs w prompt) (tabl P.T fun i => tabl P.d (nrmK P κ nf tbs w prompt i)) :=
  Is.bind (stream_is P κ nf tbs w prompt hP Tmax t hT st hst W hW)
    (Is.mapM_tabl fun i _ => hst.final ▸ rmsNorm_is nf P.d (XK P κ tbs w prompt (2 * P.layers) i))

theorem logits_is :
    Is (ArrayProgram.logits (shapeOf P Tmax) t st W (Array.ofFn fun i => (prompt i).val))
      (RunsK P κ nf tbs w prompt) (tabl P.T fun i => tabl P.V (lgK P κ nf tbs w prompt i)) := by
  have e : ArrayProgram.logits (shapeOf P Tmax) t st W (Array.ofFn fun i => (prompt i).val) =
      ((ArrayProgram.stream (shapeOf P Tmax) t st W (Array.ofFn fun i => (prompt i).val)).bind
          fun x => x.mapM (ArrayProgram.rmsNorm st.final)).map
        fun n => n.map fun r => ArrayProgram.row P.V fun v => ArrayProgram.dot r (W.head · v) :=
    bind_bind_some _ _ _
  rw [e]
  refine ((final_is P κ nf tbs w prompt hP Tmax t hT st hst W hW).map _).val fun _ => ?_
  rw [tabl_map]
  exact tabl_congr fun i _ =>
    tabl_congr fun v hv => (dot_tabl _ _ _).trans (dot_congr fun j hj => hW.head j hj v hv)

theorem model_is :
    Is (ArrayProgram.Model (shapeOf P Tmax) t st W (Array.ofFn fun i => (prompt i).val))
      (RunsK P κ nf tbs w prompt)
      (tabl P.T fun i => argTo (lgK P κ nf tbs w prompt i) (P.V - 1)) := by
  refine ((logits_is P κ nf tbs w prompt hP Tmax t hT st hst W hW).map _).val fun _ => ?_
  rw [tabl_map]
  exact tabl_congr fun i _ => argmax_tabl _ _

theorem next_is :
    Is (ArrayProgram.next (shapeOf P Tmax) t st W (Array.ofFn fun i => (prompt i).val))
      (0 < P.T ∧ P.T ≤ Tmax ∧ RunsK P κ nf tbs w prompt)
      (argTo (lgK P κ nf tbs w prompt (P.T - 1)) (P.V - 1)) := by
  have e : ArrayProgram.next (shapeOf P Tmax) t st W (Array.ofFn fun i => (prompt i).val) =
      if (decide (0 < P.T) && decide (P.T ≤ Tmax) &&
        (Array.ofFn fun i => (prompt i).val).all (· < P.V)) = true then
          ((ArrayProgram.stream (shapeOf P Tmax) t st W (Array.ofFn fun i => (prompt i).val)).bind
            fun x => x.mapM (ArrayProgram.rmsNorm st.final)).map fun n =>
              ArrayProgram.argmaxFirst
                (ArrayProgram.row P.V fun v => ArrayProgram.dot n[P.T - 1]! (W.head · v))
        else none := by
    unfold ArrayProgram.next
    rw [Array.size_ofFn, ← bind_bind_some]
    rfl
  have hall : (Array.ofFn fun i => (prompt i).val).all (· < P.V) = true := by
    rw [← Array.all_toList, List.all_eq_true]
    intro a ha
    obtain ⟨i, rfl⟩ : ∃ i, (prompt i).val = a := by simpa [List.mem_ofFn] using ha
    exact decide_eq_true (prompt i).isLt
  rw [e, hall, Bool.and_true]
  by_cases h0 : 0 < P.T ∧ P.T ≤ Tmax
  · rw [if_pos (by simp [h0.1, h0.2])]
    refine Is.of ⟨fun a => ⟨h0.1, h0.2, a⟩, fun a => a.2.2⟩ (fun _ => ?_)
      ((final_is P κ nf tbs w prompt hP Tmax t hT st hst W hW).map _)
    rw [tabl_get _ (by omega : P.T - 1 < P.T)]
    exact (congrArg ArrayProgram.argmaxFirst
        (tabl_congr fun v hv =>
          (dot_tabl _ _ _).trans (dot_congr fun j hj => hW.head j hj v hv))).trans
      (argmax_tabl _ _)
  · rw [if_neg (by simpa using h0)]
    exact ⟨fun a => absurd ⟨a.1, a.2.1⟩ h0, fun _ => rfl⟩

end Proofs

include hP hT hst hW

/-- All logits, at any sizes P with Good P, under hT, hst, hW (the `variable` lines above). -/
theorem logits_eq [Decidable (RunsK P κ nf tbs w prompt)] :
    ArrayProgram.logits (shapeOf P Tmax) t st W (Array.ofFn fun i => (prompt i).val) =
      if RunsK P κ nf tbs w prompt then
        some
          (Array.ofFn fun i : Fin P.T => Array.ofFn fun v : Fin P.V => lgK P κ nf tbs w prompt i v)
      else none := by
  rw [(logits_is P κ nf tbs w prompt hP Tmax t hT st hst W hW).eq_ite,
    tabl_ofFn P.T fun i => Array.ofFn fun v : Fin P.V => lgK P κ nf tbs w prompt i v]
  simp only [tabl_ofFn]

/-- The program's own Model, at any sizes P with Good P, under hT, hst, hW: the first choice (argTo:
the least token of largest logit) at every position -/
theorem model_eq [Decidable (RunsK P κ nf tbs w prompt)] :
    ArrayProgram.Model (shapeOf P Tmax) t st W (Array.ofFn fun i => (prompt i).val) =
      if RunsK P κ nf tbs w prompt then
        some (Array.ofFn fun i : Fin P.T => argTo (lgK P κ nf tbs w prompt i) (P.V - 1))
      else none := by
  rw [(model_is P κ nf tbs w prompt hP Tmax t hT st hst W hW).eq_ite,
    tabl_ofFn P.T fun i => argTo (lgK P κ nf tbs w prompt i) (P.V - 1)]

/-- The next token, at any sizes P with Good P, under hT, hst, hW. -/
theorem next_eq [Decidable (RunsK P κ nf tbs w prompt)] :
    ArrayProgram.next (shapeOf P Tmax) t st W (Array.ofFn fun i => (prompt i).val) =
      if 0 < P.T ∧ P.T ≤ Tmax ∧ RunsK P κ nf tbs w prompt then
        some (argTo (lgK P κ nf tbs w prompt (P.T - 1)) (P.V - 1))
      else none :=
  (next_is P κ nf tbs w prompt hP Tmax t hT st hst W hW).eq_ite

/-- Under hP, hT, hst, hW, on P.T tokens below P.V, if 0 < P.T ≤ Tmax, ArrayProgram.next is the last
entry of the program's ArrayProgram.Model; otherwise it is none. -/
theorem next_of_Model :
    ArrayProgram.next (shapeOf P Tmax) t st W (Array.ofFn fun i => (prompt i).val) =
      if 0 < P.T ∧ P.T ≤ Tmax then
        (ArrayProgram.Model (shapeOf P Tmax) t st W (Array.ofFn fun i => (prompt i).val)).map
          fun a => a[P.T - 1]! else none := by
  have hn := next_is P κ nf tbs w prompt hP Tmax t hT st hst W hW
  have hm := (model_is P κ nf tbs w prompt hP Tmax t hT st hst W hW).map fun a => a[P.T - 1]!
  by_cases h0 : 0 < P.T ∧ P.T ≤ Tmax
  · rw [if_pos h0]
    by_cases hr : RunsK P κ nf tbs w prompt
    · rw [hn.1 ⟨h0.1, h0.2, hr⟩, hm.1 hr, tabl_get _ (by omega : P.T - 1 < P.T)]
    · rw [hn.2 fun a => hr a.2.2, hm.2 hr]
  · rw [if_neg h0]
    exact hn.2 fun a => h0 ⟨a.1, a.2.1⟩

end General

end IntegerModel.Runnable
