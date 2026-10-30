-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/RelTruePaper.lean: the true request (`TrueAt` of Cm/RelBase.lean) is the text's sentence "the
reply is the greedy reply to the request", written out after the text.

In standard terms: greedy decoding. `TrueAt` is proved equivalent (`paper_iff`) to a second
wording, in which each checked token is the least token among those with a greatest logit
(`IsGreedy`).

Two definitions, two theorems. No cells, no code, no protocol, no chance.

Main names:
  `PaperTrue κ nf i x`: the text's sentence: a range r < e ≤ 1,024; the integer program runs on the
    prompt (else the greedy reply is undefined); for r ≤ t < min(e, 1,023) token t + 1 of the
    prompt is the greedy token at t; the reply is the greedy token at position 1,023 if e = 1,024,
    and 0 otherwise.

Limits: that `PaperTrue` renders the text is a comparison by reading of one sentence. That the
integer program (`RunsK`, `logitsAt`) is the text's integer model is a comparison by reading of two
definitions, and no theorem.
Definitions, theorems and proofs are written after the text's sentence.

Terms: lean/GLOSSARY.md.
-/
import Cm.RelBase

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm
open Inst.Model Inst.Model.All

/-- the greedy token of a list of V logits: the least token among those with a greatest logit -/
def IsGreedy (V : ℕ) (l : ℕ → ℤ) (v : ℕ) : Prop :=
  v < V ∧ (∀ u < V, l u ≤ l v) ∧ ∀ u < V, (∀ u' < V, l u' ≤ l u) → v ≤ u

/-- Under `hw`: `IsGreedy V l w`, in the form of `TrueAt`'s third clause: no logit is greater,
every smaller token has a strictly smaller logit -/
theorem greedy_iff {V : ℕ} {l : ℕ → ℤ} {w : ℕ} (hw : w < V) :
    IsGreedy V l w ↔ (∀ v < V, l v ≤ l w) ∧ ∀ v < w, l v < l w := by
  constructor
  · rintro ⟨_, h1, h2⟩
    refine ⟨h1, fun v hv => ?_⟩
    by_contra hc
    have hle : l w ≤ l v := not_lt.1 hc
    have := h2 v (lt_trans hv hw) (fun u' hu' => le_trans (h1 u' hu') hle)
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨hw, h1, fun u hu hmax => ?_⟩
    by_contra hc
    have hlt : u < w := not_le.1 hc
    have a := h2 u hlt
    have b := hmax w hw
    omega

/-- The text's sentence "the reply is the greedy reply to the request", written out (in words: the
head). -/
def PaperTrue (κ : ℕ → LayerScale) (nf : NormPar) (i : Idx) (x : Instance ppref) : Prop :=
  (x.r < x.e ∧ x.e ≤ 1024) ∧ RunsK ppref κ nf (fun _ => tbRef) i.weights x.prompt ∧
  (∀ t (h : t + 1 < 1024), x.r ≤ t → t < min x.e 1023 → IsGreedy 202048 (logitsAt κ nf i x t) (x.prompt ⟨t + 1, h⟩).val) ∧
  (if x.e = 1024 then IsGreedy 202048 (logitsAt κ nf i x 1023) x.y.val else x.y.val = 0)

/-- The true request is the text's sentence, at all words, final normalisations, indices and
requests: `TrueAt` ⇔ `PaperTrue`. That `PaperTrue` renders the text: Limits, in the head. -/
theorem paper_iff (κ : ℕ → LayerScale) (nf : NormPar) (i : Idx) (x : Instance ppref) :
    TrueAt κ nf i x ↔ PaperTrue κ nf i x := by
  have hwlt : ∀ t, x.w t < 202048 := fun t => x.w_lt t
  have hw1 : ∀ t (h : t + 1 < 1024), x.w t = (x.prompt ⟨t + 1, h⟩).val := fun t h => by
    unfold Instance.w Instance.tok
    exact dif_pos h
  have hw2 : x.w 1023 = x.y.val := x.w_last (by decide)
  constructor
  · rintro ⟨⟨a, b, c⟩, hr, hg⟩
    refine ⟨⟨a, b⟩, hr, fun t h h1 h2 => ?_, ?_⟩
    · rw [← hw1 t h]
      exact (greedy_iff (hwlt t)).2 (hg t h1 (lt_of_lt_of_le h2 (min_le_left _ _)))
    · split
      · rename_i he
        rw [← hw2]
        exact (greedy_iff (hwlt _)).2 (hg 1023 (by omega) (by omega))
      · rename_i he
        exact c (lt_of_le_of_ne b he)
  · rintro ⟨⟨a, b⟩, hr, h1, h2⟩
    refine ⟨⟨a, b, fun hlt => ?_⟩, hr, fun t ht1 ht2 => ?_⟩
    · have hne : ¬ x.e = 1024 := Nat.ne_of_lt hlt
      rw [if_neg hne] at h2
      exact h2
    · by_cases h : t + 1 < 1024
      · have h3 := h1 t h ht1 (lt_min ht2 (by omega))
        rw [← hw1 t h] at h3
        exact (greedy_iff (hwlt t)).1 h3
      · have e1 : t = 1023 := by omega
        have e2 : x.e = 1024 := by omega
        rw [if_pos e2, ← hw2] at h2
        subst e1
        exact (greedy_iff (hwlt _)).1 h2

end Cm
