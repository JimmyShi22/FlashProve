-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/HashEvents.lean: general lemmas for bounding hash events on a trace. The probabilistic core
is Rom/OneCount.lean: an event that a single new answer causes (`StepEvent`) is bounded query by
query.
  `stepOf`, `hashEvent_iff_stepEvent`
                         the hash event of Hash/MerklePure.lean (`Merkle.Events.HashEvent`) is such
                         an event
  `stepEvent_or`         two such events, joined by "or", are one such event
  `pr_unif_mem_le`, `pr_unif_snd_mem_le`
                         a uniform element of a non-empty C, or the second component of a uniform
                         pair, is under an injective map in a given list with probability at most
                         (length of the list) / |C|
  `card_dig`             there are 2^lam digests (`Dig lam`, Iop/Wire.lean)
  `three_sum_range_le`   3 · (0 + 1 + ... + (t - 1)) ≤ 2 t²
Compile/Batch/Hash.lean applies them to the events `EM` and `EF` of Compile/Batch/Events.lean.
-/
import Rom.OneCount
import Compile.Spec
import Hash.MerklePure

noncomputable section

namespace Compile
open Iop Rom Prob
open scoped ENNReal

/-- The step that causes the hash event of Hash/MerklePure.lean: a new entry whose "answer" occurs
before it. -/
def stepOf {S : OSpec} {D : Type} (Ev : Merkle.Events (QA S) D) (pre : Trace S) (e : QA S) : Prop :=
  e ∉ pre ∧ ∃ c, Ev.answer e = some c ∧ c ∈ Ev.occAll pre

theorem hashEvent_iff_stepEvent
    {S : OSpec} {D : Type} (Ev : Merkle.Events (QA S) D) (tr : Trace S) :
    Ev.HashEvent tr ↔ StepEvent (stepOf Ev) tr := by
  constructor
  · rintro ⟨pre, e, post, c, h1, h2, h3, h4⟩
    exact ⟨pre, e, post, h1, h2, c, h3, Merkle.Events.mem_occAll.2 h4⟩
  · rintro ⟨pre, e, post, h1, h2, c, h3, h4⟩
    exact ⟨pre, e, post, c, h1, h2, h3, Merkle.Events.mem_occAll.1 h4⟩

theorem stepEvent_or {S : OSpec} (s₁ s₂ : Trace S → QA S → Prop) (tr : Trace S) :
    StepEvent (fun pre e => s₁ pre e ∨ s₂ pre e) tr ↔ StepEvent s₁ tr ∨ StepEvent s₂ tr := by
  constructor
  · rintro ⟨pre, e, post, h, h1 | h1⟩
    · exact Or.inl ⟨pre, e, post, h, h1⟩
    · exact Or.inr ⟨pre, e, post, h, h1⟩
  · rintro (⟨pre, e, post, h, h1⟩ | ⟨pre, e, post, h, h1⟩)
    · exact ⟨pre, e, post, h, Or.inl h1⟩
    · exact ⟨pre, e, post, h, Or.inr h1⟩

/-- A uniform element of a non-empty C, under an injective map, is in a given list with probability
at most (length of the list) / |C|. -/
theorem pr_unif_mem_le {C B : Type} [Fintype C] [Nonempty C] (g : C → B)
    (hg : Function.Injective g) (l : List B) :
    pr (unif C) {c | g c ∈ l} ≤ (l.length : ℝ≥0∞) / Fintype.card C := by
  classical
  refine pr_unif_le_of_cnt_le (cnt_le_of_forall_finset fun Y hY => ?_)
  calc Y.card = (Y.image g).card := (Finset.card_image_of_injective _ hg).symm
    _ ≤ l.toFinset.card := Finset.card_le_card fun b hb => by
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hb
        exact List.mem_toFinset.2 (hY c hc)
    _ ≤ l.length := List.toFinset_card_le l

/-- `pr_unif_mem_le` for the second component of a uniform pair. -/
theorem pr_unif_snd_mem_le {A C B : Type} [Fintype A] [Nonempty A] [Fintype C] [Nonempty C]
    (g : C → B) (hg : Function.Injective g) (l : List B) :
    pr (unif (A × C)) {r | g r.2 ∈ l} ≤ (l.length : ℝ≥0∞) / Fintype.card C := by
  have h : pr (unif (A × C)) {r | g r.2 ∈ l} = pr ((unif (A × C)).map Prod.snd) {c | g c ∈ l} := by
    rw [pr_map]; rfl
  rw [h, map_snd_unif]
  exact pr_unif_mem_le g hg l

theorem card_dig (lam : ℕ) : (Fintype.card (Dig lam) : ℝ≥0∞) = 2 ^ lam := by
  simp [Dig]

/-- 3 · (0 + 1 + ... + (t - 1)) ≤ 2 t² -/
theorem three_sum_range_le (t : ℕ) : ∑ v ∈ Finset.range t, 3 * v ≤ 2 * t ^ 2 := by
  have h1 : (∑ v ∈ Finset.range t, v) * 2 = t * (t - 1) := Finset.sum_range_id_mul_two t
  have h2 : t * (t - 1) ≤ t * t := Nat.mul_le_mul_left t (Nat.sub_le t 1)
  rw [← Finset.mul_sum, pow_two]
  omega

end Compile
