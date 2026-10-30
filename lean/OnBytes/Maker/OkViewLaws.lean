-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/OkViewLaws.lean: what a yes of the tests on a view's words and on the words of a key's
seeds (`okView`, `okSeeds`, OnBytes/Maker/OkView.lean) says (of a view: word by word; of a key's
seeds: element by element, by `okE`); and that one word that is not below the prime makes the three
decisions as one (`decide3`, OnBytes/Maker/Decide3.lean) say no.

Main names:
  `okF_iff`, `okGot_e`, `okGot_answer`, `okGot_f`: the tests on a word and on an item, as
    inequalities of words. `pW` is the prime as a word (OnBytes/Field/Word.lean).
  `okView_iff`: the test on a view, item by item and word by word. `okSeeds_iff`: on a key's seeds.
  `decide3_vals`, `decide3_opened`: where `decide3` says yes, every item of every round of the three
    views passes `okGot`, and every word of every opened column is below the prime.
  `decide3_seeds`: and every seed's factor and point pass `okE`.
  `decide3_no_of_item`, `decide3_no_of_word`: one item that fails `okGot`, or one word of an opened
    column that is not below the prime, in any of the three views: `decide3` says no, whatever the
    three runs say.
  `decide3_no_of_factor`: a seed of the key whose factor fails `okE`: no. `factor_p`: the factor
    with the words (p, 0, 0) is "not zero" to the test on words and fails `okE`.
No letter stands under "there is" in a conclusion.

What is not claimed. THAT THE THREE RUNS SAY YES AT A KEY WITH SUCH A FACTOR: no input is known at
which `runs3` says yes and `decide3` no. At the files' own descriptions the key is written by
`keyOf` (OnBytes/Slice/KeyOfRec.lean), every word through `writeE`, below the prime, so the test on
the seeds is idle there. What OnBytes/Maker/OkView.lean's head lists as not tested: the draws, the
key's answers, that the seeds are the table's, the instance, the silent rounds. Nothing on
soundness.


-/
import OnBytes.Maker.Decide3

set_option autoImplicit false

namespace OnBytes.Maker

open OnBytes.Proof (TailPublic FirstEnd)

theorem okF_iff (w : UInt64) : okF w = true ↔ w < pW := by
  unfold okF
  exact decide_eq_true_iff

theorem okE_ofTriple (x : UInt64 × UInt64 × UInt64) :
    okE (E.ofTriple x) = true ↔ x.1 < pW ∧ x.2.1 < pW ∧ x.2.2 < pW := by
  show (okF x.1 && okF x.2.1 && okF x.2.2) = true ↔ _
  rw [Bool.and_eq_true, Bool.and_eq_true, okF_iff, okF_iff, okF_iff, and_assoc]

theorem okGot_f (x : UInt64) : okGot (.f x) = true ↔ x < pW := okF_iff x

theorem okGot_e (x : UInt64 × UInt64 × UInt64) :
    okGot (.e x) = true ↔ x.1 < pW ∧ x.2.1 < pW ∧ x.2.2 < pW := okE_ofTriple x

theorem okGot_answer (x : UInt64 × UInt64 × UInt64) :
    okGot (.answer x) = true ↔ x.1 < pW ∧ x.2.1 < pW ∧ x.2.2 < pW := okE_ofTriple x

/-- **The test on a view, item by item and word by word.** -/
theorem okView_iff (v : Fmt.View) :
    okView v = true ↔
      (∀ r ∈ v.rounds, ∀ g ∈ r.vals, okGot g = true) ∧ ∀ o ∈ v.opened, ∀ w ∈ o.2.2, w < pW := by
  unfold okView
  simp only [Bool.and_eq_true, List.all_eq_true, okF_iff]

/-- The test on a key's seeds, seed by seed. -/
theorem okSeeds_iff (key : TableKey) :
    okSeeds key = true ↔ ∀ x ∈ key.seeds, okE x.beta = true ∧ ∀ a ∈ x.z, okE a = true := by
  unfold okSeeds
  simp only [List.all_eq_true, Bool.and_eq_true]

/-- **The factor with the words (p, 0, 0)** is "not zero" to the test on words, and fails the test
on the range. -/
theorem factor_p : isZeroE (E.mk3 pW 0 0) = false ∧ okE (E.mk3 pW 0 0) = false :=
  ⟨by decide, by decide⟩

section
variable {p : TailPublic} {key : TableKey} {b₁ : Blk FirstEnd} {s₁ : Start} {n₁ n₂ : Nat}
  {v₁ v₂ v₃ : Fmt.View}

/-- **Where the three decisions as one say yes, every item of the three views passes the test.** -/
theorem decide3_vals (h : decide3 p key b₁ s₁ n₁ n₂ v₁ v₂ v₃ = true) :
    ∀ r ∈ v₁.rounds ++ (v₂.rounds ++ v₃.rounds), ∀ g ∈ r.vals, okGot g = true := by
  obtain ⟨-, h1, h2, h3, -⟩ := decide3_parts h
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · exact ((okView_iff _).1 h1).1 r hr
  · rcases List.mem_append.1 hr with hr | hr
    · exact ((okView_iff _).1 h2).1 r hr
    · exact ((okView_iff _).1 h3).1 r hr

/-- **Where they say yes, every word of every opened column is below the prime.** -/
theorem decide3_opened (h : decide3 p key b₁ s₁ n₁ n₂ v₁ v₂ v₃ = true) :
    ∀ o ∈ v₁.opened ++ (v₂.opened ++ v₃.opened), ∀ w ∈ o.2.2, w < pW := by
  obtain ⟨-, h1, h2, h3, -⟩ := decide3_parts h
  intro o ho
  rcases List.mem_append.1 ho with ho | ho
  · exact ((okView_iff _).1 h1).2 o ho
  · rcases List.mem_append.1 ho with ho | ho
    · exact ((okView_iff _).1 h2).2 o ho
    · exact ((okView_iff _).1 h3).2 o ho

/-- **Where they say yes, every seed's factor and point pass the test on the range.** -/
theorem decide3_seeds (h : decide3 p key b₁ s₁ n₁ n₂ v₁ v₂ v₃ = true) :
    ∀ x ∈ key.seeds, okE x.beta = true ∧ ∀ a ∈ x.z, okE a = true :=
  (okSeeds_iff key).1 (decide3_parts h).1

/-- **A seed whose factor fails the test on the range: no**, whatever the three runs say. -/
theorem decide3_no_of_factor {x : SampleSeed} (hx : x ∈ key.seeds) (hn : okE x.beta = false) :
    decide3 p key b₁ s₁ n₁ n₂ v₁ v₂ v₃ = false := by
  cases h : decide3 p key b₁ s₁ n₁ n₂ v₁ v₂ v₃ with
  | false => rfl
  | true =>
    rw [(decide3_seeds h x hx).1] at hn
    cases hn

/-- **One item that fails the test: no**, whatever the three runs say. -/
theorem decide3_no_of_item {r : Fmt.RoundView} (hr : r ∈ v₁.rounds ++ (v₂.rounds ++ v₃.rounds))
    {g : Fmt.ItemValue} (hg : g ∈ r.vals) (hn : okGot g = false) :
    decide3 p key b₁ s₁ n₁ n₂ v₁ v₂ v₃ = false := by
  cases h : decide3 p key b₁ s₁ n₁ n₂ v₁ v₂ v₃ with
  | false => rfl
  | true =>
    rw [decide3_vals h r hr g hg] at hn
    cases hn

/-- **One word of an opened column that is not below the prime: no**, whatever the three runs say.
-/
theorem decide3_no_of_word {o : Nat × Nat × List UInt64}
    (ho : o ∈ v₁.opened ++ (v₂.opened ++ v₃.opened)) {w : UInt64} (hw : w ∈ o.2.2)
    (hn : pW ≤ w) : decide3 p key b₁ s₁ n₁ n₂ v₁ v₂ v₃ = false := by
  cases h : decide3 p key b₁ s₁ n₁ n₂ v₁ v₂ v₃ with
  | false => rfl
  | true => exact absurd (decide3_opened h o ho w hw) (UInt64.not_lt.2 hn)

end

end OnBytes.Maker

#print axioms OnBytes.Maker.okView_iff
#print axioms OnBytes.Maker.okSeeds_iff
#print axioms OnBytes.Maker.factor_p
#print axioms OnBytes.Maker.decide3_seeds
#print axioms OnBytes.Maker.decide3_no_of_factor
#print axioms OnBytes.Maker.decide3_vals
#print axioms OnBytes.Maker.decide3_opened
#print axioms OnBytes.Maker.decide3_no_of_item
#print axioms OnBytes.Maker.decide3_no_of_word
