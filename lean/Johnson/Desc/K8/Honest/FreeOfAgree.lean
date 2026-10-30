-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FreeOfAgree.lean: A FUNCTION OF A LIST OF CHALLENGES WHOSE VALUES ON EACH
FIBRE OVER ONE ROUND AGREE LIES UNDER ONE THAT DOES NOT READ THAT ROUND. One statement and its
proof, on functions alone: no block, no state of the chain, no prover. A lemma; none of the
library's goals.

Why. `chance_of_counts` (Johnson/Desc/K8/Honest/ChanceOfCounts.lean) asks of front that it does not
read round j's challenge. A function that is read off a whole run need not meet that: at one
challenge of round j the run returns, at another something behind round j refuses, and the function
says nothing. What such a function can meet: wherever it says something on a fibre over round j, it
says one thing.
  `Agree j front`   on each fibre over round j all the values "some s" are one s
  **`free_of_agree`**   then there is front' which does not read round j's challenge (free), says
      what front says wherever front says something (over), and each of whose values is a value of
      front on the same fibre (from)
Limits. By choice: front' is no program. Nothing says that any function of a run meets `Agree`.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.ChanceOfCounts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest

section
variable {ι : Type} [DecidableEq ι] {A : ι → Type} {σ : Type}

/-- On each fibre over round j all the values "some s" are one s. -/
def Agree (j : ι) (front : (∀ i, A i) → Option σ) : Prop :=
  ∀ f a a' s s', front (Function.update f j a) = some s →
    front (Function.update f j a') = some s' → s = s'

/-- **Under a function that does not read round j.** -/
theorem free_of_agree (j : ι) (front : (∀ i, A i) → Option σ) (h : Agree j front) :
    ∃ front' : (∀ i, A i) → Option σ,
      (∀ f a, front' (Function.update f j a) = front' f) ∧
      (∀ f s, front f = some s → front' f = some s) ∧
      (∀ f s, front' f = some s → ∃ a, front (Function.update f j a) = some s) := by
  classical
  let front' : (∀ i, A i) → Option σ := fun f =>
    if hx : ∃ s a, front (Function.update f j a) = some s then some hx.choose else none
  have val : ∀ f s a, front (Function.update f j a) = some s → front' f = some s := by
    intro f s a hs
    have hx : ∃ s a, front (Function.update f j a) = some s := ⟨s, a, hs⟩
    obtain ⟨a', ha'⟩ := hx.choose_spec
    simp only [front', dif_pos hx]
    exact congrArg some (h f a' a _ _ ha' hs)
  have back : ∀ f s, front' f = some s → ∃ a, front (Function.update f j a) = some s := by
    intro f s hs
    by_cases hx : ∃ s a, front (Function.update f j a) = some s
    · simp only [front', dif_pos hx] at hs
      obtain ⟨a', ha'⟩ := hx.choose_spec
      exact ⟨a', by rw [ha', Option.some.inj hs]⟩
    · simp only [front', dif_neg hx] at hs
      cases hs
  refine ⟨front', fun f a => ?_, fun f s hs => ?_, back⟩
  · cases hf : front' f with
    | some s =>
      obtain ⟨a', ha'⟩ := back f s hf
      exact val _ s a' (by rw [Function.update_idem]; exact ha')
    | none =>
      cases hu : front' (Function.update f j a) with
      | none => rfl
      | some s =>
        obtain ⟨a', ha'⟩ := back _ s hu
        rw [Function.update_idem] at ha'
        rw [val f s a' ha'] at hf
        cases hf
  · exact val f s (f j) (by rw [Function.update_eq_self]; exact hs)

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.free_of_agree
