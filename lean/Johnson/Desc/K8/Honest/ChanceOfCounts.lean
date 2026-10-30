-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/ChanceOfCounts.lean: FROM A COUNT AT EACH FIXING OF THE OTHER ROUNDS'
CHALLENGES TO A CHANCE OVER A WHOLE LIST OF CHALLENGES. Statements and proofs, on counting alone: no
block, no state of the chain, no prover. Lemmas; none of the library's goals.

The measure. ι: a finite type of rounds. A i: round i's challenges, a finite type with a member. The
list: f : ∀ i, A i, uniform (Prob.unif): each round's challenge uniform, the rounds independent.
  `cnt_pi_fibre`   if at every list f at most n values a of round j's challenge make P true of f
      with a laid at j, then P's count times the number of round j's challenges is at most n times
      the number of lists. (Prob.cnt_pi_coord, Prob/Count.lean, is the case in which P reads round j
      alone.)
  `pr_pi_fibre`   so the chance of P is at most n / (the number of round j's challenges)
  **`chance_of_counts`**   front: what stands in front of round j, read off the list: nothing, or a
      value s; it does not read round j's challenge. el: the value of type K that round j's
      challenge gives; at most w challenges give one value. Q s x: an event at s and x. If at every
      s that front returns at most n values x have Q s x, the chance that front returns an s with Q
      s (el (f j)) is at most n * w / (the number of round j's challenges)
Limits. Nothing says which lists of challenges a run of a protocol draws, nor that any function of a
run is such a front.
Terms: lean/GLOSSARY.md.
-/
import Prob.Count
import Prob.Bias

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open scoped ENNReal

section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ i, Fintype (A i)]

/-- A count on every fibre over one coordinate bounds the count on the product. -/
theorem cnt_pi_fibre (j : ι) (P : (∀ i, A i) → Prop) (n : ℕ)
    (h : ∀ f, Prob.cnt (fun a : A j => P (Function.update f j a)) ≤ n) :
    Prob.cnt P * Fintype.card (A j) ≤ n * Fintype.card (∀ i, A i) := by
  classical
  let e : (∀ i, A i) ≃ (∀ i : {i // i ≠ j}, A i) × A j :=
    (Equiv.piSplitAt j A).trans (Equiv.prodComm _ _)
  have h1 : Prob.cnt P = Prob.cnt fun x : (∀ i : {i // i ≠ j}, A i) × A j => P (e.symm x) := by
    rw [← Prob.cnt_equiv e fun x => P (e.symm x)]
    simp only [Equiv.symm_apply_apply]
  have h2 : Prob.cnt (fun x : (∀ i : {i // i ≠ j}, A i) × A j => P (e.symm x)) ≤
      Fintype.card (∀ i : {i // i ≠ j}, A i) * n := by
    refine Prob.cnt_prod_le _ n fun g => ?_
    by_cases hne : Nonempty (A j)
    · obtain ⟨a₀⟩ := hne
      refine le_trans (le_of_eq (Prob.cnt_congr fun a => ?_)) (h (e.symm (g, a₀)))
      have : e.symm (g, a) = Function.update (e.symm (g, a₀)) j a := by
        funext i
        by_cases hi : i = j
        · subst hi
          simp [e, Equiv.piSplitAt]
        · simp [e, Equiv.piSplitAt, hi]
      rw [this]
    · have : IsEmpty (A j) := not_nonempty_iff.1 hne
      rw [Prob.cnt_false fun a _ => this.false a]
      exact Nat.zero_le _
  have h3 : Fintype.card (∀ i, A i) =
      Fintype.card (∀ i : {i // i ≠ j}, A i) * Fintype.card (A j) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  rw [h1, h3]
  calc Prob.cnt (fun x : (∀ i : {i // i ≠ j}, A i) × A j => P (e.symm x)) * Fintype.card (A j)
      ≤ Fintype.card (∀ i : {i // i ≠ j}, A i) * n * Fintype.card (A j) :=
        Nat.mul_le_mul_right _ h2
    _ = n * (Fintype.card (∀ i : {i // i ≠ j}, A i) * Fintype.card (A j)) := by ring

variable [∀ i, Nonempty (A i)]

/-- So the chance, over a uniform list. -/
theorem pr_pi_fibre (j : ι) (P : (∀ i, A i) → Prop) (n : ℕ)
    (h : ∀ f, Prob.cnt (fun a : A j => P (Function.update f j a)) ≤ n) :
    Prob.pr (Prob.unif (∀ i, A i)) {f | P f} ≤ (n : ℝ≥0∞) / Fintype.card (A j) := by
  rw [Prob.pr_unif_le_iff]
  have hc : (Fintype.card (A j) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have ht : (Fintype.card (A j) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hk : (Prob.cnt P : ℝ≥0∞) * Fintype.card (A j) ≤ (n : ℝ≥0∞) * Fintype.card (∀ i, A i) := by
    exact_mod_cast cnt_pi_fibre j P n h
  calc (Prob.cnt P : ℝ≥0∞)
      = (Prob.cnt P : ℝ≥0∞) * Fintype.card (A j) / Fintype.card (A j) :=
        (ENNReal.mul_div_cancel_right hc ht).symm
    _ ≤ (n : ℝ≥0∞) * Fintype.card (∀ i, A i) / Fintype.card (A j) :=
        ENNReal.div_le_div_right hk _
    _ = (n : ℝ≥0∞) / Fintype.card (A j) * Fintype.card (∀ i, A i) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring

/-- **From a count at what stands in front of a round to a chance over the list.** -/
theorem chance_of_counts {σ K : Type} [Fintype K] (j : ι) (el : A j → K) (w : ℕ)
    (hw : ∀ x, Prob.cnt (fun a => el a = x) ≤ w) (front : (∀ i, A i) → Option σ)
    (hfree : ∀ f a, front (Function.update f j a) = front f) (Q : σ → K → Prop) (n : ℕ)
    (hQ : ∀ f s, front f = some s → Prob.cnt (fun x => Q s x) ≤ n) :
    Prob.pr (Prob.unif (∀ i, A i)) {f | ∃ s, front f = some s ∧ Q s (el (f j))} ≤
      ((n * w : ℕ) : ℝ≥0∞) / Fintype.card (A j) := by
  refine pr_pi_fibre j _ (n * w) fun f => ?_
  simp only [hfree, Function.update_self]
  cases hf : front f with
  | none =>
    rw [Prob.cnt_false fun a ha => by
      obtain ⟨s, hs, -⟩ := ha
      cases hs]
    exact Nat.zero_le _
  | some s =>
    refine (Prob.cnt_mono fun a ha => ?_).trans
      ((Prob.cnt_comp_le el hw (Q s)).trans (Nat.mul_le_mul_right w (hQ f s hf)))
    obtain ⟨s', hs, hq⟩ := ha
    obtain rfl := Option.some.inj hs
    exact hq

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.cnt_pi_fibre
#print axioms VerifiableInference.Desc.First.K8.Honest.pr_pi_fibre
#print axioms VerifiableInference.Desc.First.K8.Honest.chance_of_counts
