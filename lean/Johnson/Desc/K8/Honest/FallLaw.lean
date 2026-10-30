-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FallLaw.lean: THE SMALLNESS TEST: what `zeroUnit`
(Johnson/Desc/K8/Honest/Fall.lean) says, entry by entry. Statements and proofs. Lemmas; none of the
library's goals.

  `modelAllFrom_iff`, `modelAllBelow_iff`   the library's two loops over numbers, as sentences
  `selfUnits_iff`   the verifier's test says yes just if no entry of a vector that the segment has
                     has the weight 0
  `zeroUnit_iff`    `zeroUnit` says yes just if some such entry has the weight 0
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.Fall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.First.TailClaims

/-- The library's loop over count numbers from i on, as a sentence. -/
theorem modelAllFrom_iff (p : Nat → Bool) : ∀ (count i : Nat),
    OnBytes.Model.allFrom p count i = true ↔ ∀ j, i ≤ j → j < i + count → p j = true
  | 0, i => by
    constructor
    · intro _ j h1 h2
      omega
    · intro _
      rfl
  | count + 1, i => by
    rw [OnBytes.Model.allFrom, Bool.and_eq_true, modelAllFrom_iff p count (i + 1)]
    constructor
    · intro ⟨h0, h⟩ j h1 h2
      by_cases hj : j = i
      · rw [hj]
        exact h0
      · exact h j (by omega) (by omega)
    · intro h
      exact ⟨h i (Nat.le_refl _) (by omega), fun j h1 h2 => h j (by omega) (by omega)⟩

/-- The library's loop over the numbers below n, as a sentence. -/
theorem modelAllBelow_iff (n : Nat) (p : Nat → Bool) :
    OnBytes.Model.allBelow n p = true ↔ ∀ j < n, p j = true := by
  unfold OnBytes.Model.allBelow
  rw [modelAllFrom_iff]
  constructor
  · intro h j hj
    exact h j (Nat.zero_le _) (by omega)
  · intro h j _ hj
    exact h j (by omega)

/-- The verifier's test says yes just if no entry of a vector that the segment has has the weight 0.
-/
theorem selfUnits_iff (tl : HTailF2) (nU : Array Nat) (F : Fork) :
    selfUnits tl nU F = true ↔
      ∀ n < 3, ∀ t, tl.ix.U.getD n none = some t →
        ∀ x < nU.getD n 0, isZeroE (unitWeightAt F t x) = false := by
  unfold selfUnits
  rw [List.all_eq_true]
  constructor
  · intro h n hn t ht x hx
    have h1 := h n (List.mem_range.2 hn)
    rw [ht] at h1
    have h2 := (modelAllBelow_iff _ _).1 h1 x hx
    simpa [unitWeightAt] using h2
  · intro h n hn
    have hn' := List.mem_range.1 hn
    cases ht : tl.ix.U.getD n none with
    | none => rfl
    | some t =>
      refine (modelAllBelow_iff _ _).2 fun x hx => ?_
      have h2 := h n hn' t ht x hx
      simpa [unitWeightAt] using h2

/-- `zeroUnit` says yes just if some entry of a vector that the segment has has the weight 0. -/
theorem zeroUnit_iff (tl : HTailF2) (nU : Array Nat) (F : Fork) :
    zeroUnit tl nU F = true ↔
      ∃ n < 3, ∃ t, tl.ix.U.getD n none = some t ∧
        ∃ x < nU.getD n 0, isZeroE (unitWeightAt F t x) = true := by
  unfold zeroUnit
  rw [Bool.not_eq_true', ← Bool.not_eq_true, selfUnits_iff]
  constructor
  · intro h
    exact Classical.byContradiction fun hc => h fun n hn t ht x hx => by
      cases hz : isZeroE (unitWeightAt F t x) with
      | false => rfl
      | true => exact absurd ⟨n, hn, t, ht, x, hx, hz⟩ hc
  · intro ⟨n, hn, t, ht, x, hx, hz⟩ h
    rw [h n hn t ht x hx] at hz
    exact Bool.false_ne_true hz

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.modelAllFrom_iff
#print axioms VerifiableInference.Desc.First.K8.Honest.modelAllBelow_iff
#print axioms VerifiableInference.Desc.First.K8.Honest.selfUnits_iff
#print axioms VerifiableInference.Desc.First.K8.Honest.zeroUnit_iff
