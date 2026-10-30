-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/FitFromB.lean: a Boolean test for the sentence "the sampled challenges from
a round on fit the declared rounds" (`FitFrom`, Johnson/Prover/Link/BodyFit.lean), and the theorem
that the test's "true" gives `FitFrom`. That sentence speaks of every list of shown items of the
declared sorts; of a round's fitting all clauses but the one on the items read what was sampled
alone, so a test on the sampled challenges gives it. Two definitions that compute, one theorem and
its proof. They are general: `D` is any function from a round's number to what was sampled there
(`Fmt.Drawn`), `l` any list of declared rounds (`Laid`, Johnson/Desc/K12/Frame.lean: each round is
paired with a list of oracles, which is not read here), `o` any first number. The lists of tests in
Johnson/Desc/ProofFile/Honest/K12/AllB.lean have `fitFromB` as an item, and the proofs there call
`fitFrom_of_B`.

  `fitFrom_of_B`: `fitFromB D l o = true` gives `FitFrom D l o`
  `fitOneB d x`: a definition: one declared round `d` against what was sampled `x`: as many
    elements, positions and matrix entries as the round's entry states; every position is below
    `2 ^ logN`, the entry's range; every matrix entry is -1, 0 or 1; `drawsMarkedNonzeroHaveNonzeroWords`
    (Johnson/Desc/Block.lean) is true: the elements that must not be 0 are not, as raw words (the
    three words are not all 0), and the format knows the round's name; the three words of every
    element are below the prime (`ltE`, Johnson/Prover/Link/ViewWords.lean)
  `fitFromB D l o`: a definition: the same along `l`: the declared round of number n, counted from
    0, against `D (o + n)`; true at the empty list

By what. Induction along `l`. A round's fitting is `RoundFits`
(Johnson/Top/H0/StepLaws/RoundsFit.lean), with seven fields. The first, `items`, is the hypothesis
that `FitFrom` puts on the list of items; the other six are the first six clauses of `fitOneB`. The
seventh clause of `fitOneB` is the second half of `FitFrom`. `fitOneB` calls `drawsMarkedNonzeroHaveNonzeroWords` at the empty
list of items; `drawsMarkedNonzeroHaveNonzeroWords` reads only what was sampled, so its value at every other list of items is the
same by unfolding.

Limits. The test is sufficient for `FitFrom`; it is not shown to be necessary. Nothing on
completeness, on soundness or on what is hidden.
-/
import Johnson.Prover.Link.BodyFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link

/-- One declared round `d` against what was sampled `x`: the six clauses of `RoundFits` that do not
read the items, and `ltE` at every element. -/
def fitOneB (d : Fmt.DeclaredRound) (x : Fmt.Drawn) : Bool :=
  decide (x.elems.length = d.entry.drawE) && decide (x.poss.length = d.entry.poss) &&
  decide (x.trits.length = d.entry.trits) && (x.poss.all fun y => decide (y < 2 ^ d.entry.logN)) &&
  (x.trits.all fun t => decide (t = -1 ∨ t = 0 ∨ t = 1)) && drawsMarkedNonzeroHaveNonzeroWords d ⟨[], x⟩ &&
  x.elems.all ltE

/-- `fitOneB` along a list of declared rounds: the round of number n against `D (o + n)`. -/
def fitFromB (D : ℕ → Fmt.Drawn) : Laid → ℕ → Bool
  | [], _ => true
  | d :: l, o => fitOneB d.1 (D o) && fitFromB D l (o + 1)

/-- **The test's "true" gives `FitFrom`.** At every `D`, `l` and `o`. -/
theorem fitFrom_of_B (D : ℕ → Fmt.Drawn) : ∀ (l : Laid) (o : ℕ), fitFromB D l o = true →
    FitFrom D l o
  | [], _, _ => fun n d hd => by simp at hd
  | e :: l, o, h => by
    rw [fitFromB, Bool.and_eq_true] at h
    intro n d hd
    cases n with
    | zero =>
      obtain rfl : e = d := by simpa using hd
      have k := h.1
      unfold fitOneB at k
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at k
      obtain ⟨⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩ := k
      exact ⟨fun vals hv => ⟨hv, k1, k2, k3, k4, k5, k6⟩, k7⟩
    | succ m =>
      have ih := fitFrom_of_B D l (o + 1) h.2 m d (by simpa using hd)
      have e1 : o + (m + 1) = o + 1 + m := by omega
      rw [e1]
      exact ih

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.fitFrom_of_B
#print axioms ProofFile.Honest.K12.fitOneB
#print axioms ProofFile.Honest.K12.fitFromB
