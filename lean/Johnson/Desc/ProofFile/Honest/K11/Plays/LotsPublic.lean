-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/LotsPublic.lean: the proofs of the five statements of
Johnson/Desc/ProofFile/Honest/K11/Plays/LotsPublicStatement.lean, to the letter. Lemmas; none of the
library's goals.

How. `lendsAtRow`: by unfolding: both rows have the same three counts, part by part. `lentIff`:
`lendsRow_iff` (Honest/Small/LendsRow.lean) at `k11Lent`'s own term. The two on the texts: where the
row is lent the text is its own "if"; where it is not, `lotsSilent` (LotsRuns.lean of this folder).
The last: the two right sides name no run. Two helpers stand beside the five: `lent_or_not` (a value
of the type Except is an error or a return) and `lends_false` (a refusal makes the public test say
no).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.LotsPublicStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.LotsRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (zeroE)
open OnBytes.Model (Reading)
open ProofFile.Honest.SumLaw (firstRun endRun)

/-- **At the seated row the test is the public one.** -/
theorem lendsAtRow : LendsAtRow := by
  intro Bk W₀ Rc Xi Tr X ch pl P claims weights
  rfl

/-- **The row is lent just where the public test says yes.** -/
theorem lentIff : LentIff := by
  intro Bk W₀ Rc Xi Tr X ch pl P claims weights k
  rw [← lendsAtRow Bk W₀ Rc Xi Tr X ch pl P claims weights]
  exact lendsRow_iff k ch pl _

/-- The row is lent or refused. -/
theorem lent_or_not {α β : Type} (x : Except α β) : (∃ e, x = .error e) ∨ ∃ c, x = .ok c := by
  cases x with
  | error e => exact Or.inl ⟨e, rfl⟩
  | ok c => exact Or.inr ⟨c, rfl⟩

/-- Where the row is refused the public test says no. -/
theorem lends_false {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X : Type} {ch : Nat}
    {pl : VerifiableInference.Desc.Place} {P : Johnson.Desc.First.ForkMerge.HeadMergeP}
    {claims : Xi → List Fmt.Drawn → List OnBytes.Model.WsClaim} {weights : W₀ → Weights}
    {k : Coins Bk} {e : String}
    (he : k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k = .error e) :
    k11Lends Bk ch pl P = false := by
  cases hL : k11Lends Bk ch pl P with
  | false => rfl
  | true =>
    obtain ⟨c, hc⟩ := (lentIff Bk W₀ Rc Xi Tr X ch pl P claims weights k).2 hL
    rw [he] at hc
    cases hc

/-- **Where the first text answers.** -/
theorem maskLotAnswers : MaskLotAnswers := by
  intro Bk W₀ Rc Xi Tr X ch pl P claims weights n ν₀ k w hd mask row place
  rcases lent_or_not (k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k) with
    ⟨e, he⟩ | ⟨c, hc⟩
  · rw [(lotsSilent Bk W₀ Rc Xi Tr X ch pl P claims weights n ν₀ 0 0 0 k e he w hd mask row
      place).1, lends_false he]
    rfl
  · have ht : (k11MaskLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n ν₀).txt k w hd mask
        row place =
        (if mask = true ∧ row = 0 ∧ ν₀ ≤ place ∧ place < ν₀ + (2 * P.lay.lk + 2) then
          some (Reading.gl.val ((firstRun c.2.1).getD (place - ν₀) zeroE)) else none) := by
      show (match k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k with
        | .error _ => none
        | .ok c =>
          if mask = true ∧ row = 0 ∧ ν₀ ≤ place ∧ place < ν₀ + (2 * P.lay.lk + 2) then
            some (Reading.gl.val ((firstRun c.2.1).getD (place - ν₀) zeroE))
          else none) = _
      rw [hc]
    rw [ht, (lentIff Bk W₀ Rc Xi Tr X ch pl P claims weights k).1 ⟨c, hc⟩]
    by_cases hf : mask = true ∧ row = 0 ∧ ν₀ ≤ place ∧ place < ν₀ + (2 * P.lay.lk + 2)
    · rw [if_pos hf, decide_eq_true hf]
      rfl
    · rw [if_neg hf, decide_eq_false hf]
      rfl

/-- **Where the second text answers.** -/
theorem indexLotAnswers : IndexLotAnswers := by
  intro Bk W₀ Rc Xi Tr X ch pl P claims weights n r p k w hd mask row place
  rcases lent_or_not (k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k) with
    ⟨e, he⟩ | ⟨c, hc⟩
  · rw [(lotsSilent Bk W₀ Rc Xi Tr X ch pl P claims weights 0 0 n r p k e he w hd mask row
      place).2, lends_false he]
    rfl
  · have ht : (k11IndexLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n r p).txt k w hd mask
        row place =
        (if mask = true ∧ row = r ∧ place = p then
          some (Reading.gl.val ((endRun c.2.1).headD zeroE)) else none) := by
      show (match k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k with
        | .error _ => none
        | .ok c =>
          if mask = true ∧ row = r ∧ place = p then
            some (Reading.gl.val ((endRun c.2.1).headD zeroE))
          else none) = _
      rw [hc]
    rw [ht, (lentIff Bk W₀ Rc Xi Tr X ch pl P claims weights k).1 ⟨c, hc⟩]
    by_cases hf : mask = true ∧ row = r ∧ place = p
    · rw [if_pos hf, decide_eq_true hf]
      rfl
    · rw [if_neg hf, decide_eq_false hf]
      rfl

/-- **At two runs each text answers at the same entries.** -/
theorem lotsAnswerAlike : LotsAnswerAlike := by
  intro Bk W₀ Rc Xi Tr X ch pl P claims weights n ν₀ n' r p k k' w w' hd hd' mask row place
  constructor
  · rw [maskLotAnswers Bk W₀ Rc Xi Tr X ch pl P claims weights n ν₀ k w hd mask row place,
      maskLotAnswers Bk W₀ Rc Xi Tr X ch pl P claims weights n ν₀ k' w' hd' mask row place]
  · rw [indexLotAnswers Bk W₀ Rc Xi Tr X ch pl P claims weights n' r p k w hd mask row place,
      indexLotAnswers Bk W₀ Rc Xi Tr X ch pl P claims weights n' r p k' w' hd' mask row place]

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.k11PublicRow
#print axioms ProofFile.Honest.K11.k11Lends
#print axioms ProofFile.Honest.K11.lendsAtRow
#print axioms ProofFile.Honest.K11.lentIff
#print axioms ProofFile.Honest.K11.lent_or_not
#print axioms ProofFile.Honest.K11.lends_false
#print axioms ProofFile.Honest.K11.maskLotAnswers
#print axioms ProofFile.Honest.K11.indexLotAnswers
#print axioms ProofFile.Honest.K11.lotsAnswerAlike
