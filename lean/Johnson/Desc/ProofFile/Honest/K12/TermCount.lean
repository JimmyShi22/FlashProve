-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TermCount.lean: how many rounds `testAll` (K12/Test.lean) lists,
against how many moves the proximity test's two parts have (K12/Parts.lean). No definition; eight
theorems.

Why. `msgAt` (Parts.lean) takes a round's items from what `testAll` lists, and gives the empty
message, without a warning, beyond it. Both counts are functions of the stages' numbers alone.

  `lenFrom_sum`, `termLen_sum`   `testAll`'s number of rounds as a sum: 3, and h + (k - h) + 3 for
                 every stage but the last
  `twoLens_sum`  the two parts' numbers of rounds together, at two stages or more: 3, and k + 3 for
                 every stage but the last
  `moves_le_termLen`   so the second is never above the first: no hypothesis on h and k
  `moves_eq_termLen`   and they are one where h ≤ k at every stage but the last
  `test_covers`  at every job at two stages or more, every input, front, coins and challenges: the
                 two parts have together no more moves than `testAll` lists rounds
  `test_count`   just as many, where h ≤ k at every stage but the last
  `listed_at`    so no move of the two parts asks `testAll` for a round that it does not list

By what. `length_test` (K12/TermLen.lean); `first_moves`, `rest_moves` (K12/HalfSteps.lean);
the text of `movesFrom` (K12/Parts.lean). In `sgOf` (Johnson/Desc/K12/Law/ChainOf.lean) g is k - h
on the natural numbers: so h + g is the larger of h and k.

Limits.
- That move number n of a part plays the test's round number n, or that number behind the first
  part's, is the form of `first_moves` and `rest_moves`; it is not restated here: `listed_at` speaks
  of a number below the two lengths' sum.
- `msgAt` also reads the list of tables (`O.tr`): not treated. `test_widths` (K12/FitsAll.lean) has
  that list's widths as a function of the stages' numbers.
- One stage or none: not treated.
- Where h > k at a stage but the last, `testAll` lists more rounds than the two parts play: the
  surplus is shown by no move. What the verifier's block declares there is not looked at.
- Nothing on what the rounds hold. It moves no count. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.TermLen
import Johnson.Desc.ProofFile.Honest.K12.HalfSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open H2K.Pub (sgOf)

variable {V W X : Type}

theorem lenFrom_sum : ∀ (rest : List Fmt.M1.Stage) (s : Fmt.M1.Stage),
    lenFrom s rest = 2 + (((s :: rest).dropLast).map fun a => a.h + (a.k - a.h) + 3).sum
  | [], _ => rfl
  | t :: rest, s => by
    show (sgOf s).h + (sgOf s).g + 3 + lenFrom t rest =
      2 + ((s :: (t :: rest).dropLast).map fun a => a.h + (a.k - a.h) + 3).sum
    rw [lenFrom_sum rest t, List.map_cons, List.sum_cons]
    show s.h + (s.k - s.h) + 3 + _ = _
    omega

/-- `testAll`'s number of rounds, at one stage or more. -/
theorem termLen_sum (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) :
    termLen (s :: rest) = 3 + (((s :: rest).dropLast).map fun a => a.h + (a.k - a.h) + 3).sum := by
  show 1 + lenFrom s rest = _
  rw [lenFrom_sum]
  omega

/-- The two parts' numbers of rounds together, at two stages or more. -/
theorem twoLens_sum (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) :
    firstLen (s :: t :: rest) + restLen (s :: t :: rest) =
      3 + (((s :: t :: rest).dropLast).map (·.k + 3)).sum := by
  unfold restLen roundOf
  rw [← List.dropLast_eq_take]
  show (2 + s.k) + (1 + ((s :: (t :: rest).dropLast).map (·.k + 3)).sum + 2 - (2 + s.k)) =
    3 + ((s :: (t :: rest).dropLast).map (·.k + 3)).sum
  rw [List.map_cons, List.sum_cons]
  omega

/-- **No hypothesis on h and k.** -/
theorem moves_le_termLen (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) :
    firstLen (s :: t :: rest) + restLen (s :: t :: rest) ≤ termLen (s :: t :: rest) := by
  rw [twoLens_sum, termLen_sum]
  exact Nat.add_le_add_left (List.sum_le_sum fun a _ => by omega) 3

/-- **Just as many where h ≤ k at every stage but the last.** -/
theorem moves_eq_termLen (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hk : ∀ a ∈ (s :: t :: rest).dropLast, a.h ≤ a.k) :
    firstLen (s :: t :: rest) + restLen (s :: t :: rest) = termLen (s :: t :: rest) := by
  rw [twoLens_sum, termLen_sum]
  refine congrArg (3 + ·) (congrArg List.sum (List.map_congr_left fun a ha => ?_))
  have := hk a ha
  omega

/-- **At every job at two stages or more, every input, front, coins and challenges: the two parts
have together no more moves than `testAll` lists rounds.** -/
theorem test_covers (J : TestJob W X) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: t :: rest) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) :
    (firstPart J : Part V W X).moves.length + (restPart J : Part V W X).moves.length ≤
      (testAll J w fr C D).rs.length := by
  have l1 : (firstPart J : Part V W X).moves.length = firstLen J.p.nums.stages := by
    rw [first_moves J]
    exact (List.length_map _).trans List.length_range
  have l2 : (restPart J : Part V W X).moves.length = restLen J.p.nums.stages := by
    rw [rest_moves J s t rest hst]
    exact (List.length_map _).trans List.length_range
  rw [l1, l2, length_test, hst]
  exact moves_le_termLen s t rest

/-- **Just as many, where h ≤ k at every stage but the last.** -/
theorem test_count (J : TestJob W X) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: t :: rest) (hk : ∀ a ∈ (s :: t :: rest).dropLast, a.h ≤ a.k)
    (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn) :
    (testAll J w fr C D).rs.length =
      (firstPart J : Part V W X).moves.length + (restPart J : Part V W X).moves.length := by
  have l1 : (firstPart J : Part V W X).moves.length = firstLen J.p.nums.stages := by
    rw [first_moves J]
    exact (List.length_map _).trans List.length_range
  have l2 : (restPart J : Part V W X).moves.length = restLen J.p.nums.stages := by
    rw [rest_moves J s t rest hst]
    exact (List.length_map _).trans List.length_range
  rw [l1, l2, length_test, hst]
  exact (moves_eq_termLen s t rest hk).symm

/-- **No move of the two parts asks `testAll` for a round that it does not list.** By `first_moves`
and `rest_moves` the two parts' moves are `moveAt J _ i` at the numbers i below
firstLen + restLen. -/
theorem listed_at (J : TestJob W X) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: t :: rest) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (i : ℕ)
    (hi : i < firstLen J.p.nums.stages + restLen J.p.nums.stages) :
    ∃ r, (testAll J w fr C D).rs[i]? = some r := by
  have hl : i < (testAll J w fr C D).rs.length := by
    rw [length_test, hst]
    rw [hst] at hi
    exact Nat.lt_of_lt_of_le hi (moves_le_termLen s t rest)
  exact ⟨_, List.getElem?_eq_getElem hl⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.lenFrom_sum
#print axioms ProofFile.Honest.K12.termLen_sum
#print axioms ProofFile.Honest.K12.twoLens_sum
#print axioms ProofFile.Honest.K12.moves_le_termLen
#print axioms ProofFile.Honest.K12.moves_eq_termLen
#print axioms ProofFile.Honest.K12.test_covers
#print axioms ProofFile.Honest.K12.test_count
#print axioms ProofFile.Honest.K12.listed_at
