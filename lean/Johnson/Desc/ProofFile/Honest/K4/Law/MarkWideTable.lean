-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/MarkWideTable.lean.

What is here. WHICH ROWS OF THE VERIFIER's TABLE OF K4's ROUNDS (OnBytes/Desc/First/K4/Rounds.lean)
THE WIDER MARK (Law/MarkWide.lean) LISTS, BY THE ROWS' NAMES: every row under one of the four names
`.pscEpsilon` (the element that joins a hiding polynomial to a claim), `.pscRound` (the challenge of
a round of a sumcheck), `.batSigma` (the element that batches rows) and `.line` (the point on the
line through two points) draws one element, and none by the rule that never gives 0
(`k4_named_plain`): so its number is listed, but for the one round that the mark leaves out
(`k4WideRounds_named`). Whoever knows a round's name in the table, and that it is not that round,
knows that it is listed: without a number under three of the names (Law/MarkWideStarts.lean,
`k4_not_coin_of_name`); the joining elements' rounds by their numbers in the order of the seven
sumchecks (the same file, `k4Start_listed`). AT EVERY PLAN: no hypothesis on the plan's numbers.
Statements with their proofs: the table's text unfolded.

Not shown here. Which number a named round has. The rows under the names `.zero` and `.join` draw
points: Law/MarkWide.lean (`k4Wide_point`): WHETHER THE ROUND OF THE POINT OVER THE LAYERS WITH
ROUTED EXPERTS IS LISTED AT THE FULL SIZE (it is just where ll − 1 = 1) IS NOT SHOWN HERE (that ll −
1 = 1 there: Law/Live/AtFull.lean, conditional). How many rounds are listed: Law/MarkWideCount.lean.
What the mark's silence gives at any state of the verifier. No property is claimed.

  `k4_named_plain`   the rows under the four names.
  `k4WideRounds_named`   **their numbers are listed, but for the round that is left out.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.MarkWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (pointRd batchRd masked layerRds)
open OnBytes.Desc.First.K4.Honest

/-- Every row of the table under one of the four names draws one element, and none by the rule that
never gives 0. -/
theorem k4_named_plain (P : OnBytes.Model.Layer.Pub) (hp : OnBytes.Model.Layer.HPlan2) (g : Nat) :
    ∀ d ∈ OnBytes.Desc.First.K4.rounds P hp g,
      d.name ∈ [OnBytes.Model.RoundName.pscEpsilon, .pscRound, .batSigma, .line] →
      d.drawn = 1 ∧ d.notZero = 0 := by
  intro d hd hn
  unfold OnBytes.Desc.First.K4.rounds at hd
  simp only [layerRds, masked, List.mem_append, List.mem_cons, List.mem_replicate,
    List.not_mem_nil, or_false] at hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  cases hg : (g == 0) <;> simp only [hg, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
    List.not_mem_nil, or_false] at hd
  all_goals
    casesm* _ ∨ _
    all_goals
      obtain ⟨-, rfl⟩ := hd
      first
        | exact ⟨rfl, rfl⟩
        | (exfalso; cases hn)

/-- CONDITIONAL: on h, hn and hc. **THE NUMBER OF A ROW UNDER ONE OF THE FOUR NAMES IS LISTED, IF IT
IS NOT THE ROUND THAT IS LEFT OUT.** -/
theorem k4WideRounds_named (Q : K4Pub) {i : Nat} {d : OnBytes.Desc.First.K4.Rd}
    (h : (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g)[i]? = some d)
    (hn : d.name ∈ [OnBytes.Model.RoundName.pscEpsilon, .pscRound, .batSigma, .line])
    (hc : i ≠ k4CoinRound Q) : i ∈ k4WideRounds Q :=
  (k4WideRounds_iff Q i).2
    ⟨⟨d, h, k4_named_plain Q.P Q.hp Q.g d (List.mem_of_getElem? h) hn⟩, hc⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_named_plain
#print axioms ProofFile.Honest.K4.k4WideRounds_named
