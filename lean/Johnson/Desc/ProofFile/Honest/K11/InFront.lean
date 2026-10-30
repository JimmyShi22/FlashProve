-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/InFront.lean: the proofs of the three statements of
Honest/K11/InFrontStatement.lean, to the letter. Lemmas; none of the library's goals.

How. The first: by induction on the list of blocks. The other two: CLOSED FACTS, BY EVALUATION IN
LEAN's KERNEL (`decide +kernel`), each under a raised depth of recursion, as the library's own two
lemmas near them stand.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.InFrontStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc.K13.Honest (roundsAhead roundsAhead_zero)

/-- **The rounds in front of a place are those of the blocks in front of its first block.** -/
theorem roundsInFrontIs : RoundsInFrontIs := by
  intro S Cl bs
  induction bs with
  | nil =>
    intro a j _ hj
    exact absurd hj (Nat.not_lt_zero j)
  | cons b bs ih =>
    intro a j hi hj
    have hi2 : (bif b.place == a then 0 else (bs.map (·.place)).idxOf a + 1) = j := by
      rw [← List.idxOf_cons]
      exact hi
    cases hb : (b.place == a) with
    | true =>
      rw [hb] at hi2
      have h0 : 0 = j := hi2
      subst h0
      rw [roundsInFront, if_pos hb]
      exact congrArg some (roundsAhead_zero (b :: bs)).symm
    | false =>
      rw [hb] at hi2
      have hi' : (bs.map (·.place)).idxOf a + 1 = j := hi2
      subst hi'
      have hn : ¬ (b.place == a) = true := by
        rw [hb]
        exact Bool.false_ne_true
      have h1 := ih a _ rfl (by rw [List.length_cons] at hj; omega)
      rw [roundsInFront, if_neg hn, h1, Option.map_some]
      unfold roundsAhead
      rw [List.take_succ_cons, List.flatMap_cons, List.length_append]
      exact congrArg some (Nat.add_comm _ _)

set_option maxRecDepth 1000000 in
/-- **The lookup on the head's calls stands first at number 340 of the written list.** -/
theorem callsPlace_at_full : CallsPlaceAtFull := by
  unfold CallsPlaceAtFull
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The head's own sub-protocol stands first at number 341 of the written list.** -/
theorem headOwnPlace_at_full : HeadOwnPlaceAtFull := by
  unfold HeadOwnPlaceAtFull
  decide +kernel

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.roundsInFrontIs
#print axioms ProofFile.Honest.K11.callsPlace_at_full
#print axioms ProofFile.Honest.K11.headOwnPlace_at_full
