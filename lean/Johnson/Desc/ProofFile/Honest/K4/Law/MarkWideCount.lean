-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/MarkWideCount.lean.

What is here. HOW MANY ROUNDS THE WIDER MARK (Law/MarkWide.lean) LISTS, as a sum of the plan's
numbers (`k4WideRounds_length`): thirteen rounds that stand in the verifier's table of K4's rounds
at every plan (six of the seven joining elements: the second token sumcheck's is left out; four
batching elements; three points on the line through two points), the challenges of the variables of
the seven masked sumchecks (muV + lt + lt + lamS + muH + muH2 + lk), and one more for each of the
rounds that draw a point where that point has one coordinate. AT EVERY PLAN: no hypothesis.
Statements with their proofs: the table's text unfolded and counted (`k4_plain_count`: fourteen and
the rest); the round that is left out is one of the rows counted, and stands there once.

Not shown here. The sum is evaluated at no plan. The mark's share is written as a product in this
number; it is a stated number and no bound. No property is claimed.

  `k4One n`   1 where n = 1, else 0.
  `k4_plain_count`   the table's rows that draw one element by the plain rule, counted.
  `k4_filter_ne_length`   a list without doubles, less one of its members, is one shorter.
  `k4WideRounds_length`   **the number of listed rounds.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.MarkWideTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (pointRd batchRd masked layerRds)
open OnBytes.Desc.First.K4.Honest

/-- 1 where n = 1, else 0. -/
def k4One (n : Nat) : Nat := if n = 1 then 1 else 0

/-- The table's rows that draw one element, and none by the rule that never gives 0, counted. -/
theorem k4_plain_count (P : OnBytes.Model.Layer.Pub) (hp : OnBytes.Model.Layer.HPlan2) (g : Nat) :
    (OnBytes.Desc.First.K4.rounds P hp g).countP k4PlainOne =
      14 + P.rd.muV + 2 * P.y.h.lt + hp.lamS + P.rd.muH + P.rd.muH2 + P.wsLay.lk +
        k4One P.y.h.lt +
        (if g == 0 then k4One (P.y.ls + P.y.h.lt) + k4One (P.y.lPd - P.y.ls) else 0) +
        k4One P.rd.lNI + k4One (P.y.h.ll - 1) := by
  unfold OnBytes.Desc.First.K4.rounds
  cases hg : (g == 0) <;>
    simp [layerRds, masked, pointRd, batchRd, k4PlainOne, k4One, List.countP_append,
      List.countP_cons, List.countP_replicate, List.countP_nil] <;>
    omega

/-- CONDITIONAL: on the two hypotheses. A list without doubles, less one of its members, is one
shorter. -/
theorem k4_filter_ne_length : ∀ (l : List Nat) (a : Nat), l.Nodup → a ∈ l →
    (l.filter fun i => i != a).length + 1 = l.length
  | [], _, _, h => by cases h
  | x :: l, a, hn, h => by
    obtain ⟨hx, hl⟩ := List.nodup_cons.1 hn
    by_cases e : x = a
    · subst e
      have t : (l.filter fun i => i != x) = l :=
        List.filter_eq_self.2 fun i hi => bne_iff_ne.2 fun ei => hx (ei ▸ hi)
      rw [List.filter_cons_of_neg (p := fun i => i != x) (by simp), t, List.length_cons]
    · have ha : a ∈ l := (List.mem_cons.1 h).resolve_left fun e' => e e'.symm
      rw [List.filter_cons_of_pos (p := fun i => i != a) (bne_iff_ne.2 e), List.length_cons,
        List.length_cons, k4_filter_ne_length l a hl ha]

/-- **THE NUMBER OF LISTED ROUNDS.** -/
theorem k4WideRounds_length (Q : K4Pub) :
    (k4WideRounds Q).length =
      13 + Q.P.rd.muV + 2 * Q.P.y.h.lt + Q.hp.lamS + Q.P.rd.muH + Q.P.rd.muH2 + Q.P.wsLay.lk +
        k4One Q.P.y.h.lt +
        (if Q.g == 0 then k4One (Q.P.y.ls + Q.P.y.h.lt) + k4One (Q.P.y.lPd - Q.P.y.ls) else 0) +
        k4One Q.P.rd.lNI + k4One (Q.P.y.h.ll - 1) := by
  obtain ⟨d, hd, hn⟩ := k4CoinRound_row Q
  obtain ⟨h1, h2⟩ := k4_named_plain Q.P Q.hp Q.g d (List.mem_of_getElem? hd)
    (by rw [hn]; exact List.mem_cons_self)
  have hp : k4PlainOne d = true := by
    unfold k4PlainOne
    rw [h1, h2]
    rfl
  have hm : k4CoinRound Q ∈ k4Listed k4PlainOne 0 (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g) :=
    (k4Listed_mem _ _ _ _).2 ⟨k4CoinRound Q, d, by omega, hd, hp⟩
  have e := k4_filter_ne_length _ _ (k4Listed_nodup k4PlainOne _ 0) hm
  rw [k4Listed_length, k4_plain_count] at e
  unfold k4WideRounds
  omega

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_plain_count
#print axioms ProofFile.Honest.K4.k4_filter_ne_length
#print axioms ProofFile.Honest.K4.k4WideRounds_length
