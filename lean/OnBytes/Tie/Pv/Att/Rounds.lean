-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/Rounds.lean: what the loops of attention's two kinds of sumcheck have heard and
done, where they succeed.

sc3Rounds and scdRounds (OnBytes/Model/AttentionSums.lean) run one round of a masked sumcheck after
the other. If such a loop succeeds from a state and a context, then: the rounds that were closed are
those of the block's own listener (hearMany), with as many scalars as the degree says; the
sumcheck's record has stepped through these rounds under plain weights (`Stepped`); the challenges
were pushed in the order of the rounds; and just as many slots were taken as scalars were sent.

Main names:
  `sc3Rounds_ok`: n rounds with 3 scalars each, under Weight.plain 4.
  `scdRounds_ok`: one round for each degree d of the list, with d scalars, under Weight.plain (d +
    1); every degree lies from 1 to 64.

Limits: one direction: from the loop's success. On a view and in the dry run alike.
-/
import OnBytes.Model.AttentionSums
import OnBytes.Tie.Pv.Psc.Run.PscLoops
import OnBytes.Tie.Pv.Att.Flat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Attention
open OnBytes.Psc (Weight hearMany)

theorem sc3Rounds_ok : ∀ (n : Nat) (p : Psc) (a : Array E) (x : Array E × Psc) (F G : Fork)
    (c c' : Ctx), sc3Rounds n p a F c = .ok ((x, G), c') →
    ∃ rs : List (List E × E),
      (hearMany (List.replicate n 3)).Yields c rs c' ∧
      Stepped p x.2 (List.replicate n (Weight.plain 4)) rs ∧
      x.1.toList = a.toList ++ rs.map (·.2) ∧ G = taken F (3 * n)
  | 0, p, a, x, F, G, c, c', h => by
    simp only [sc3Rounds] at h
    obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 h
    rw [e1, e2, e3]
    exact ⟨[], hearMany_nil _, Stepped.nil _, by simp, rfl⟩
  | n + 1, p, a, x, F, G, c, c', h => by
    simp only [sc3Rounds] at h
    obtain ⟨⟨r, q⟩, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
    obtain ⟨w, sent, b1, _, y1, s1, g1⟩ := roundIn_stepped _ _ _ _ _ _ _ _ _ _ h1
    rw [weight_sum3] at b1
    have hw := Option.some.inj b1
    rw [← hw] at y1 s1 g1
    obtain ⟨rs, y2, s2, r2, g2⟩ := sc3Rounds_ok n _ _ _ _ _ _ _ k1
    refine ⟨(sent, r) :: rs, ?_, ?_, ?_, ?_⟩
    · exact hearMany_append [3] _ _ _ _ _ _ y1 y2
    · exact s1.trans s2
    · rw [r2]; simp
    · rw [g2, g1, taken_taken]
      show taken F (3 + 3 * n) = _
      rw [show 3 + 3 * n = 3 * (n + 1) by omega]

theorem scdRounds_ok : ∀ (ds : List Nat) (p : Psc) (a : Array E) (x : Array E × Psc) (F G : Fork)
    (c c' : Ctx), scdRounds ds p a F c = .ok ((x, G), c') →
    ∃ rs : List (List E × E),
      (hearMany ds).Yields c rs c' ∧
      Stepped p x.2 (ds.map fun d => Weight.plain (d + 1)) rs ∧
      x.1.toList = a.toList ++ rs.map (·.2) ∧ G = taken F ds.sum ∧ ∀ d ∈ ds, 1 ≤ d ∧ d ≤ 64
  | [], p, a, x, F, G, c, c', h => by
    simp only [scdRounds] at h
    obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 h
    rw [e1, e2, e3]
    exact ⟨[], hearMany_nil _, Stepped.nil _, by simp, rfl, by simp⟩
  | d :: ds, p, a, x, F, G, c, c', h => by
    simp only [scdRounds] at h
    obtain ⟨⟨r, q⟩, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
    obtain ⟨w, sent, b1, _, y1, s1, g1⟩ := roundIn_stepped _ _ _ _ _ _ _ _ _ _ h1
    have hd : 1 ≤ d ∧ d ≤ 64 := by
      by_contra hn
      rw [weight_nodes_none zeroE d (by omega)] at b1
      exact absurd b1 (by simp)
    rw [weight_nodes zeroE d hd.1 hd.2] at b1
    have hw := Option.some.inj b1
    rw [← hw] at y1 s1 g1
    obtain ⟨rs, y2, s2, r2, g2, o2⟩ := scdRounds_ok ds _ _ _ _ _ _ _ k1
    refine ⟨(sent, r) :: rs, ?_, ?_, ?_, ?_, ?_⟩
    · exact hearMany_append [d] _ _ _ _ _ _ y1 y2
    · exact s1.trans s2
    · rw [r2]; simp
    · rw [g2, g1, taken_taken]
      show taken F (d + ds.sum) = _
      rw [List.sum_cons]
    · intro u hu
      rcases List.mem_cons.1 hu with rfl | hu
      · exact hd
      · exact o2 u hu

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.sc3Rounds_ok
#print axioms OnBytes.Tie.Pv.Att.scdRounds_ok
