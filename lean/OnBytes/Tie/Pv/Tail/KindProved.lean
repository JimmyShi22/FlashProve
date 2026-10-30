-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/KindProved.lean: which place of the program's own list of links has a link of
which kind: the step that OnBytes/Tie/Pv/Tail/KindRows.lean types, with its proof.

OnBytes/Tie/Pv/Keeps/LinksOrder.lean goes from a group to its places: the link of the layers of
group g, that of its attention and the head's stand at places that it names, and the list has no
further place. Here the direction is turned: a place of the list is the head's or lies below it;
below it the quotient by 1 or 2 is a group that has its plans, and the remainder says which of the
group's links stands there. A link keeps its plan's routine by definition.

Main names:
  `place_kind_attention_size`: where the proof covers attention and the list is made, the public
    record has one attention plan for each group.
  `place_kind_with`, `place_kind_without`: the step where the proof covers attention, and where
    it does not.
  `place_kind`: `KindRows.row_place_kind`.

Limits: on the routine of the link at each place of the list that `Verify.linksOf` returns, and on
nothing else: not on the link's other fields, not on what a routine does, and not on the order in
which the planner (`Verify.linkRounds`) is called.


-/
import OnBytes.Tie.Pv.Tail.KindRows
import OnBytes.Tie.Pv.Keeps.LinksOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.KindProved
open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.L5.LinksOrder

variable {V : Verify.Public} {cov : Head.Covered} {ls : Array LinkH}

/-- Where the proof covers attention and the list is made, the public record has one attention plan
for each group. -/
theorem place_kind_attention_size (h : Verify.linksOf V cov = .ok ls) (hq : V.p4 = true) :
    V.A.size = V.NGr := by
  unfold Verify.linksOf at h
  rw [hq] at h
  simpa using (listLinksH_with _ _ _ _ _ h).2.1

/-- The step where the proof covers attention: two places for each group, then the head's. -/
theorem place_kind_with (h : Verify.linksOf V cov = .ok ls) (hq : V.p4 = true) (l : Nat)
    (X : LinkH) (hX : ls[l]? = some X) :
    (l = 2 * V.NGr ∧ X.run = (Verify.headPlanOf V cov).run) ∨
    (l < 2 * V.NGr ∧ l % 2 = 0 ∧ ∃ hp, V.G[l / 2]? = some hp ∧
      X.run = (Verify.layersPlanOf V cov.tokv (l / 2) hp).run) ∨
    (l < 2 * V.NGr ∧ l % 2 ≠ 0 ∧ ∃ a, V.A[l / 2]? = some a ∧
      X.run = (Verify.attentionPlanOf a).run) := by
  obtain ⟨hG, hs⟩ := linksOf_size h
  have hA := place_kind_attention_size h hq
  have hl : l < ls.size := (Array.getElem?_eq_some_iff.1 hX).1
  rw [if_pos hq] at hs
  rcases Nat.lt_or_ge l (2 * V.NGr) with hlt | hge
  · by_cases hr : l % 2 = 0
    · have hg : l / 2 < V.G.size := by omega
      have hh := linksOf_layers h _ _ (Array.getElem?_eq_getElem hg)
      unfold layersLink at hh
      rw [if_pos hq, show 2 * (l / 2) = l by omega, hX] at hh
      exact .inr (.inl ⟨hlt, hr, _, Array.getElem?_eq_getElem hg,
        congrArg LinkH.run (Option.some.inj hh)⟩)
    · have hg : l / 2 < V.A.size := by omega
      have hh := linksOf_attention h hq _ _ (Array.getElem?_eq_getElem hg)
      rw [show 2 * (l / 2) + 1 = l by omega, hX] at hh
      exact .inr (.inr ⟨hlt, hr, _, Array.getElem?_eq_getElem hg,
        congrArg LinkH.run (Option.some.inj hh)⟩)
  · have e : l = 2 * V.NGr := by omega
    have hh := linksOf_head h
    rw [if_pos hq, ← e, hX] at hh
    exact .inl ⟨e, congrArg LinkH.run (Option.some.inj hh)⟩

/-- The step where the proof does not cover attention: one place for each group, then the
head's. -/
theorem place_kind_without (h : Verify.linksOf V cov = .ok ls) (hq : ¬ V.p4 = true) (l : Nat)
    (X : LinkH) (hX : ls[l]? = some X) :
    (l = V.NGr ∧ X.run = (Verify.headPlanOf V cov).run) ∨
    (l < V.NGr ∧ ∃ hp, V.G[l]? = some hp ∧
      X.run = (Verify.layersPlanOf V cov.tokv l hp).run) := by
  obtain ⟨hG, hs⟩ := linksOf_size h
  have hl : l < ls.size := (Array.getElem?_eq_some_iff.1 hX).1
  rw [if_neg hq] at hs
  rcases Nat.lt_or_ge l V.NGr with hlt | hge
  · have hg : l < V.G.size := by omega
    have hh := linksOf_layers h _ _ (Array.getElem?_eq_getElem hg)
    unfold layersLink at hh
    rw [if_neg hq, hX] at hh
    exact .inr ⟨hlt, _, Array.getElem?_eq_getElem hg, congrArg LinkH.run (Option.some.inj hh)⟩
  · have e : l = V.NGr := by omega
    have hh := linksOf_head h
    rw [if_neg hq, ← e, hX] at hh
    exact .inl ⟨e, congrArg LinkH.run (Option.some.inj hh)⟩

/-- Which place of the program's own list of links has a link of which kind. -/
theorem place_kind : KindRows.row_place_kind := by
  intro V cov ls h l X hX
  by_cases hq : V.p4 = true
  · have hst : Fo.BatRows.stepOf V = 2 := if_pos hq
    rw [hst]
    exact place_kind_with h hq l X hX
  · have hst : Fo.BatRows.stepOf V = 1 := if_neg hq
    rw [hst, Nat.one_mul, Nat.mod_one, Nat.div_one]
    rcases place_kind_without h hq l X hX with a | ⟨a, b⟩
    · exact .inl a
    · exact .inr (.inl ⟨a, rfl, b⟩)

end OnBytes.Tie.Pv.Tail.KindProved
