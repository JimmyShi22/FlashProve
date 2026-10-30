-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/OpensNone.lean: NO DECLARED ROUND OF THE KIND's EIGHT BLOCKS ON THE SHARED
CHAIN OPENS A TREE. A theorem, by the blocks' own text.

WHY. The rule by which a block of the shared chain is charged once for all slots asks of its
stretch of written rounds: every tree that it opens has a number from the chain's first own tree on
(∀ d ∈ p.ds, ∀ j ∈ d.opens, lo ≤ j). At these eight the list is empty: "LOC" reads columns of the
STORED table (its round's field stored), and no other round reads anything.
  own_opens_none   for each of the eight and each of its declared rounds r: r.opens = [].
FROM THE DECLARED ROUNDS TO THE WRITTEN ONES: RoundIs (Johnson/Desc/Sound/Stretch.lean) has
d.opens = r.opens.map …: so wherever a piece's written rounds go along the block's declared ones
(Along (RoundIs …) b.rounds q.ds) each d.opens is []: that step is not taken here.
What is not claimed. Anything on the two proximity tests, which do open trees. Nothing on soundness.

-/
import Johnson.Desc.K14.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open VerifiableInference.Desc (Block)

/-- **No declared round of the eight opens a tree.** -/
theorem own_opens_none (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∀ x ∈ [b1, b2, b3, b4, b5, b6, b7, b8], ∀ r ∈ x.rounds, r.opens = [] := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  intro x hx r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨e, _, rfl⟩ := List.mem_map.1 hr
    rfl
  · have hr' : r ∈ VerifiableInference.Desc.K1.rounds _ := hr
    simp only [VerifiableInference.Desc.K1.rounds, List.mem_cons, List.not_mem_nil,
      or_false] at hr'
    rcases hr' with rfl | rfl <;> rfl
  · obtain ⟨e, _, rfl⟩ := List.mem_map.1 hr
    rfl
  · obtain ⟨e, _, rfl⟩ := List.mem_map.1 hr
    rfl
  · have hr' : r ∈ VerifiableInference.Desc.K1.rounds _ := hr
    simp only [VerifiableInference.Desc.K1.rounds, List.mem_cons, List.not_mem_nil,
      or_false] at hr'
    rcases hr' with rfl | rfl <;> rfl
  · obtain ⟨e, _, rfl⟩ := List.mem_map.1 hr
    rfl
  · obtain ⟨e, _, rfl⟩ := List.mem_map.1 hr
    rfl
  · obtain ⟨e, _, rfl⟩ := List.mem_map.1 hr
    rfl

end Desc.K14.Law
