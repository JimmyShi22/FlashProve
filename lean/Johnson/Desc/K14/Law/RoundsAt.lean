-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/RoundsAt.lean: HOW MANY ROUNDS EACH OF THE KIND's EIGHT BLOCKS DECLARES, and so
how many rounds stand in front of each. Theorems.

  rounds_counts   1 · 2 · 0 · 1 · 2 · 0 · 1 · (1 where the shape splits, else 0).
  rounds_front    the rounds in front of the k-th block, k = 0 … 7: 0 · 1 · 3 · 3 · 4 · 6 · 6 · 7:
                  with CutAt.lean | PieceAt.lean: at which round of the chain's data a piece's
                  stretch begins.
Nothing on soundness.

-/
import Johnson.Desc.K14.Law.CutAt
import Johnson.Desc.K14.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (Block)

/-- **The declared rounds, counted, block by block.** -/
theorem rounds_counts (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    [b1, b2, b3, b4, b5, b6, b7, b8].map (·.rounds.length) =
      [1, 2, 0, 1, 2, 0, 1, if P.S.sharedSplitNeeded then 1 else 0] := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  cases h : P.S.sharedSplitNeeded <;>
    simp [entries, rounds, whys, h, sendAt, Block.inside, VerifiableInference.Desc.K1.sendOwn,
      VerifiableInference.Desc.K1.rounds]

/-- **The rounds in front of each block.** -/
theorem rounds_front (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    (List.range 8).map (fun k => roundsIn ([b1, b2, b3, b4, b5, b6, b7, b8].take k)) =
      [0, 1, 3, 3, 4, 6, 6, 7] := by
  have h := rounds_counts P b1 b2 b3 b4 b5 b6 b7 b8 hb
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, _⟩ := h
  simp [roundsIn, List.range, List.range.loop, h1, h2, h3, h4, h5, h6, h7]

end Desc.K14.Law
