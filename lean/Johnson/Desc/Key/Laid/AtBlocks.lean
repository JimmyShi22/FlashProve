-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Laid/AtBlocks.lean: from the function to the block. The yes of the third, the sixth
and the eighth of K14's eight blocks (Johnson/Desc/K14/Blocks.lean: `blocks`) gives `RecLaid`,
`Joined` and `SplitLaid`. Theorems; no definition.

OBJECT. The members 2, 5 and 7 (from 0) of the list that `Desc.K14.blocks Q` returns: "(rec_gamma)",
"joins", "SPLIT": the blocks themselves, by their field `decide`. `laid_rec`,
`joined_joins` and `laid_split` speak of the functions `laysRec`, `joins` and `split` of
Johnson/Desc/K14/Text.lean, by which these blocks decide.
USER. A table of the shared chain's joints that holds a piece at such a block and wants "the block's
yes gives the plain facts", in the form `∀ d rs gs d', b.decide d rs gs = .ok d' → ∃ …`. At the key
file's own description: Johnson/RunOne/KeyBridges23.lean.
LETTERS. Q (the place's public parameters), the eight blocks, d d' rs gs: all free. Tied: the eight
are what `blocks Q` returns. `Joined` and `SplitLaid` want besides that the shape splits the row over
two codes.

CAUTION. Each statement has the form "a yes gives": it is true, and says nothing, of a block that
never says yes, and at a Q at which `blocks Q` returns nothing. That the blocks say yes at the key
file's real parameters is shown by no theorem here: a ride on honest files shows it, at the files
that were ridden.

Main names.
  `blocks_eight`: what `blocks Q` returns has just eight members.
  `recLaid_at_blocks`, `joined_at_blocks`, `splitLaid_at_blocks`: the three bridges.
  `split_rounds_at_blocks`: where the shape splits, the eighth block's yes is at just one round.

How. `blocks` is unfolded once; `why_some` (Johnson/Desc/K14/Law/AtBlocks.lean) turns the
block's yes into the function's; "SPLIT"'s one round is `split_one`
(Johnson/Desc/K14/Law/Step.lean). `Q.par.S` is `Q.S` by the text of `P14.par`.

Limits. Nothing on the blocks' tests on the plan, their rounds or their places. Nothing on the five
other blocks. Nothing on soundness or on hiding.
-/
import Johnson.Desc.Key.Laid.Joined
import Johnson.Desc.Key.Laid.Rec
import Johnson.Desc.Key.Laid.Split
import Johnson.Desc.K14.Law.AtBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes
open VerifiableInference.Desc (Block)
open _root_.Desc.K14 (St P14 blocks joins laysRec split)
open _root_.Desc.K14.Law (why_some split_one)

namespace VerifiableInference.Desc.Key

/-- What `blocks Q` returns has just eight members. -/
theorem blocks_eight (Q : P14) (l : List (Block St Unit)) (h : blocks Q = some l) :
    ∃ b1 b2 b3 b4 b5 b6 b7 b8, l = [b1, b2, b3, b4, b5, b6, b7, b8] := by
  unfold blocks at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨_, _, rfl⟩ := h
  exact ⟨_, _, _, _, _, _, _, _, rfl⟩

/-- **The block "(rec_gamma)": its yes gives RecLaid.** -/
theorem recLaid_at_blocks (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∀ d rs gs d', b3.decide d rs gs = .ok d' → ∃ GU rows, RecLaid Q.par d d' GU rows := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  intro d rs gs d' h
  exact laid_rec Q.par d d' rs (why_some h)

/-- **The block "joins": its yes gives Joined**, where the shape splits. -/
theorem joined_at_blocks (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : Q.S.sharedSplitNeeded = true) :
    ∀ d rs gs d', b6.decide d rs gs = .ok d' → ∃ GU GO, Joined d d' GU GO := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  intro d rs gs d' h
  exact joined_joins Q.par d d' rs hS (why_some h)

/-- Where the shape splits, the block "SPLIT" says yes at just one round. -/
theorem split_rounds_at_blocks (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : Q.S.sharedSplitNeeded = true) :
    ∀ d rs gs d', b8.decide d rs gs = .ok d' → ∃ r, rs = [r] := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  intro d rs gs d' h
  exact split_one Q.par d d' rs hS (why_some h)

/-- **The block "SPLIT": its yes gives SplitLaid**, where the shape splits. -/
theorem splitLaid_at_blocks (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : Q.S.sharedSplitNeeded = true) :
    ∀ d rs gs d', b8.decide d rs gs = .ok d' →
      ∃ GU GO x l n row mu, SplitLaid Q.S d d' GU GO x l n row mu := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  intro d rs gs d' h
  have k : split Q.par d rs = some d' := why_some h
  obtain ⟨r, rfl⟩ := split_one Q.par d d' rs hS k
  exact laid_split Q.par d d' r hS k

end VerifiableInference.Desc.Key
