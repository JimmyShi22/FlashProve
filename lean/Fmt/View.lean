-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/View.lean: an untyped view of a chain as a verifier's decision sees it: for each round the items
read and what was drawn; and the opened columns.

Two records; nothing else. No Mathlib.
A protocol's decision can be written on the format's own data, with no typed term: dec : statement →
View → Bool. The generic construction, which leads from a chain's description to the compiled
verifier, makes this view from a typed transcript (`viewOf`, Run/PlanQTypes.lean); a decision
written in Fmt/ takes it from here.

Main names:
  `RoundView`: one round: vals: the items of the prover's message as read, without the roots, in their
    order (`ItemValue`, Fmt/Rules8.lean); drawn: the format's record of what the round draws (`Drawn`,
    Fmt/Rules6Round.lean: elements, positions as drawn, matrix entries, the sealed digest).
  `View`: rounds: the chain's rounds in their order (the description's rounds: no round in front);
    opened: for each own tree that is opened and each position of its list: (the tree's number in
    the order of sending, counted from 0; the position; the column's words). `viewOf`
    (Fmt/M1View.lean) and `viewX` (Fmt/Rules8X.lean) also lay here the columns of other trees: see
    part 1 of the first head, `storedKey` in the second.

Limits: not in the view are roots, nonces, salts, given digests and chain values: what the compiled
verifier tests by itself (work, walks) is no matter of a decision.
Nothing is proved. This file does not say which view belongs to which file: the generic
construction's matter.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules8

namespace Fmt

/-- One round, as a decision sees it. -/
structure RoundView where
  vals  : List ItemValue
  drawn : Drawn

/-- The view. -/
structure View where
  rounds : List RoundView
  /-- Tree (by its number in the order of sending), position, column. -/
  opened : List (Nat × Nat × List UInt64)

end Fmt
