-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Shared/PricesShared.lean: WHICH PRICE OF THE PLAN BELONGS TO WHICH ROUND OF WHICH BLOCK: as
terms. Definitions with code; nothing is proved. (`wholePricesOf`: the price WITH the draws' distance from
uniform, which is what the planner's own verdict on a round compares.) No Mathlib.

Why. A law of a chain's blocks "at the plan's prices" has to name, for each block and each of its rounds,
one number of the plan. The plan of a chain is a list of rounds, each with its entry (name and eleven
words) and its price (`PlanRound.error`: an upper bound on the round's error, work not counted:
OnBytes/Params/Planner.lean). A block declares its rounds by the same entries (`Block.rounds`).

  `entriesOf bs`: the blocks' declared rounds' entries, in a row.
  `roundsArePlans bs P`: A TEST: they are, entry for entry and field for field, the plan's rounds'.
  `offsetOf bs k`: how many rounds stand in front of block number k.
  `pricesOf bs P k`: THE PLAN's PRICES OF BLOCK NUMBER k's ROUNDS, in order. `worksOf`: their bits of work.
  `wholePricesOf bs P k`: THE SAME WITH THE DISTANCE FROM UNIFORM OF THE FIELD ELEMENTS THAT A ROUND DRAWS (the planner's `wholeError`, at the plan's own
    setting and unit): THE NUMBER THAT `roundHolds` HOLDS AGAINST 2 ^ (work − target). With hundredths of a bit of room in many rounds the
    difference counts: A LAW "AT THE PLAN's PRICES" IS MEANT AT THESE.

WHAT OF `verify-on-bytes` IS REACHED: the planner's plain structures `Planned`, `PlanRound`,
`Binary` (data), and two of its routines, `wholeError` and `capped`, which `wholePricesOf` calls.

Limits. (1) Where the test says no, `pricesOf` means nothing. (2) A price is a share of a round's
challenges, as a binary number; a block's error in the rule of composition is a COUNT of the written
round's challenges: how a price, the round's bits of work and the distance from uniform of its draws
become such a count is another row's matter (the reading of a round): it enters
Johnson/Desc/Sound/PricesSharedQ.lean as a letter. (3) The plan is the plan as made.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Block
import OnBytes.Params.Planner

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Shared
open VerifiableInference.Desc OnBytes.Params

variable {S Cl : Type}

/-- The blocks' declared rounds' entries, in a row. -/
def entriesOf (bs : List (Block S Cl)) : List Fmt.Entry := bs.flatMap fun b => b.rounds.map (·.entry)

/-- A TEST: the blocks' declared rounds, in a row, are the plan's rounds. -/
def roundsArePlans (bs : List (Block S Cl)) (P : Planned) : Bool :=
  decide (entriesOf bs = P.rounds.map (·.entry))

/-- How many rounds stand in front of block number k. -/
def offsetOf (bs : List (Block S Cl)) (k : Nat) : Nat := ((bs.take k).map (·.rounds.length)).sum

/-- The plan's rounds of block number k. -/
def planRoundsOf (bs : List (Block S Cl)) (P : Planned) (k : Nat) : List PlanRound :=
  (P.rounds.drop (offsetOf bs k)).take ((bs[k]?.map (·.rounds.length)).getD 0)

/-- **The plan's prices of block number k's rounds.** -/
def pricesOf (bs : List (Block S Cl)) (P : Planned) (k : Nat) : List Binary :=
  (planRoundsOf bs P k).map (·.error)

/-- **The same, with the draws' distance from uniform: what the planner's verdict on a round compares.** -/
def wholePricesOf (bs : List (Block S Cl)) (P : Planned) (k : Nat) : List Binary :=
  (planRoundsOf bs P k).map (wholeError P.set (capped P.set))

/-- Their bits of work. -/
def worksOf (bs : List (Block S Cl)) (P : Planned) (k : Nat) : List Nat :=
  (planRoundsOf bs P k).map (·.entry.work)

end VerifiableInference.Desc.Shared
