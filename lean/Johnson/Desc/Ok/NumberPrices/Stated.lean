-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/NumberPrices/Stated.lean: towards the row `number_prices` of
a list that is not in this library: every
round's price in a finished plan that passes a public test is, with the round's work counted, within
the bound on a round's error ((1/2)^128; the name roundError of
Ladder/NumberEps/Stated.lean [not in this library]), and
the plan of the stored full-size files passes the test.

WHERE THINGS STAND. No file under this folder imports a file under Ladder/: where the three public
files occur they are the letters pol, lay, KL; where a bound on a round's error occurs it is a
literal. `PricesAtRelease`, `PricesAtGap`, `PricesRungs`, `pricesRungs`, `PricesNamed`,
`pricesNamed_of`, `prices_at_release`, `below_step`, `pricedAt_of_release`, wherever a head under
this folder names them, stand in Johnson/Goal/Numbers/NumberPricesAt.lean [not in this library].

Definitions and one statement, `PricesGeneral`. `PricesAt`, of three public files, stands in
Johnson/Desc/Ok/NumberPrices/AtRelease.lean; `PricesRungs`, `PricesAtRelease` and `PricesNamed` in
Johnson/Goal/Numbers/NumberPricesAt.lean [not in this library]. The proof of `PricesGeneral` is in
Johnson/Desc/Ok/NumberPrices/Proved.lean, with `rungsLit`, which is `PricesRungs` in literals.
`PricesAtRelease` IS STATED AND NOT PROVED, and so `PricesNamed` is not proved. `PricesGeneral` and
`PricesRungs` are tools: they name no file, no description and no routine of the planner, and would
stand as they are if the protocol were another. `PricesAtRelease` is of the release's plan and of
the rounds' data that are made of it; it names no description. NO LINE FOR
THE LIST's FILE OF STATEMENTS (NOT IN THIS LIBRARY) IS GIVEN
HERE. The row speaks of written rounds. In `PricesNamed` a written round occurs only under "for all
written rounds that are aligned with the plan": that the one description's written rounds are the
priced rounds is a further part, which is not in it. What is had of that part, at the rounds' data
that are made of the public files, is in Johnson/Desc/Ok/NumberPrices/AtData.lean; `PricesAtRelease`
asks what the theorems there need. Until the part stands, `PricesNamed` is not the row's statement.

Main names (all in the namespace `VerifiableInference.Number`):
  `price P r`: the planner's number for the error of the round r of the plan P, with its term for
    the distance from uniform of the round's draws (`wholeError`, OnBytes/Params/Planner.lean), as a
    rational number. The round's proof of work is not counted in it.
  `PricesOf w P`. For every round r of P: (G1) price P r / 2^work ≤ (1/2)^128; (G2) (1 + 2^-128)^(3
    drawE) (r.error / 2^work) ≤ (1/2)^128; (G3) price P r ≤ 2^w (1/2)^128. And place by place (G4):
    for written rounds ds whose entries are those of the plan's rounds of the chain, one by one
    (`Aligned`), for each written round d and its round r, every count that is at most r.error times
    the number of the round's typed values is, times the sampler's weight, at most 2 ^ -128 times
    the number of d's written verifier messages.
  `PricesGeneral`: PricesOf w P for every w and every plan P with `Desc.chainOk w P` = true.
The tests are those of Johnson/Desc/MadeOk.lean, by name; no second text of them stands here:
  `Desc.chainOk w P`: the planner's verdict (`Planned.holds`); the side conditions `sideB`
    (OnBytes/Flat/HeldAll.lean); the target is 128; no round has more than w bits of work.
  `Desc.madeOk c`: the key has three plans and the proof three; `Desc.chainOk` at each of the seven,
    with w = 32 at the key's three and the entry's, and 20, 28, 20 at the proof's; the parameter
    file's line on slots says `Desc.slots`, which is 64. It asks more, which is not used here: see
    its own file.
  `Desc.fitOk c` (Johnson/Desc/FitOk.lean): the plans of the seven chains fit the format's words.
  `PricesRungs` (Johnson/Goal/Numbers/NumberPricesAt.lean [not in this library]): 64 (1/2)^128 ≤
    (1/2)^122, in rational
    numbers, and `Desc.slots` times 2 ^ -128 is at most 2 ^ -122.
  `PricesAtRelease` (Johnson/Goal/Numbers/NumberPricesAt.lean [not in this library]): at the stored
    full-size files
    (`VerifierAndGoals.storedPublicFiles`) the plan is made, `Desc.madeOk` and `Desc.fitOk` say yes of it, the data of the
    key file's and of the proof file's rounds are made of it (`dataKAt`, `dataPAt`,
    Johnson/G/RoundsOfPlan.lean), and neither are the data of three empty lists: the third list of
    each has a round.
  `PricesNamed` (Johnson/Goal/Numbers/NumberPricesAt.lean [not in this library]): the three
    together, closed.

Limits: `PricesGeneral` is a law on a record: P is any record, whatever routine made it; a routine
written for the purpose could close the same entries at other errors. It does not say that a price
bounds any count or any prover's chance: in (G4) that is the premise on the count. It holds idly of
a plan with no rounds and of a plan whose errors are all 0
(Johnson/Desc/Ok/NumberPrices/Teeth.lean). In (G1), (G2) and (G4) the work is counted as the written
round counts it: of the 2^work strings of test bits one passes; nothing on what that is worth
against many tries. (G4) passes over the entry under the name RECORD, which is no round of the
chain. Nothing says that a description asks `Desc.madeOk`, nor that the written rounds of a
description are aligned with the made plan. `Desc.slots` is tied to the parameter file's line on
slots alone: nothing here ties it to the number of slots of a batch protocol. No sum over rounds.
Nothing on the C++ planner.

What of OnBytes/Model/ is used: no statement of this file names anything of it. The file imports
Johnson/Desc/Ok/NumberPrices/AtRelease.lean, whose `PricesAt` does: see its head.


-/
import OnBytes.Flat.HeldAll
import Johnson.Desc.Ok.NumberPrices.AtRelease

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number
open _root_.Iop Prob _root_.Run OnBytes.Params OnBytes.Slice OnBytes.Flat.Held
open scoped ENNReal

/-- A round's price: the planner's number for its error, with the distance from uniform of its
draws; the round's proof of work not counted. -/
def price (P : Planned) (r : PlanRound) : ℚ := (wholeError P.set (capped P.set) r).val

/-- `PricesOf`: four clauses on one plan. w: a bound on the bits of work of a round. -/
def PricesOf (w : ℕ) (P : Planned) : Prop :=
  (∀ r ∈ P.rounds,
    -- (G1) the price, work counted
    price P r / 2 ^ r.entry.work ≤ (2⁻¹ : ℚ) ^ 128 ∧
    -- (G2) the round's own error, work counted, with the sampler's bias for the drawn elements
    (1 + (2 : ℚ) ^ (-128 : ℤ)) ^ (3 * r.entry.drawE) * (r.error.val / 2 ^ r.entry.work) ≤
      (2⁻¹ : ℚ) ^ 128 ∧
    -- (G3) the price, work not counted
    price P r ≤ (2 : ℚ) ^ w * (2⁻¹ : ℚ) ^ 128) ∧
  -- (G4) place by place, against written rounds
  (∀ ds : List PQ.RD, Aligned ds P →
    List.Forall₂ (fun d r => ∀ count : ℕ,
      (count : ℚ) ≤ r.error.val * (nVals (Fmt.dsOf d.entry d.kind) : ℚ) →
        ((count * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤
          ((2 : ℝ≥0∞)⁻¹ ^ 128) * (Fintype.card (wRound d).Chal : ℝ≥0∞)) ds (chainRounds P))

/-- Of every finished plan that passes the public test. -/
def PricesGeneral : Prop :=
  ∀ (w : ℕ) (P : Planned), Desc.chainOk w P = true → PricesOf w P

end VerifiableInference.Number
