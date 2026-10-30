-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/MadeOk.lean: the public test on the prices of a finished plan.

A file's description (`FileDescription`, Johnson/Desc/Block.lean) holds the plan's declared rounds. It
holds no price: the planner's bound on a round's error stands in the planner's own record
(`PlanRound.error`, OnBytes/Params/Planner.lean). So nothing in a description says that its rounds
are priced at the target. This file has the test that says so, with code, on the planner's record
alone. A description asks it through its field `fileOk`, which is filled where the description is
made.

What is here.
  `chainOk w P`: of one chain's finished plan P. Every round holds at the target, work counted, and
    the plan's other two verdicts (`Planned.holds`); the side conditions of the law on a
    round (`sideB`, OnBytes/Flat/HeldAll.lean: the format's prime and the extension's degree 3; at
    each round: logN ≤ 64; no more elements are marked as never 0 than are drawn; work + 66 ≤ target
    where an element is drawn); the target is 128; no round has more than w bits of work.
  `workPlaced P`: a round that has work is priced by the argument on drawn positions
    (`ErrorKind.query`), and its entry draws a position. `chainOk` bounds how many bits of work a
    round may count, not at which rounds: a parameter file that states work for rounds of other
    kinds, within the bounds, passes `chainOk`, and each such round is then priced at the target
    less its work. The release counts work at the rounds on positions alone.
  `chainAll w P`: `chainOk w P`; `Number.smallOk P` (Johnson/Flat/SmallOk.lean): a round that draws
    matrix entries over -1, 0, 1 draws nothing else, a multiple of 128 of them, and has no work
    (such a round's price stands exactly at the target: it has no room for the distance from uniform
    of another draw, nor for work; of a plan without such a round it says yes idly); and
    `workPlaced P`.
  `keyOk`, `entryOk`, `proofOk`: `chainAll` at one file's own chains, with that file's bounds on
    work: 32, 32, 32 at the key file's three chains; 32 at the entry file's; 20, 28, 20 at the proof
    file's. `proofOk` also asks that the public files state 64 slots: an error of the chain that the
    requests of a batch share counts once for each slot.
  `madeOk`: all seven chains.
  `madeOk_iff`: it is the three files' tests together. `chainAll_iff`, `workPlaced_iff`: what these
    two say, as propositions.

`madeOk` has a clause for each of the seven chains of the three files, and the clause on the slots.
It does not say that a plan has rounds that draw matrix entries, nor how many.

Five numbers are written out here: the target 128, the bounds on work, 20, 28 and 32, and the 64
slots. The bounds are the release's policy on work, by scope: 20 for a chain of one request, 28 for
a chain that requests share, 32 for a chain that is made once. A parameter file that asks more work
than that, or another number of slots, is refused by this test: by design.

Limits. No theorem on what the test gives is here. `Planned.holds` is asked already where the
planner hands a plan out (`finishHeld`), and a target below 128 is refused there too where the
planner's caller leaves its own bound on the target at 128 (`configure`,
OnBytes/Params/Configure.lean); a target above 128, the side conditions, the bounds on work and
where work is counted are asked by nothing else.
  * A round's `error` and `why` are the planner's own words, and these tests take any record of the
    type: the planner's record with every error struck to 0 passes. So the level hangs on two
    things: this test, and that the record tested is the planner's at the public files, which is
    asked where the description is made. In the planner's own records a round's work is its kind's
    line of the parameter file (`close`, OnBytes/Params/Planner.lean): there `why` is no free
    word.
  * The level stands in two numerals of this file: the target 128 and the bounds on work. The target
    that `Planned.holds` reads is the parameter file's own line: a file that lowers it passes
    `holds` at the lower level; beside `configure`'s own bound, the clause on 128 refuses it.
  * Lines of the parameter file that move a price and that nothing here pins: which reading of the
    assumed theorem on codes is taken, the cost of a row, the answers to a sample, and on which
    footing a count of close words stands. The planner prices each as it is stated. The salt's
    length moves no price, and nothing here pins it either.
  * The test speaks of one round at a time. It does not add the rounds' errors up: what holds of a
    whole file would follow from the bound at each step through a general theorem on the compiled
    verifier, not from a sum over rounds. No such theorem is named or used here.
  * A round on positions may also draw an element behind them. It has one `why`, so its work
    discounts that share of its error too; `sideB`'s clause work + 66 ≤ target stands there.
-/
import OnBytes.Flat.HeldAll
import OnBytes.Params.Configure
import Johnson.Flat.SmallOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
open OnBytes.Params OnBytes.Flat.Held

/-- The public test on one chain's finished plan. w: the most bits of work of a round. -/
def chainOk (w : ℕ) (P : Planned) : Bool :=
  P.holds && sideB P && decide (P.set.target = 128) &&
    P.rounds.all fun r => decide (r.entry.work ≤ w)

/-- Work is counted at one kind of round alone: a round that has work is priced by the argument on
drawn positions, and its entry draws a position. The first half reads the planner's own word on the
round; the second reads the entry, which a reader of the files reads too. -/
def workPlaced (P : Planned) : Bool :=
  P.rounds.all fun r => r.entry.work == 0 || (r.why == .query && r.entry.poss != 0)

/-- `chainOk`; `Number.smallOk` (Johnson/Flat/SmallOk.lean): a round that draws matrix entries draws
nothing else, a multiple of 128 of them, and has no work; and `workPlaced`. -/
def chainAll (w : ℕ) (P : Planned) : Bool := chainOk w P && Number.smallOk P && workPlaced P

/-- The test at the key file's three chains. False unless there are just three. -/
def keyOk (c : Configured) : Bool :=
  match c.key with
  | [k₁, k₂, k₃] => chainAll 32 k₁ && chainAll 32 k₂ && chainAll 32 k₃
  | _ => false

/-- The test at the entry file's chain. -/
def entryOk (c : Configured) : Bool := chainAll 32 c.entry

/-- The slots of a batch: how many requests share the proof file's second chain. -/
def slots : ℕ := 64

/-- The test at the proof file's three chains, and that the public files state just `slots` slots.
False unless there are just three chains. -/
def proofOk (c : Configured) : Bool :=
  match c.proof with
  | [p₁, p₂, p₃] =>
    chainAll 20 p₁ && chainAll 28 p₂ && chainAll 20 p₃ && decide (c.sized.lines.slots = slots)
  | _ => false

/-- The public test on the seven chains' plans: the three files' tests together. -/
def madeOk (c : Configured) : Bool := keyOk c && entryOk c && proofOk c

/-- The test on the seven chains is the three files' tests together. -/
theorem madeOk_iff (c : Configured) :
    madeOk c = true ↔ keyOk c = true ∧ entryOk c = true ∧ proofOk c = true := by
  simp only [madeOk, Bool.and_eq_true, and_assoc]

/-- What `workPlaced` says. -/
theorem workPlaced_iff (P : Planned) :
    workPlaced P = true ↔
      ∀ r ∈ P.rounds, r.entry.work ≠ 0 → r.why = .query ∧ r.entry.poss ≠ 0 := by
  simp only [workPlaced, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne]
  constructor
  · intro h r hr hw
    exact (h r hr).resolve_left hw
  · intro h r hr
    by_cases hw : r.entry.work = 0
    · exact Or.inl hw
    · exact Or.inr (h r hr hw)

/-- `chainAll` is its three tests together. -/
theorem chainAll_iff (w : ℕ) (P : Planned) :
    chainAll w P = true ↔
      chainOk w P = true ∧ Number.smallOk P = true ∧ workPlaced P = true := by
  simp only [chainAll, Bool.and_eq_true, and_assoc]

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.madeOk_iff
#print axioms VerifiableInference.Desc.workPlaced_iff
#print axioms VerifiableInference.Desc.chainAll_iff
