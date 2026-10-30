-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/NumberPrices/EntryAtWrittenTeeth.lean: where the closed fact on the entry file's
prices (`EntryPricesWritten`, Johnson/Desc/Ok/NumberPrices/EntryAtWritten.lean) and its test bite,
and where they do not.

`not_pricedRD_of_above` and `not_entryPriced_of_above` are tools. All else are facts on
a written value that is bent here.

Definitions. The turns of an error (`scaleAt`, `twice`, `finer`, `halved`, `struck`) are those of
Johnson/Desc/Ok/NumberPrices/KeyAtWrittenTeeth.lean.
  `finer512`: an error times 513 / 512, exact.
  `entryWith f`: the written priced plan with the error of the round 34 turned by f: a round "FOLD
    round" of the fourth stage, one of the four whose price stands nearest to the bound among the
    plan's 42 (0.0023 of a bit, by a program outside Lean; not shown here).
  `struckEntry`: all errors struck to 0. `shortEntry`: the last round dropped. `longEntry`: the
    first round of the chain stands twice.
Statements.
  Where the test and the statement bite. `bent_aligned`: with that error doubled the entries are
    untouched. `bent_entry_no`: the test says no. `not_entryPriced_bent`: the statement is false
    there, not only untested. `fine512_no`, `not_entryPriced_fine512`: the like with the error
    raised by one part in 512.
  `not_pricedRD_of_above`: a priced round whose error is above 2 ^ (work - 128) has `PricedRD` with
    no round's data. By `not_pricedAt_of_above`.
  Where the comparison of entries bites. `short_no`, `long_no`: with the last round dropped, and
    with one round more, the test says no. `record_not_passed`: held against all 42 entries of the
    plan, "RECORD" among them, the data's entries are not these.
  Where they do not bite. `fine1024_ok`, `fine1024_priced`: with that error raised by one part in
    1024 the test says yes and the statement holds: the price has that much room. So the finest turn
    that is caught here is coarser than at the key file. `halved_entry_ok`, `halved_entry_priced`,
    `struck_entry_ok`, `struck_entry_priced`: with that error halved, and with every error struck to
    0, the test says yes and the statement holds, and must: a smaller error passes every clause
    here. Only a law from below, on a count, can catch it, and there is none yet.
By evaluations in Lean's kernel (`decide +kernel`): `bent_aligned`, `bent_entry_no`, `fine512_no`,
`short_no`, `long_no`, `record_not_passed`, `fine1024_ok`, `halved_entry_ok`, `struck_entry_ok`, and
the premises inside `not_entryPriced_bent`, `not_entryPriced_fine512`. All else is by proof.

What of OnBytes/Model/ is used: nothing by name.

Limits. The plants stand at one round. A doubled error is caught only where the price has less than
one bit of room: by the program named above that is so at 25 of the 41 rounds of the chain. No tooth
here bends `why`, `group`, `rests`, `scope`, `wordFault`, the work or the target (for all plans:
Johnson/Desc/Ok/NumberPrices/Teeth.lean). Nothing on soundness.


-/
import Johnson.Desc.Ok.NumberPrices.EntryAtWritten
import Johnson.Desc.Ok.NumberPrices.KeyAtWrittenTeeth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.ByRuns
open VerifiableInference VerifiableInference.Number
open _root_.Run OnBytes.Params OnBytes.Slice OnBytes.Flat OnBytes.Flat.Held
open OnBytes.Maker Johnson.G

/-! ## Tools -/

/-- **An error above the bound has `PricedRD` with no round's data.** -/
theorem not_pricedRD_of_above {d : PQ.RD} {r : PlanRound}
    (hb : (2⁻¹ : ℚ) ^ 128 * 2 ^ r.entry.work < r.error.val) : ¬ PricedRD d r := by
  intro P
  refine not_pricedAt_of_above (d := liftRD d) hb ((pricedAt_iff (liftRD d) r).2 ?_)
  rw [toRD_lift]
  exact P

/-- A plan with a round of the chain above the bound: the statement is false. -/
theorem not_entryPriced_of_above {P : Planned}
    (h : (chainRounds P).any (aboveB 20) = true) : ¬ EntryPricedAt P := by
  intro H
  obtain ⟨r, hr, hb⟩ := List.any_eq_true.1 h
  obtain ⟨d, _, Q⟩ := f2_right H r hr
  exact not_pricedRD_of_above (above_of_test hb) Q

/-! ## The bent plans -/

/-- An error times 513 / 512. -/
def finer512 (b : Binary) : Binary := ⟨513 * b.m, b.e - 9⟩

/-- The written priced plan with the error of the round 34 turned by f. -/
def entryWith (f : Binary → Binary) : Planned :=
  ⟨pricedEntrySetFull, scaleAt 34 f pricedEntryRoundsFull⟩

/-- All errors struck to 0. -/
def struckEntry : Planned := ⟨pricedEntrySetFull, pricedEntryRoundsFull.map struck⟩

/-- The last round dropped. -/
def shortEntry : Planned := ⟨pricedEntrySetFull, pricedEntryRoundsFull.dropLast⟩

/-- The first round of the chain stands twice. -/
def longEntry : Planned :=
  ⟨pricedEntrySetFull, pricedEntryRoundsFull.take 2 ++ pricedEntryRoundsFull.drop 1⟩

/-! ## Where the test and the statement bite -/

/-- With one error doubled the entries are untouched. -/
theorem bent_aligned : decide (Aligned frD.ds (entryWith twice)) = true := by decide +kernel

/-- **The test says no.** -/
theorem bent_entry_no : entryLitOk (entryWith twice) = false := by decide +kernel

/-- **And the statement is false.** -/
theorem not_entryPriced_bent : ¬ EntryPricedAt (entryWith twice) :=
  not_entryPriced_of_above (by decide +kernel)

/-- **With that error raised by one part in 512 the test says no.** -/
theorem fine512_no : entryLitOk (entryWith finer512) = false := by decide +kernel

/-- **And the statement is false.** -/
theorem not_entryPriced_fine512 : ¬ EntryPricedAt (entryWith finer512) :=
  not_entryPriced_of_above (by decide +kernel)

/-! ## Where the comparison of entries bites -/

/-- With the last round dropped the test says no. -/
theorem short_no : entryLitOk shortEntry = false := by decide +kernel

/-- With one round more it says no. -/
theorem long_no : entryLitOk longEntry = false := by decide +kernel

/-- Held against all 42 entries of the plan, the data's entries are not these. -/
theorem record_not_passed :
    decide (frD.ds.map (·.entry) = pricedEntryFull.rounds.map (·.entry)) = false := by
  decide +kernel

/-! ## Where they do not bite -/

/-- With that error raised by one part in 1024 the test says yes: the price has that much room. -/
theorem fine1024_ok : entryLitOk (entryWith finer) = true := by decide +kernel

/-- And the statement holds. -/
theorem fine1024_priced : EntryPricedAt (entryWith finer) := entryPriced_of_test fine1024_ok

/-- With that error halved the test says yes. -/
theorem halved_entry_ok : entryLitOk (entryWith halved) = true := by decide +kernel

/-- **And the statement holds.** -/
theorem halved_entry_priced : EntryPricedAt (entryWith halved) :=
  entryPriced_of_test halved_entry_ok

/-- With every error struck to 0 the test says yes. -/
theorem struck_entry_ok : entryLitOk struckEntry = true := by decide +kernel

/-- **And the statement holds**: it then serves the count 0 alone. -/
theorem struck_entry_priced : EntryPricedAt struckEntry := entryPriced_of_test struck_entry_ok

end VerifiableInference.Number.ByRuns

#print axioms VerifiableInference.Number.ByRuns.not_pricedRD_of_above
#print axioms VerifiableInference.Number.ByRuns.not_entryPriced_of_above
#print axioms VerifiableInference.Number.ByRuns.bent_aligned
#print axioms VerifiableInference.Number.ByRuns.bent_entry_no
#print axioms VerifiableInference.Number.ByRuns.not_entryPriced_bent
#print axioms VerifiableInference.Number.ByRuns.fine512_no
#print axioms VerifiableInference.Number.ByRuns.not_entryPriced_fine512
#print axioms VerifiableInference.Number.ByRuns.short_no
#print axioms VerifiableInference.Number.ByRuns.long_no
#print axioms VerifiableInference.Number.ByRuns.record_not_passed
#print axioms VerifiableInference.Number.ByRuns.fine1024_ok
#print axioms VerifiableInference.Number.ByRuns.fine1024_priced
#print axioms VerifiableInference.Number.ByRuns.halved_entry_ok
#print axioms VerifiableInference.Number.ByRuns.halved_entry_priced
#print axioms VerifiableInference.Number.ByRuns.struck_entry_ok
#print axioms VerifiableInference.Number.ByRuns.struck_entry_priced
