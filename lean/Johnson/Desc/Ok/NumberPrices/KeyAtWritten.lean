-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/NumberPrices/KeyAtWritten.lean: the key file's part of the row number_prices with
the plan as data, as a closed statement. Every round of the data of the key file's three written
lists of the full size (`writtenKFull`, Johnson/Flat/Dec/FitAtWritten.lean) has, at its place, a
round of the key file's three written priced plans (Johnson/G/PricedKeyLit.lean) with `PricedAt`
(Johnson/Desc/Ok/NumberPrices/AtData.lean), and the three plans pass the public test on a chain's
plan (`Desc.chainAll 32`, Johnson/Desc/MadeOk.lean).

`KeyPricesWritten` is a closed fact on two written files: it names no letter, no public file, no
planner and no description of the protocol. It becomes the row's clause for the key file where a
description's data are shown to be `writtenKFull`. All else here are facts on the two written files.

Definitions.
  `keyThree`: the three written priced plans, as `Three` (AtWritten.lean).
  `KeyPricesWritten`: `KeyPricedAt keyThree`, and `Desc.chainAll 32` = true at each of the three
    plans. The two belong together: `PricedAt` says that error / 2 ^ work is within 2 ^ -128; that
    no round counts more than 32 bits of work, and that work is counted at rounds that draw
    positions alone, is in `Desc.chainAll`.
Statements.
  `key_recs0`, `1`, `2`: `Desc.chainAll 32` says yes at each chain's 37, 48, 21 records, taken as a
    plan of their own: each price, work counted, is within 2 ^ -128; the side conditions; the target
    is 128; no round has more than 32 bits of work; the tests on words and on pairs; the test on
    rounds that draw matrix entries; work is counted at rounds on positions alone.
  `key_walk0`, `1`, `2`: one walk along both lists of runs finds the same entry at every place; the
    entry under the name "RECORD" at the head of the first plan is passed over.
  `key_lit_ok`: so `keyLitOk 10000 keyThree` = true. `keyPricedFull`, `keyAll_full`: the two halves.
  `keyPricesWritten : KeyPricesWritten`.
  `written_lengths`, `priced_lengths`: the three lists of `writtenKFull` have 18850, 68 and 30
    rounds, and so have the three lists of priced rounds against which they are held: `KeyPricedAt
    keyThree` speaks of 18948 rounds. The plans have 18950: the entry "RECORD" and the first chain's
    last round are tested by `Desc.chainAll` and have no `PricedAt`.
  `key_set`: the written setting is `recordSet` (OnBytes/Params/EntryStagesRecord.lean).
  `key_locs`, `key_bases`: the second plan's entries under the names "LOC" (one) and "BASE" (two),
    by `filter_of_lit` (ByRuns.lean).
By evaluations in Lean's kernel (`decide +kernel`): `key_recs0` to `key_walk2`, `key_set`, and
inside `key_locs`, `key_bases`. All else is by proof.

What holds an error here: from above the test; from below nobody yet. See the head of
AtWritten.lean.

What of OnBytes/Model/ is used: nothing by name.

Limits. That the written priced plans are the planner's at any public files is no theorem here: a
run by evaluation held them so, field by field (the head of Johnson/G/PricedKeyLit.lean). `why`,
`group`, `rests`, `scope` and `wordFault` are the written records' own words, held against nothing
in Lean: of "work is counted at rounds on positions alone" the half "draws a position" reads the
entry, which the walk ties to the written list; the half on `why` is the record's word. That one
stage is priced at one distance is read off `group`. That the written lists are what the planner
makes of the public files, and that a description's data are `writtenKFull`, is not said here. No
count is bounded. Nothing on the proof file's or the entry file's plans; nothing on the small
example. The limits of AtWritten.lean and of AtData.lean hold here. Nothing on soundness.

-/
import Johnson.G.PricedKeyLit
import Johnson.Desc.Ok.NumberPrices.AtWritten
import OnBytes.Params.EntryStagesRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.ByRuns
open VerifiableInference VerifiableInference.Number
open OnBytes OnBytes.Params OnBytes.Flat OnBytes.Flat.Held OnBytes.Maker
open Johnson.G Johnson.G.Runs

/-- The key file's three written priced plans. -/
def keyThree : Three :=
  ⟨⟨pricedKeySetFull, pricedKeyRecsFull0, pricedKeyRunsFull0⟩,
    ⟨pricedKeySetFull, pricedKeyRecsFull1, pricedKeyRunsFull1⟩,
    ⟨pricedKeySetFull, pricedKeyRecsFull2, pricedKeyRunsFull2⟩⟩

/-! ## The test at the records -/

theorem key_recs0 : Desc.chainAll 32 ⟨pricedKeySetFull, pricedKeyRecsFull0⟩ = true := by
  decide +kernel

theorem key_recs1 : Desc.chainAll 32 ⟨pricedKeySetFull, pricedKeyRecsFull1⟩ = true := by
  decide +kernel

theorem key_recs2 : Desc.chainAll 32 ⟨pricedKeySetFull, pricedKeyRecsFull2⟩ = true := by
  decide +kernel

/-! ## The walk along both lists of runs -/

set_option maxRecDepth 1000000 in
theorem key_walk0 :
    sameBy (fun x r => decide (x.1.entry = r.entry)) 10000 (valRuns dryKeyRecsFull dryKeyRunsFull0)
      (chainRuns pricedKeyRecsFull0 pricedKeyRunsFull0) = true := by
  decide +kernel

theorem key_walk1 :
    sameBy (fun x r => decide (x.1.entry = r.entry)) 10000 (valRuns dryKeyRecsFull dryKeyRunsFull1)
      (chainRuns pricedKeyRecsFull1 pricedKeyRunsFull1) = true := by
  decide +kernel

theorem key_walk2 :
    sameBy (fun x r => decide (x.1.entry = r.entry)) 10000 (valRuns dryKeyRecsFull dryKeyRunsFull2)
      (chainRuns pricedKeyRecsFull2 pricedKeyRunsFull2) = true := by
  decide +kernel

/-! ## The closed fact -/

/-- **The test says yes at the key file's three written priced plans.** -/
theorem key_lit_ok : keyLitOk 10000 keyThree = true :=
  Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2
    ⟨Bool.and_eq_true_iff.2 ⟨key_recs0, key_walk0⟩, Bool.and_eq_true_iff.2 ⟨key_recs1, key_walk1⟩⟩,
    Bool.and_eq_true_iff.2 ⟨key_recs2, key_walk2⟩⟩

/-- Every round of the key file's data at the written lists has a round of the written priced plans
at its place with `PricedAt`. -/
theorem keyPricedFull : KeyPricedAt keyThree := (pricedOfThree 10000 keyThree).1 key_lit_ok

/-- The public test on a chain's plan says yes at each of the three whole plans. -/
theorem keyAll_full : Desc.chainAll 32 keyThree.A.plan = true ∧
    Desc.chainAll 32 keyThree.B.plan = true ∧ Desc.chainAll 32 keyThree.C.plan = true :=
  ⟨chainAll_of_runs _ key_recs0, chainAll_of_runs _ key_recs1, chainAll_of_runs _ key_recs2⟩

/-- The prices of the key file's rounds, at written data: each round of the data has a priced round
at its place, and the three priced plans pass the public test on a chain's plan. -/
def KeyPricesWritten : Prop :=
  KeyPricedAt keyThree ∧ Desc.chainAll 32 keyThree.A.plan = true ∧
    Desc.chainAll 32 keyThree.B.plan = true ∧ Desc.chainAll 32 keyThree.C.plan = true

/-- **It holds.** -/
theorem keyPricesWritten : KeyPricesWritten := ⟨keyPricedFull, keyAll_full⟩

/-! ## It is not idle for want of rounds -/

/-- The three lists of the key file's data at the written lists. -/
theorem written_lengths :
    writtenKFull.ds₁.length = 18850 ∧ writtenKFull.ds₂.length = 68 ∧
      writtenKFull.ds₃.length = 30 := by
  have l := dryKeyFull_length
  have l1 : dryKeyFull.1.length = 18851 := congrArg (fun x : ℕ × ℕ × ℕ => x.1) l
  have l2 : dryKeyFull.2.1.length = 68 := congrArg (fun x : ℕ × ℕ × ℕ => x.2.1) l
  have l3 : dryKeyFull.2.2.length = 30 := congrArg (fun x : ℕ × ℕ × ℕ => x.2.2) l
  have e1 : writtenKFull.ds₁.length = dryKeyFull.1.length - 1 := by
    have h := congrArg List.length (Flat.of_entry₁ 32 dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2)
    simpa only [List.length_map, List.length_dropLast] using h
  have e2 : writtenKFull.ds₂.length = dryKeyFull.2.1.length := by
    have h := congrArg List.length (Flat.of_entry₂ 32 dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2)
    simpa only [List.length_map] using h
  have e3 : writtenKFull.ds₃.length = dryKeyFull.2.2.length := by
    have h := congrArg List.length (Flat.of_entry₃ 32 dryKeyFull.1 dryKeyFull.2.1 dryKeyFull.2.2)
    simpa only [List.length_map] using h
  exact ⟨by omega, by omega, by omega⟩

/-- The lists of priced rounds against which they are held have as many. -/
theorem priced_lengths :
    (chainRounds keyThree.A.plan).dropLast.length = 18850 ∧
      (chainRounds keyThree.B.plan).length = 68 ∧ (chainRounds keyThree.C.plan).length = 30 := by
  obtain ⟨h1, h2, h3⟩ := keyPricedFull
  obtain ⟨l1, l2, l3⟩ := written_lengths
  exact ⟨h1.length_eq.symm.trans l1, h2.length_eq.symm.trans l2, h3.length_eq.symm.trans l3⟩

/-! ## Beside -/

/-- The written setting is the setting of the written lines. -/
theorem key_set : pricedKeySetFull = recordSet := by decide +kernel

/-- The key file's second written priced plan has one entry under the name "LOC". -/
theorem key_locs : keyThree.B.plan.plan.entries.filter (fun e => e.name == "LOC") =
    [⟨"LOC", 1, 32, 0, 0, 0, 0, 0, 62, 32, 0, 0⟩] := by
  rw [filter_of_lit]
  decide +kernel

/-- It has two under the name "BASE". -/
theorem key_bases : keyThree.B.plan.plan.entries.filter (fun e => e.name == "BASE") =
    [⟨"BASE", 1, 32, 39216, 0, 0, 0, 0, 49, 14, 0, 0⟩,
      ⟨"BASE", 1, 32, 38736, 0, 0, 0, 0, 39, 15, 0, 0⟩] := by
  rw [filter_of_lit]
  decide +kernel

end VerifiableInference.Number.ByRuns

#print axioms VerifiableInference.Number.ByRuns.key_recs0
#print axioms VerifiableInference.Number.ByRuns.key_recs1
#print axioms VerifiableInference.Number.ByRuns.key_recs2
#print axioms VerifiableInference.Number.ByRuns.key_walk0
#print axioms VerifiableInference.Number.ByRuns.key_walk1
#print axioms VerifiableInference.Number.ByRuns.key_walk2
#print axioms VerifiableInference.Number.ByRuns.key_lit_ok
#print axioms VerifiableInference.Number.ByRuns.keyPricedFull
#print axioms VerifiableInference.Number.ByRuns.keyAll_full
#print axioms VerifiableInference.Number.ByRuns.keyPricesWritten
#print axioms VerifiableInference.Number.ByRuns.written_lengths
#print axioms VerifiableInference.Number.ByRuns.priced_lengths
#print axioms VerifiableInference.Number.ByRuns.key_set
#print axioms VerifiableInference.Number.ByRuns.key_locs
#print axioms VerifiableInference.Number.ByRuns.key_bases
