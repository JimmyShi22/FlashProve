-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean: the proof file's part of the row number_prices
with the plan as data, as a closed statement. Every round of the data of the proof file's three
written lists of the full size (`writtenPFull`, Johnson/Flat/Dec/FitAtWritten.lean) has, at its
place, a round of three written priced plans with `PricedAt`
(Johnson/Desc/Ok/NumberPrices/AtData.lean), and the three plans pass the public test on a chain's
plan (`Desc.chainAll`, Johnson/Desc/MadeOk.lean) at the bounds on work 20, 28, 20.

Whose data the written priced plans are. They stand in Johnson/Desc/ProofFile/Written/Priced.lean,
which a program wrote from a print of the library's own planner at the stored full-size public
files. A second copy, laid by another program from another print, held the same setting, the
same records in the same order and the same runs: by a program outside Lean, round by round, all
seven fields, and once by Lean's kernel. A program outside Lean also held them, round by round,
against a table that a twin of the C++ verifier printed, the errors to six decimals of a bit. These
three holdings were made beside the library: no file of the library records them, and no build
repeats them.

`ProofPricesWritten` is a closed fact on two written files: it names no letter, no public file, no
planner and no description of the protocol. It becomes the row's clause for the proof file where a
description's data are shown to be `writtenPFull`.

Definitions.
  `proofThree`: the three written priced plans, as `Three` (AtWritten.lean).
  `ProofPricesAt T`: `ProofPricedAt T`, and `Desc.chainAll` = true at the three plans, at 20, 28,
    20. The two belong together: `PricedAt` says that error / 2 ^ work is within 2 ^ -128; how much
    work a round may count, and at which rounds, is in `Desc.chainAll`.
  `ProofPricesWritten`: `ProofPricesAt proofThree`.
Statements.
  `proof_recs0`, `1`, `2`: `Desc.chainAll` says yes at each chain's 105, 48, 21 records, taken as a
    plan of their own.
  `proof_walk0`, `1`, `2`: one walk along both lists of runs finds the same entry at every place.
  `proof_lit_ok`: so `proofLitOk 40000 proofThree` = true. `proofPricedFull`, `proofAll_full`: the
    two halves. `proofPricesWritten : ProofPricesWritten`.
  `writtenP_lengths`, `pricedP_lengths`: the three lists of `writtenPFull` have 48292, 68 and 30
    rounds, and so have the three lists of priced rounds against which they are held: 48390 rounds.
    The plans have 48391: the first chain's last round is tested by `Desc.chainAll` and has no
    `PricedAt`.
  `proof_set`: the written setting is `recordSet` (OnBytes/Params/EntryStagesRecord.lean).
By evaluations in Lean's kernel (`decide +kernel`): `proof_recs0` to `proof_walk2`, `proof_set`. All
else is by proof.

What holds an error here: from above the test; from below nobody yet. See the head of
AtWritten.lean.

What of OnBytes/Model/ is used: nothing by name.

Limits. That the written priced plans are the planner's at any public files is no theorem. `why`,
`group`, `rests`, `scope` and `wordFault` are the written records' own words, held against nothing
in Lean. That the written lists are what the planner makes of the public files, and that a
description's data are `writtenPFull`, is not said here. No count is bounded. One round draws an
element at the error 0: a round "BAT-sigma" of the first plan that batches one row; the planner's
text gives (rows - 1) / |E| there. The factor for the requests of a batch stands inside the written
error of the second plan's round "LIN point", 64 at the written lines, and the setting's own factor,
its number of instances, is 1
(Johnson/Desc/Ok/NumberPrices/ProofLinPoint.lean); whether the other
rounds of the shared chain need a factor is a matter of the protocol's analysis, and none is laid
here (`PricedAt.held_times`, AtData.lean). Nothing on the small example. The limits of
AtWritten.lean and of AtData.lean hold here. Nothing on soundness.
-/
import Johnson.Desc.ProofFile.Written.Priced
import Johnson.Desc.Ok.NumberPrices.AtWritten
import OnBytes.Params.EntryStagesRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.ByRuns
open VerifiableInference VerifiableInference.Number
open OnBytes OnBytes.Params OnBytes.Flat OnBytes.Flat.Held OnBytes.Maker
open Johnson.G Johnson.G.Runs

/-- The proof file's three written priced plans. -/
def proofThree : Three :=
  ⟨⟨pricedProofSetFull, pricedProofRecsFull0, pricedProofRunsFull0⟩,
    ⟨pricedProofSetFull, pricedProofRecsFull1, pricedProofRunsFull1⟩,
    ⟨pricedProofSetFull, pricedProofRecsFull2, pricedProofRunsFull2⟩⟩

/-! ## The test at the records -/

theorem proof_recs0 : Desc.chainAll 20 ⟨pricedProofSetFull, pricedProofRecsFull0⟩ = true := by
  decide +kernel

theorem proof_recs1 : Desc.chainAll 28 ⟨pricedProofSetFull, pricedProofRecsFull1⟩ = true := by
  decide +kernel

theorem proof_recs2 : Desc.chainAll 20 ⟨pricedProofSetFull, pricedProofRecsFull2⟩ = true := by
  decide +kernel

/-! ## The walk along both lists of runs -/

set_option maxRecDepth 1000000 in
theorem proof_walk0 :
    sameBy (fun x r => decide (x.1.entry = r.entry)) 40000
      (valRuns dryProofRecsFull dryProofRunsFull0)
      (chainRuns pricedProofRecsFull0 pricedProofRunsFull0) = true := by
  decide +kernel

theorem proof_walk1 :
    sameBy (fun x r => decide (x.1.entry = r.entry)) 40000
      (valRuns dryProofRecsFull dryProofRunsFull1)
      (chainRuns pricedProofRecsFull1 pricedProofRunsFull1) = true := by
  decide +kernel

theorem proof_walk2 :
    sameBy (fun x r => decide (x.1.entry = r.entry)) 40000
      (valRuns dryProofRecsFull dryProofRunsFull2)
      (chainRuns pricedProofRecsFull2 pricedProofRunsFull2) = true := by
  decide +kernel

/-! ## The closed fact -/

/-- **The test says yes at the proof file's three written priced plans.** -/
theorem proof_lit_ok : proofLitOk 40000 proofThree = true :=
  Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2
    ⟨Bool.and_eq_true_iff.2 ⟨proof_recs0, proof_walk0⟩,
      Bool.and_eq_true_iff.2 ⟨proof_recs1, proof_walk1⟩⟩,
    Bool.and_eq_true_iff.2 ⟨proof_recs2, proof_walk2⟩⟩

/-- Every round of the proof file's data at the written lists has a round of the written priced
plans at its place with `PricedAt`. -/
theorem proofPricedFull : ProofPricedAt proofThree :=
  (pricedOfThree 40000 proofThree).2 proof_lit_ok

/-- The public test on a chain's plan says yes at each of the three whole plans. -/
theorem proofAll_full : Desc.chainAll 20 proofThree.A.plan = true ∧
    Desc.chainAll 28 proofThree.B.plan = true ∧ Desc.chainAll 20 proofThree.C.plan = true :=
  ⟨chainAll_of_runs _ proof_recs0, chainAll_of_runs _ proof_recs1, chainAll_of_runs _ proof_recs2⟩

/-- The prices of the proof file's rounds, at three written priced plans: each round of the written
data has a priced round at its place, and the three plans pass the public test on a chain's plan. -/
def ProofPricesAt (T : Three) : Prop :=
  ProofPricedAt T ∧ Desc.chainAll 20 T.A.plan = true ∧ Desc.chainAll 28 T.B.plan = true ∧
    Desc.chainAll 20 T.C.plan = true

/-- The closed statement. -/
def ProofPricesWritten : Prop := ProofPricesAt proofThree

/-- **It holds.** -/
theorem proofPricesWritten : ProofPricesWritten := ⟨proofPricedFull, proofAll_full⟩

/-! ## It is not idle for want of rounds -/

/-- The three lists of the proof file's data at the written lists. -/
theorem writtenP_lengths :
    writtenPFull.ds₁.length = 48292 ∧ writtenPFull.ds₂.length = 68 ∧
      writtenPFull.ds₃.length = 30 := by
  have l := dryProofFull_length
  have l1 : dryProofFull.1.length = 48293 := congrArg (fun x : ℕ × ℕ × ℕ => x.1) l
  have l2 : dryProofFull.2.1.length = 68 := congrArg (fun x : ℕ × ℕ × ℕ => x.2.1) l
  have l3 : dryProofFull.2.2.length = 30 := congrArg (fun x : ℕ × ℕ × ℕ => x.2.2) l
  have e1 : writtenPFull.ds₁.length = dryProofFull.1.length - 1 := by
    have h := congrArg List.length
      (Flat.of_entry₁ 32 dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2)
    simpa only [List.length_map, List.length_dropLast] using h
  have e2 : writtenPFull.ds₂.length = dryProofFull.2.1.length := by
    have h := congrArg List.length
      (Flat.of_entry₂ 32 dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2)
    simpa only [List.length_map] using h
  have e3 : writtenPFull.ds₃.length = dryProofFull.2.2.length := by
    have h := congrArg List.length
      (Flat.of_entry₃ 32 dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2)
    simpa only [List.length_map] using h
  exact ⟨by omega, by omega, by omega⟩

/-- The lists of priced rounds against which they are held have as many. -/
theorem pricedP_lengths :
    (chainRounds proofThree.A.plan).dropLast.length = 48292 ∧
      (chainRounds proofThree.B.plan).length = 68 ∧
      (chainRounds proofThree.C.plan).length = 30 := by
  obtain ⟨h1, h2, h3⟩ := proofPricedFull
  obtain ⟨l1, l2, l3⟩ := writtenP_lengths
  exact ⟨h1.length_eq.symm.trans l1, h2.length_eq.symm.trans l2, h3.length_eq.symm.trans l3⟩

/-- The written setting is the setting of the written lines. -/
theorem proof_set : pricedProofSetFull = recordSet := by decide +kernel

end VerifiableInference.Number.ByRuns

#print axioms VerifiableInference.Number.ByRuns.proof_recs0
#print axioms VerifiableInference.Number.ByRuns.proof_recs1
#print axioms VerifiableInference.Number.ByRuns.proof_recs2
#print axioms VerifiableInference.Number.ByRuns.proof_walk0
#print axioms VerifiableInference.Number.ByRuns.proof_walk1
#print axioms VerifiableInference.Number.ByRuns.proof_walk2
#print axioms VerifiableInference.Number.ByRuns.proof_lit_ok
#print axioms VerifiableInference.Number.ByRuns.proofPricedFull
#print axioms VerifiableInference.Number.ByRuns.proofAll_full
#print axioms VerifiableInference.Number.ByRuns.proofPricesWritten
#print axioms VerifiableInference.Number.ByRuns.writtenP_lengths
#print axioms VerifiableInference.Number.ByRuns.pricedP_lengths
#print axioms VerifiableInference.Number.ByRuns.proof_set
