-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/KeyPlansWritten.lean: a law in the goals' scope, and four negative tests of the
comparison on which it rests.

The law. At every three public files in the scope of the goals (`VerifierAndGoals.InScope`, Ladder.lean),
where the library's planner returns (`Model.Verify.planned`, OnBytes/Model/Verify.lean: the
library's rendering of the C++ verifier's checking calls), the plans of the key file's second and
third chains in what it computes are the second and the third of the key file's written priced plans
(Johnson/G/PricedKeyLit.lean), field by field. They have 68 and 30 rounds, of the three plans'
18950. Of the first plan the law says that it is what `Plan.oneTimePlan keyFull` returns; that this
is the first written plan is `first_written` (Johnson/Goal/Numbers/KeyFirstListed.lean). The three
together: where `configure` returns at the written lines, under one premise on the sizing,
`keyPlans_of_configure` (Johnson/Goal/Numbers/KeyPlansOfConfigure.lean); in scope, at the public
part that the proof file's description computes, `keyPlans_at_pure`
(Johnson/Goal/Numbers/KeyPlansAtPure.lean).

The negative tests. The law rests on two closed equations (`shared_written`, `second_written`,
Johnson/Goal/Numbers/KeyLaterListed.lean), and these on two answers yes of the comparison `rideAt`
(Johnson/Desc/Ok/NumberPrices/ByRuns.lean). Here the same comparison, at the same two calls of the
planner's routines, says no at four written plans that are changed in one place each. So the two
answers yes could have failed. (A written plan is stored as its distinct rounds, `Lit.recs`,
Johnson/G/RunsDefs.lean, and runs over them. In this file "record" means one such distinct round,
after that name; it is no out-of-domain sample.)

`KeyLaterPlansWritten` is a name for the law's statement, which is proved right below it
(`keyLaterPlansWritten`): nothing is left open under that name, and it is not one of the statements
that lean/STATEMENTS.html lists. It speaks of the goals' scope and of that planner, and says where
the written numbers come from. It says nothing on whether a price is right (on prices: the head of
Johnson/Desc/Ok/NumberPrices/Stated.lean).

How. By `plans_at_scope` (Johnson/Goal/PlanValues/KeyPlansAtScope.lean), in scope the three plans
are what `Plan.oneTimePlan keyFull`, `sharedPlan keyFull.set keyFull.codes keyFull.once` and
`secondPlan keyFull.set keyFull.once` return: three calls at closed arguments. The two closed
equations say what the second and the third call return.

The heads of Johnson/Desc/Ok/NumberPrices/ByRuns.lean and
Johnson/Desc/Ok/NumberPrices/KeyAtWritten.lean say of a written plan's fields `why`, `group`,
`rests`, `scope`, `wordFault` that they are the written record's own words, held against nothing;
the first says of its errors that they are held against nothing but the bound. For the key file's
second and third plan Johnson/Goal/Numbers/KeyLaterListed.lean holds fields and errors against the
planner's routines.

Definitions.
  `KeyLaterPlansWritten`: the law's statement, closed.
  `mapAt i f recs`: the records with f at the record i.
Statements.
  `keyLaterPlansWritten : KeyLaterPlansWritten`.
  `keyLaterPriced_in_scope`: in scope, where the planner returns, its second and third plan pass
    `Desc.chainAll 32`, and every round of the second and third list of `writtenKFull` has
    `PricedAt` with the round at its place.
  Where `rideAt` says no: `ride_shared_bent`: against the second written plan with one error doubled
    (`bentKey`, Johnson/Desc/Ok/NumberPrices/KeyAtWrittenTeeth.lean); `ride_second_why`,
    `ride_second_group`, `ride_second_target`: against the third written plan with one record's
    `why` changed, with one record's `group` struck, with the setting's target raised by 1.
By evaluations in Lean's kernel (`decide +kernel`): the four that say no.

What of OnBytes/Model/ is used: `Model.Verify.planned` and `Model.Verify.Planned`, as in
`plans_at_scope`.

Limits. Four changes, one at a time: of a round's seven fields three are changed (the error, `why`,
`group`), each at one record, and of the setting one field. The statements in scope go one way: from
a planner that returns; where it refuses they say nothing. That it returns is shown by no theorem in
this file, and none is known in the files that it imports. In other files the two premises of the
statements in scope are met at the library's written copy of the full-size public files
(`VerifierAndGoals.storedPublicFiles`: three terms written in Lean; no theorem ties them to the shipped files): that the
files are in scope by `VerifierAndGoals.inScope_full` (Johnson/Goal/Files/ScopeExample.lean); that the planner
returns by `AtFullSide.Planner.planned_zFull_returns` (AtFullSide/Planner/MadeReturns.lean), at the
format's second hash function (`OnBytes.secondHashFunction`) and the files' own digest, in a side library
outside the main library (one constant beneath it passes Lean's kernel only at a larger thread
stack; Lean's re-checker, leanchecker, was run on it and fails there at each shell stack limit that
was tried; the toolchain's own replay passes it at a larger thread stack; so that constant has been
checked by the kernel in the build and by that replay, and by no independent program); no
independent checker has replayed any of the closed facts beneath it, and the full-size example's
weights are synthetic. These two theorems speak of `VerifierAndGoals.storedPublicFiles` alone, not of other files in
scope. `planned`
forms the digest of the public files by the format's hash, by name: so the statements speak of the
plan at that digest, and can stand in no description that takes the hash as a random oracle; the
like for every digest, from the sizes, is in Johnson/Goal/Written/MadeOfSized.lean. Nothing says
that an error bounds a count. Nothing on the proof file's or the entry file's plans.
Nothing on soundness.
-/
import Johnson.Goal.PlanValues.KeyPlansAtScope
import Johnson.Goal.Numbers.KeyLaterListed
import Johnson.Desc.Ok.NumberPrices.KeyAtWrittenTeeth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.ByRuns
open VerifiableInference VerifiableInference.Number
open OnBytes OnBytes.Params OnBytes.Flat.Held OnBytes.Model OnBytes.Model.Verify
open Lk6.AtPlan Johnson.G

/-! ## In scope, where the planner returns -/

/-- In scope, where the planner returns, the plans of the key file's second and third chains are the
written ones. -/
def KeyLaterPlansWritten : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles), VerifierAndGoals.InScope Z = true → ∀ p : Verify.Planned,
    planned Z.pol Z.KL (some Z.lay) = .ok p →
      ∃ P1, p.chains.made.key = [P1, keyThree.B.plan, keyThree.C.plan] ∧
        Plan.oneTimePlan keyFull = .ok P1

/-- **It holds.** -/
theorem keyLaterPlansWritten : KeyLaterPlansWritten := by
  intro Z hZ p hp
  obtain ⟨P1, P2, P3, e, a1, a2, a3⟩ := plans_at_scope hZ hp
  have b2 : P2 = keyThree.B.plan := Except.ok.inj (a2.symm.trans shared_written)
  have b3 : P3 = keyThree.C.plan := Except.ok.inj (a3.symm.trans second_written)
  exact ⟨P1, by rw [e, b2, b3], a1⟩

/-- In scope, where the planner returns: its second and third plan pass the public
test on a chain's plan, and every round of the second and third written list has a priced round of
them at its place. -/
theorem keyLaterPriced_in_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Verify.Planned} (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) :
    ∃ K₁ K₂ K₃, p.chains.made.key = [K₁, K₂, K₃] ∧ Desc.chainAll 32 K₂ = true ∧
      Desc.chainAll 32 K₃ = true ∧
      List.Forall₂ Number.PricedAt writtenKFull.ds₂ (chainRounds K₂) ∧
      List.Forall₂ Number.PricedAt writtenKFull.ds₃ (chainRounds K₃) := by
  obtain ⟨P1, e, _⟩ := keyLaterPlansWritten Z hZ p hp
  exact ⟨P1, _, _, e, keyAll_full.2.1, keyAll_full.2.2, keyPricedFull.2.1, keyPricedFull.2.2⟩

/-! ## Where the comparison says no -/

set_option maxRecDepth 1000000 in
/-- Against the second written plan with one error doubled the comparison says no. -/
theorem ride_shared_bent :
    rideAt 200 (sharedPlan keyFull.set keyFull.codes keyFull.once) bentKey.B = false := by
  decide +kernel

/-- The records with f at the record i. -/
def mapAt : ℕ → (PlanRound → PlanRound) → List PlanRound → List PlanRound
  | _, _, [] => []
  | 0, f, r :: rs => f r :: rs
  | i + 1, f, r :: rs => r :: mapAt i f rs

set_option maxRecDepth 1000000 in
/-- Against the third written plan with one record's `why` changed it says no. -/
theorem ride_second_why :
    rideAt 200 (secondPlan keyFull.set keyFull.once)
      ⟨pricedKeySetFull, mapAt 0 (fun r => { r with why := .sample }) pricedKeyRecsFull2,
        pricedKeyRunsFull2⟩ = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- With one record's `group` struck it says no. -/
theorem ride_second_group :
    rideAt 200 (secondPlan keyFull.set keyFull.once)
      ⟨pricedKeySetFull, mapAt 1 (fun r => { r with group := none }) pricedKeyRecsFull2,
        pricedKeyRunsFull2⟩ = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- With the setting's target raised by 1 it says no. -/
theorem ride_second_target :
    rideAt 200 (secondPlan keyFull.set keyFull.once)
      ⟨{ pricedKeySetFull with target := pricedKeySetFull.target + 1 }, pricedKeyRecsFull2,
        pricedKeyRunsFull2⟩ = false := by
  decide +kernel

end VerifiableInference.Number.ByRuns

#print axioms VerifiableInference.Number.ByRuns.keyLaterPlansWritten
#print axioms VerifiableInference.Number.ByRuns.keyLaterPriced_in_scope
#print axioms VerifiableInference.Number.ByRuns.ride_shared_bent
#print axioms VerifiableInference.Number.ByRuns.ride_second_why
#print axioms VerifiableInference.Number.ByRuns.ride_second_group
#print axioms VerifiableInference.Number.ByRuns.ride_second_target
