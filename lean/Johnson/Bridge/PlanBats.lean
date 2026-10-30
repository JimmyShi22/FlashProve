-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/PlanBats.lean: the rounds «BAT» of a proof file, a key file and an entry file, in
which rows are batched in front of a fold, AS FUNCTIONS OF THE PLANS' OWN ENTRIES AND OF THE
PLANNER's RECORDS, at a rule for the radii; and one test whose yes gives, at every entry «BAT» of
the plans: the entry is the format's own; the bound on lists that the batching asks of its stage's
tables; and the count of Johnson/Bridge/BatPriced.lean is at most 2^-128 of the round's written
verifier messages. And that test with `planTestsB` as one. No numeral of a plan is written here.

This file stands above Cb/Bridge/CodeListRSProved.lean through its imports, and so above the files
under ThirdParty/: files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15). The statement on codes is not used in its own
proofs.
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

Definitions with code, and statements that follow from Johnson/Bridge/BatPriced.lean.

Main names:
  `batEntries M`: the plans' entries «BAT», in the plans' order.
  `batStagesBy ρ M`: the stages in front of whose folds rows are batched, each with its radius by
    the rule: the groups of the proof file's links as they are closed, then the first stages of the
    nine tests, in the order of `nineTests` (Johnson/Bridge/PlanTests.lean).
  `planBats ρ M`: each entry with the place of its number: the stage, its radius, the entry's rows.
  `planBatsB ρ M`: THE TEST: as many entries as stages; each entry is `(Fmt.M2.rBatN rows).entry`;
    `BatPlace.good` and `BatPlace.priced` at each place.
  `planBatsB_all`, `planBatsB_entry`, `planBatsB_lists`, `planBatsB_below`: what its yes gives.
  `planBatsAllB ρ M`: `planTestsB` (Johnson/Bridge/PlanTests.lean) and `planBatsB`, at one rule.
    `planBatsAllB_parts`.

Limits: THE RADII ARE WHATEVER THE RULE SAYS: no statement here ties a rule to a protocol. THE TEST
ALONE PINS NO RADIUS: from above it asks a radius below the Johnson radius and no more, and a
smaller radius makes the list smaller; what holds a stage's radius is `planTestsB` at the same rule
(Johnson/Bridge/PlanTests.lean). WHICH ENTRY BELONGS TO WHICH STAGE IS BY ORDER ALONE: that the
plans lay the links' closings first and then the nine tests in that order is by reading of the
planner's lists (OnBytes/Plan/ReqFrames.lean, `FrameN.rounds`; OnBytes/Params/PlanListsProx.lean,
`ioppList`). The rows are the entry's: they are held against no record; at fewer than two rows the
count is 0. THE TEST SAYS YES WHERE THERE IS NO ENTRY AND NO STAGE, and a test without a stage falls
out of `batStagesBy` in silence: `wholeB` (in `planTestsB`) is what asks a stage of each of the
nine: `planBatsAllB` takes `planTestsB` with it. An exchange of two plans was not noticed by the
test at the stored sets. THAT THE COUNT IS A BLOCK's IS NOT SAID HERE (the head of
Johnson/Bridge/BatPriced.lean says where it is read). That the records and plans are those of a
file's public files is asked where they are made. That the rounds of a plan are rounds of the
description of the protocol that a verifier runs is not said here. The test has been EVALUATED at
stored sets of public files by a sheet that is not in this repository; no theorem says that it says
yes at any plan. No sum over rounds. Nothing on a verifier or a file.

-/
import Johnson.Bridge.PlanTests
import Johnson.Bridge.BatPriced

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Bridge
open OnBytes OnBytes.Params OnBytes.Slice Cb _root_.Run
open scoped ENNReal

/-- The plans' entries «BAT», in the plans' order. -/
def batEntries (M : Configured) : List Fmt.Entry :=
  (M.proof ++ M.key ++ [M.entry]).flatMap fun P => P.plan.entries.filter fun e => e.name == "BAT"

/-- The stages in front of whose folds rows are batched, each with its radius by the rule. -/
def batStagesBy (ρ : Rad) (M : Configured) : List (Sg × ℕ) :=
  linkFoldsBy ρ M.sized.proof ++ (nineTests M.sized).flatMap fun x => (stagesBy ρ x.1 x.2).take 1

/-- **Every entry «BAT»**, with the place of its number. -/
def planBats (ρ : Rad) (M : Configured) : List (Fmt.Entry × BatPlace) :=
  (batEntries M).zipWith (fun e p => (e, ⟨p.1, p.2, e.rows⟩)) (batStagesBy ρ M)

/-- **The test on the plans' entries and the planner's records.** -/
def planBatsB (ρ : Rad) (M : Configured) : Bool :=
  Nat.beq (batEntries M).length (batStagesBy ρ M).length &&
    ((planBats ρ M).all fun p =>
      decide (p.1 = (Fmt.M2.rBatN p.1.rows).entry) && p.2.good && p.2.priced)

/-- A yes of the test: no entry «BAT» is left over. -/
theorem planBatsB_all {ρ : Rad} {M : Configured} (h : planBatsB ρ M = true) :
    (batEntries M).length = (batStagesBy ρ M).length :=
  Nat.eq_of_beq_eq_true (Bool.and_eq_true_iff.1 h).1

theorem planBatsB_at {ρ : Rad} {M : Configured} (h : planBatsB ρ M = true) :
    ∀ p ∈ planBats ρ M,
      p.1 = (Fmt.M2.rBatN p.1.rows).entry ∧ p.2.good = true ∧ p.2.priced = true := fun p hp => by
  have := List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).2 p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- **A yes of the test: every entry «BAT» is the format's own.** -/
theorem planBatsB_entry {ρ : Rad} {M : Configured} (h : planBatsB ρ M = true) :
    ∀ p ∈ planBats ρ M, p.1 = (Fmt.M2.rBatN p.1.rows).entry := fun p hp => (planBatsB_at h p hp).1

/-- **A yes of the test: the lists of each stage's tables.** -/
theorem planBatsB_lists {ρ : Rad} {M : Configured} (h : planBatsB ρ M = true) :
    ∀ p ∈ planBats ρ M, p.2.s.cIn.ListAt p.2.e (p.2.s.lstJ p.2.e) := fun p hp =>
  BatPlace.listIn (planBatsB_at h p hp).2.1

/-- **A yes of the test: at every entry «BAT» the count is at most 2^-128 of the round's written
verifier messages.** -/
theorem planBatsB_below {ρ : Rad} {M : Configured} (h : planBatsB ρ M = true) :
    ∀ p ∈ planBats ρ M, ∀ d : PQ.RD, IsRd d (Fmt.M2.rBatN p.2.rows) →
      RoundBelow p.2.cnt d ((2 : ℝ≥0∞)⁻¹ ^ 128) := fun p hp _ hd =>
  BatPlace.below (planBatsB_at h p hp).2.2 hd

/-- **The test with `planTestsB` as one**, at one rule. -/
def planBatsAllB (ρ : Rad) (M : Configured) : Bool := planTestsB ρ M && planBatsB ρ M

theorem planBatsAllB_parts {ρ : Rad} {M : Configured} (h : planBatsAllB ρ M = true) :
    planTestsB ρ M = true ∧ planBatsB ρ M = true := Bool.and_eq_true_iff.1 h

end Johnson.Bridge

#print axioms Johnson.Bridge.planBatsB_all
#print axioms Johnson.Bridge.planBatsB_at
#print axioms Johnson.Bridge.planBatsB_entry
#print axioms Johnson.Bridge.planBatsB_lists
#print axioms Johnson.Bridge.planBatsB_below
#print axioms Johnson.Bridge.planBatsAllB_parts
