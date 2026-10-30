-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/CondTransport.lean: the condition of the law of a proximity test (the kind
K12), and the two forms "every written round is below", carried from a place at which they are shown
to a place that agrees with it in what they read.

Why. The condition has closed members (CondMembers.lean, CondMembersFull.lean). A description makes
its places off a plan. Where such a place has the member's stages and written rounds, and radii that
agree with the member's at these stages, the member's condition is the place's; the test `pubOk`,
which alone reads the place's numbers of codes and the record's codes, stays a premise: a yes of the
block's step pays it. The two forms on the rounds read no codes at all: they are carried over
without that test.
Main names:
  `k12Condition_of_member`: the condition at p, radii `rad` and codes K, from: the condition at q, a
    function r of the stage, any codes; the same stages; the same written rounds; `rad` is r at the
    stages; `pubOk p K`.
  `written_of_fields`: the premise on the written rounds from eight equations on the places' numbers
    (`writtenOf_reads`, WrittenReads.lean): rows, bits of work, stages, whether the first fold sends
    its own mask, the first free own number, the first tree's number; and of the trees of the test's
    group whether there are any, and the numbers of the chain's own among them.
  `batPlaceB_of_member`: the like for the test on "BAT" at the place; besides: the same rows.
  `roundsBelowAt_of_member`, `roundsHoldAt_of_member`: `RoundsBelowAt` (RoundsAtMade.lean) and
    `RoundsHoldAt` (RoundsHold.lean) at p and `rad` from the form at q and r: the same stages, rows
    and written rounds; `rad` is r at the stages (`RoundsBelowAt.congr`, `RoundsHoldAt.congr`,
    RoundsHold.lean). No codes, no `pubOk`.
This file stands above Johnson/Bridge/ through its imports, and so above
Cb/Bridge/CodeListRSProved.lean and the files under ThirdParty/: files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Limits: implications between places: no place is named here. Who shows the equations at a
description's places is not said here: the stages, the work, the rows and the own mask hang on what
the planner sizes; the first free own number, the first tree's number and the group's own trees hang
on the plans' rounds. Nothing on soundness. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.CondReads
import Johnson.Desc.K12.Law.WrittenReads
import Johnson.Desc.K12.Law.CondCongr
import Johnson.Desc.K12.Law.RoundsHold

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open scoped ENNReal

/-- **The member's condition is the place's.** -/
theorem k12Condition_of_member {p q : P12} {K K' : Codes} {rad : Sg → ℕ} {r : Fmt.M1.Stage → ℕ}
    {εs : ℝ≥0∞} (hq : K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) q K' εs)
    (hs : p.nums.stages = q.nums.stages) (hW : writtenOf p.nums = writtenOf q.nums)
    (hr : ∀ a ∈ p.nums.stages, rad (sgOf a) = r (sgOf a).st) (hpub : pubOk p K = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ rad p K εs :=
  k12Condition_congr Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) rad
    (fun a ha => (hr a ha).symm) (K12Condition.of_pub hs hW hpub hq)

/-- The premise on the written rounds, from eight equations on the numbers. -/
theorem written_of_fields {p q : P12} (h1 : p.nums.rows = q.nums.rows)
    (h2 : p.nums.work = q.nums.work) (h3 : p.nums.stages = q.nums.stages)
    (h4 : p.nums.ownMask = q.nums.ownMask) (h5 : p.nums.free = q.nums.free)
    (h6 : p.nums.firstTree = q.nums.firstTree)
    (h7 : p.nums.first.isEmpty = q.nums.first.isEmpty)
    (h8 : p.nums.first.filterMap ownOf = q.nums.first.filterMap ownOf) :
    writtenOf p.nums = writtenOf q.nums :=
  writtenOf_reads h1 h2 h3 h4 h5 h6 ⟨h7, h8⟩

/-- The test on "BAT" at the place reads the first stage, its radius and the rows. -/
theorem batPlaceB_of_member {p q : P12} {rad : Sg → ℕ} {r : Fmt.M1.Stage → ℕ}
    (hs : p.nums.stages = q.nums.stages) (h1 : p.nums.rows = q.nums.rows)
    (hr : ∀ a ∈ p.nums.stages, rad (sgOf a) = r (sgOf a).st)
    (hb : batPlaceB q (fun s => r s.st) = true) : batPlaceB p rad = true := by
  unfold batPlaceB batPlaceOf at hb ⊢
  rw [← hs, ← h1] at hb
  cases hst : p.nums.stages with
  | nil =>
    rw [hst] at hb
    cases hb
  | cons a rest =>
    rw [hst] at hb
    rw [List.head?_cons, Option.any_some] at hb ⊢
    rw [hr a (by rw [hst]; exact List.mem_cons_self)]
    exact hb

/-- **Every written round is below, at the place**: the member's `RoundsBelowAt` is the place's. No
codes and no test on a record stand among the premises. -/
theorem roundsBelowAt_of_member {p q : P12} {rad : Sg → ℕ} {r : Fmt.M1.Stage → ℕ} {εs : ℝ≥0∞}
    (hq : RoundsBelowAt q (fun s => r s.st) εs) (hs : p.nums.stages = q.nums.stages)
    (h1 : p.nums.rows = q.nums.rows) (hW : writtenOf p.nums = writtenOf q.nums)
    (hr : ∀ a ∈ p.nums.stages, rad (sgOf a) = r (sgOf a).st) : RoundsBelowAt p rad εs :=
  RoundsBelowAt.congr hs h1 hW hr hq

/-- The like for the form with the radii pinned. -/
theorem roundsHoldAt_of_member {p q : P12} {rad : Sg → ℕ} {r : Fmt.M1.Stage → ℕ} {εs : ℝ≥0∞}
    (hq : RoundsHoldAt q (fun s => r s.st) εs) (hs : p.nums.stages = q.nums.stages)
    (h1 : p.nums.rows = q.nums.rows) (hW : writtenOf p.nums = writtenOf q.nums)
    (hr : ∀ a ∈ p.nums.stages, rad (sgOf a) = r (sgOf a).st) : RoundsHoldAt p rad εs :=
  RoundsHoldAt.congr hs h1 hW hr hq

end H2K.Pub

#print axioms H2K.Pub.k12Condition_of_member
#print axioms H2K.Pub.written_of_fields
#print axioms H2K.Pub.batPlaceB_of_member
#print axioms H2K.Pub.roundsBelowAt_of_member
#print axioms H2K.Pub.roundsHoldAt_of_member
