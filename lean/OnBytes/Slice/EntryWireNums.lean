-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/EntryWireNums.lean: three bounds on the rounds' data of an entry's chain, at the
full-size and at the small files of the setting "record with work": what a wire of the link's
protocol asks of them.

Main theorems.
 `wireNums_of_within`   at any map of statements: no round's verifier message needs more blocks
                than the description's own number `XD.K` (true of every description: that number is
                the greatest over the rounds); and for a description within the limits test
                `withinX`: no round asks for more than 64 bits of work; every tree of the
                chain's own that a round opens has a number below 2^16.
 `fr_wire_blocks`, `fr_wire_work`, `fr_wire_own`   the three at `frRds`
                (OnBytes/Slice/LinkFamily.lean), with `frD.K` for the number of blocks.
 `sr_wire_blocks`, `sr_wire_work`, `sr_wire_own`   the three at `srRds`, with `srD.K`.
The two numbers themselves: OnBytes/Slice/EntryWireK.lean.

Limits: bounds on typed data. Nothing on a wire's laws, on soundness, on bytes or files.

-/
import OnBytes.Slice.LinkFamily
import OnBytes.Slice.TopAny
import OnBytes.Tie.EntryGrounds
import Run.PlanPullM1

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Run _root_.Run.PQ
open OnBytes.Tie (xdOf withinX)

/-- The three bounds, at a description within the limits test. -/
theorem wireNums_of_within (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
    (hw : withinX S = true) :
    (∀ d ∈ (xdOf S stm).ds,
      (bsRound (xdOf S stm).base.plan.field d.entry d.kind).b ≤ (xdOf S stm).K) ∧
    (∀ d ∈ (xdOf S stm).ds, d.entry.work ≤ 64) ∧
    ∀ d ∈ (xdOf S stm).ds, ∀ n ∈ d.opens, n < 2 ^ 16 := by
  refine ⟨fun d hd => le_kMax (fun e k => (bsRound (xdOf S stm).base.plan.field e k).b)
    (rds (xdOf S stm).base) d hd, fun d hd => ?_, okX_own _ _ _ (within_okx S stm hw)⟩
  have h := within_work S stm hw
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h d hd)

/-- The full-size description is within the limits test at the empty statement. -/
theorem fr_within : withinX
    (Params.entrySpecOf Params.recordRead Params.recordRounds ByteArray.empty) = true :=
  Tie.record_within ByteArray.empty (by decide)

/-- The small description is within the limits test at the empty statement. -/
theorem sr_within : withinX
    (Params.entrySpecOf Params.smallRecordRead Params.smallRecordRounds ByteArray.empty) = true :=
  Tie.small_record_within ByteArray.empty (by decide)

/-- No round's verifier message needs more blocks than `frD.K`. -/
theorem fr_wire_blocks : ∀ d ∈ frRds, (bsRound .two d.entry d.kind).b ≤ frD.K := by
  have h := (wireNums_of_within _ (fun _ _ => ByteArray.empty) fr_within).1
  intro d hd
  exact h d (fr_ds_C ▸ hd)

/-- No round asks for more than 64 bits of work. -/
theorem fr_wire_work : ∀ d ∈ frRds, d.entry.work ≤ 64 := by
  have h := (wireNums_of_within _ (fun _ _ => ByteArray.empty) fr_within).2.1
  intro d hd
  exact h d (fr_ds_C ▸ hd)

/-- Every tree of the chain's own that a round opens has a number below 2^16. -/
theorem fr_wire_own : ∀ d ∈ frRds, ∀ n ∈ d.opens, n < 2 ^ 16 := by
  have h := (wireNums_of_within _ (fun _ _ => ByteArray.empty) fr_within).2.2
  intro d hd
  exact h d (fr_ds_C ▸ hd)

/-- No round's verifier message needs more blocks than `srD.K`. -/
theorem sr_wire_blocks : ∀ d ∈ srRds, (bsRound .two d.entry d.kind).b ≤ srD.K := by
  have h := (wireNums_of_within _ (fun _ _ => ByteArray.empty) sr_within).1
  intro d hd
  exact h d (sr_ds_C ▸ hd)

/-- No round asks for more than 64 bits of work, at the small files. -/
theorem sr_wire_work : ∀ d ∈ srRds, d.entry.work ≤ 64 := by
  have h := (wireNums_of_within _ (fun _ _ => ByteArray.empty) sr_within).2.1
  intro d hd
  exact h d (sr_ds_C ▸ hd)

/-- Every tree of the chain's own that a round opens has a number below 2^16, at the small files. -/
theorem sr_wire_own : ∀ d ∈ srRds, ∀ n ∈ d.opens, n < 2 ^ 16 := by
  have h := (wireNums_of_within _ (fun _ _ => ByteArray.empty) sr_within).2.2
  intro d hd
  exact h d (sr_ds_C ▸ hd)

end OnBytes.Slice
