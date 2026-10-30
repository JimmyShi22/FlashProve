-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ScriptLotsNumbersL.lean: PUBLIC NUMBERS beside ScriptLots.lean, at
the library's written record of the last group's test (`H2K.Member.piLFull`,
Johnson/Desc/K12/Law/PlacesFull.lean). Nine theorems; each closed fact is an evaluation in Lean's
kernel at written values.

  `oracles_len_LFull`, `seeds_send_LFull`, `tenants_LFull`   the record lists 33 rounds' oracle
                 messages; it has one at just the five rounds that `seedRound` names; one tree of
                 two tenants at each
  `depth_LFull`   the rounds below 33 at which a job at the record, whose fresh table came earlier,
                 sends a table (`depthAt`, by which `msgAt` decides) are these five
  `fit_LFull`   each stage of the record fits the next: the library's test `fitAllB` accepts, so its
                 `FitAll` holds (`fitAll_of`, Johnson/Desc/K12/Honest/FirstAsks.lean)
  `fit_bite_LFull`   a control: without its second stage the list does not fit
  `freeRoom_LFull`   the free entries of the five switches' mask tables, by number: none is 0
  `dueRest_LFull`   the second part's own coins: 38038
  `padCoins_LFull`   the five pads' coins are different, and each number is below 38038

What for. `CsFit`'s field main is the fence of a main row in `stageMsg`, its field mask says that
the pad's place is a free entry (ScriptLots.lean's limits).

Beside it. `tabB_L` (AtFullSide/K12/FirstAnyAtHeadL.lean; by the kernel; this record; the fresh
table not the fold's own): the test `tabB` (Sim/FirstPubAtHead.lean) holds, round by round, the
depth and the width that the stages' numbers give against the log-length and the words of the
record's oracle messages: it links `seeds_send_LFull` and `depth_LFull`, and says more of each round
than either; it names no round's number. Not called here.

Limits.
- All that binds whoever builds on ScriptLots.lean (its head) binds here.
- `fit_LFull`'s second limb is its first in another form. That `stageMsg`'s fences, written with k,
  are `CsFit`'s, written with h + g, wants h ≤ k at the six stages: no statement here.
- Which clause of the test bites at the control is not parted by any statement here (by a reckoning
  off the numbers, not by Lean: two at once, main and mask). The other eight have no control of
  their own beside them (`seedRound_bite`, ScriptLotsAtL.lean, is on `seedRound`).
- `padCoins_LFull`: its bound is the written number; that it is the own cut's count is
  `dueRest_LFull`. «Different» is of the five pads among themselves alone: nothing on the free
  entries or the coefficients.
- `seeds_send_LFull` and `depth_LFull` look below 33 alone; beyond the lists `getD` gives nothing:
  no statement. They speak of the record and of `msgAt`'s own test, not of a seated block or a run.
  hf is wanted: where the first fold sends its own table, own round 1 sends too.
- At the written record alone; that a seated place or a job's parameters are that record is other
  files' matter. Nothing on a block, a part or a run.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.ScriptLotsAtL
import Johnson.Desc.K12.Honest.FirstAsks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12

/-- The written record lists 33 rounds' oracle messages. -/
theorem oracles_len_LFull : H2K.Member.piLFull.oracles.length = 33 := by
  decide +kernel

/-- **The rounds at which the written record has an oracle message are the five that `seedRound`
names.** -/
theorem seeds_send_LFull :
    (List.range 33).filter (fun i => !(H2K.Member.piLFull.oracles.getD i []).isEmpty) =
      (List.range 5).map (seedRound H2K.Member.piLFull.nums.stages) := by
  decide +kernel

/-- At each of the five: one tree, of two tenants. -/
theorem tenants_LFull :
    ((List.range 5).map (seedRound H2K.Member.piLFull.nums.stages)).map
      (fun i => (H2K.Member.piLFull.oracles.getD i []).map (·.tenants.length)) = [[2], [2], [2],
        [2], [2]] := by
  decide +kernel

/-- **The rounds below 33 at which a job at the written record, whose fresh table came earlier,
sends a table** (`depthAt`, Test.lean: by it `msgAt` decides) **are these five.** -/
theorem depth_LFull {W X : Type} (J : TestJob W X) (hJ : J.p = H2K.Member.piLFull) (hf :
  J.fresh.isNone = false) :
    (List.range 33).filter (fun i => (depthAt J i).isSome) = [3, 10, 16, 22, 29] := by
  have e : (fun i => (depthAt J i).isSome) =
      fun i => ((none :: depths false H2K.Member.piLFull.nums.stages).getD i none).isSome := by
    funext i
    unfold depthAt
    rw [hJ, hf]
  rw [e]
  decide +kernel

/-- **(T-f) Each stage of the written record fits the next**: the library's test, and its `FitAll`.
-/
theorem fit_LFull :
    fitAllB (H2K.Member.piLFull.nums.stages.headD default) H2K.Member.piLFull.nums.stages.tail =
      true ∧
      FitAll (H2K.Member.piLFull.nums.stages.headD default)
        H2K.Member.piLFull.nums.stages.tail := by
  have h : fitAllB (H2K.Member.piLFull.nums.stages.headD default)
      H2K.Member.piLFull.nums.stages.tail = true := by
    decide +kernel
  exact ⟨h, fitAll_of _ _ h⟩

/-- A control: without its second stage the list does not fit. -/
theorem fit_bite_LFull :
    fitAllB (H2K.Member.piLFull.nums.stages.headD default)
      (H2K.Member.piLFull.nums.stages.tail.tail) = false := by
  decide +kernel

/-- The free entries of the five switches' mask tables, by number: none is 0. -/
theorem freeRoom_LFull :
    (List.range 5).map (fun τ => freeRoom (H2K.Member.piLFull.nums.stages.getD τ default)
      (H2K.Member.piLFull.nums.stages.getD (τ + 1) default)) = [15727, 8027, 3931, 1883, 374] := by
  decide +kernel

/-- The second part's own coins, by number. -/
theorem dueRest_LFull : dueRest H2K.Member.piLFull.nums.stages = 38038 := by
  decide +kernel

/-- The pad's coin at each switch lies inside the own cut, and the five are different coins. -/
theorem padCoins_LFull :
    ((List.range 5).map fun τ => (marksAt H2K.Member.piLFull.nums.stages τ).free +
      (freeRoom (H2K.Member.piLFull.nums.stages.getD τ default) (H2K.Member.piLFull.nums.stages.getD
        (τ + 1) default) - 1)).Nodup ∧
    ∀ τ < 5, (marksAt H2K.Member.piLFull.nums.stages τ).free +
      (freeRoom (H2K.Member.piLFull.nums.stages.getD τ default) (H2K.Member.piLFull.nums.stages.getD
        (τ + 1) default) - 1) < 38038 := by
  decide +kernel

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.oracles_len_LFull
#print axioms ProofFile.Honest.K12.seeds_send_LFull
#print axioms ProofFile.Honest.K12.tenants_LFull
#print axioms ProofFile.Honest.K12.depth_LFull
#print axioms ProofFile.Honest.K12.fit_LFull
#print axioms ProofFile.Honest.K12.fit_bite_LFull
#print axioms ProofFile.Honest.K12.freeRoom_LFull
#print axioms ProofFile.Honest.K12.dueRest_LFull
#print axioms ProofFile.Honest.K12.padCoins_LFull
