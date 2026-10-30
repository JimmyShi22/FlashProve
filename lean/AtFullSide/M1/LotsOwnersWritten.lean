-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/M1/LotsOwnersWritten.lean: a spending entry of rawAheadW whose owner is a sender of the
lots stands at the opening or at W's sending. The test is never run over the 13,116 entries.

  ownersTest, biteTest   the test of OwnersWritten, and of the control, as names
  owners_msgs        by Lean's kernel: the owners of the 26 written messages pass
  owners_short       by Lean's kernel: the eight written pieces pass
  owners_written     **OwnersWritten**: rawAll_whole over three parts. A stretch's entry spends,
                     and its owner is its message's owner, one of the 26 (rawWants_msg_mem). The
                     chain of segments' entries carry and do not spend (segmentCarries_once), so
                     the test passes there on once alone. The written pieces: owners_short
  owners_bite        a control: with W's sender struck the test says no, at foldsFirstW

Limits: written values. rawWants_msg_mem is at the written description and mergesByName's merges,
with that file's limits.
-/
import AtFullSide.M1.LotsDoor
import AtFullSide.K14.RawWantsOnce

set_option autoImplicit false

namespace AtFullSide.M1
open ProofFile.Honest ProofFile.Honest.K14 AtFullSide.K14 OnBytes.SendSim.Seat

/-- The test of OwnersWritten at one entry. -/
def ownersTest (e : Ahead) : Bool :=
  !e.once || e.owner == oOpen || e.owner == oW ||
    !(e.owner.part == 0 && parsW.any fun P => P.place == e.owner.place)

/-- The control's test at one entry: W's sender struck. -/
def biteTest (e : Ahead) : Bool :=
  !e.once || e.owner == oOpen ||
    !(e.owner.part == 0 && parsW.any fun P => P.place == e.owner.place)

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- The owners of the 26 written messages pass. -/
theorem owners_msgs : (rawMsgsW.all fun m => m.owner == oOpen || m.owner == oW ||
    !(m.owner.part == 0 && parsW.any fun P => P.place == m.owner.place)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- The eight written pieces pass. -/
theorem owners_short : rawShortW.all ownersTest = true := by
  decide +kernel

/-- The stretches' entries pass. -/
theorem owners_wants : (rawWantsW.map (·.entry)).all ownersTest = true := by
  rw [List.all_eq_true]
  intro e he
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 he
  unfold rawWantsW at hw
  have hm : w.msg ∈ rawMsgsW := rawWants_msg_mem rawLinksW rawLinks_returns w hw
  have h := List.all_eq_true.1 owners_msgs _ hm
  show (!true || w.msg.owner == oOpen || w.msg.owner == oW ||
    !(w.msg.owner.part == 0 && parsW.any fun P => P.place == w.msg.owner.place)) = true
  simp only [Bool.not_true, Bool.false_or]
  exact h

/-- The chain of segments' entries pass: none of them spends. -/
theorem owners_seg : rawSegW.all ownersTest = true := by
  rw [List.all_eq_true]
  intro e he
  unfold ownersTest
  rw [BookRow.segmentCarries_once rawSeg_returns e he]
  rfl

theorem owners_written : OwnersWritten :=
  rawAll_whole ownersTest owners_wants owners_seg owners_short

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- At the written folds the control's test says no. -/
theorem bite_folds : foldsFirstW.all biteTest = false := by
  decide +kernel

/-- A control: with W's sender struck the test says no: so W's sender owns a spending entry. -/
theorem owners_bite :
    (rawAheadW.all fun e => !e.once || e.owner == oOpen ||
      !(e.owner.part == 0 && parsW.any fun P => P.place == e.owner.place)) = false := by
  show rawAheadW.all biteTest = false
  unfold rawAheadW
  simp only [List.all_append, bite_folds, Bool.and_false, Bool.false_and]

end AtFullSide.M1

#print axioms AtFullSide.M1.owners_msgs
#print axioms AtFullSide.M1.owners_short
#print axioms AtFullSide.M1.owners_written
#print axioms AtFullSide.M1.owners_bite
