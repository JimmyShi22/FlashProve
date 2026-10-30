-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/KeepEach.lean: the closing of a segment (K10): a link has two tests that return
no state: the test behind each run of claims (Johnson/Desc/First/Batch/EachAtS.lean: eachAtS) and the tests behind the
adding (Johnson/Desc/ProofFile/Lot/K9.lean: k9Tests). Each has one outcome at two states of the first chain that are
one once wiped. Theorems alone.

Words. wipeS sets to zero the targets of the rows that a state of the first chain holds (Honest/K10/WipeS.lean says
which). "At both states": at wipeS s and at s. Test2 wipeS t (Wipe/Alike.lean): t has one outcome at two states s, s'
with wipeS s = wipeS s'.

What is proved.
  k8Window_blind, dueAtS_blind, eachAtS_blind   what the first test reads, and the test itself, are one at both states
  mergeOf_blind, tGet_blind, claimsCounted_blind, tablesHeld_blind, countsAt_blind, countsHold_blind   the same of
                  what the second test reads
  **each_keeps**    Test2 wipeS (eachAtS k o cl): the field each of SeatKeeps2 (Wipe/Lots2.lean)
  **tests_keeps**   k9Tests Z l = some t ⊢ Test2 wipeS t: its field tests

By what. The two tests read the sub-proof's engine, the smallness test's record, the tables and the slot of the
merge's end value. For the first three: Wipe/WipeLaws.lean's fork?_wipe, tl?_wipe, funs?_wipe. For the slot, and for the
part that holds it, the state is taken apart by the kind of place.

Limits. The texts windowsOk and freeSlot, which the tests call, are not opened: they are handed equal values. No
property of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepBase
import Johnson.Desc.First.Batch.EachAtS
import Johnson.Desc.ProofFile.Lot.K9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (SegSort mergeOf k8Window dueAtS eachAtS eachRun tAtS claimsCounted tablesHeld countsAt
  countsHold)

/-! ## 1 The test behind each run of claims -/

/-- The smallness test's window of slots is one at both states. -/
theorem k8Window_blind (k : SegSort) (s : S) : k8Window k (wipeS s) = k8Window k s := by
  unfold k8Window
  rw [tl?_wipe]

/-- The number of claims that is due of a run is one at both states. -/
theorem dueAtS_blind (k : SegSort) (run : Nat × String) (s : S) : dueAtS k run (wipeS s) = dueAtS k run s := by
  unfold dueAtS
  rw [tl?_wipe]

/-- The test behind a run of claims has one outcome at both states. -/
theorem eachAtS_blind (k : SegSort) (o : Nat × String) (cl : List Claim) (s : S) :
    eachAtS k o cl (wipeS s) = eachAtS k o cl s := by
  unfold eachAtS eachRun
  rw [k8Window_blind, dueAtS_blind]

/-- **The test behind each run of claims (Link.each) has one outcome at two states that are one once wiped.** -/
theorem each_keeps (k : SegSort) (o : Nat × String) (cl : List Claim) : Test2 wipeS (eachAtS k o cl) :=
  Test2.of_blind (eachAtS_blind k o cl)

/-! ## 2 The tests behind the adding -/

/-- The slot of the merge's end value is one at both states. -/
theorem mergeOf_blind (s : S) : mergeOf (wipeS s) = mergeOf s := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl

/-- The part that the tests behind the adding read is one at both states. -/
theorem tGet_blind (s : S) : tAtS.get? (wipeS s) = tAtS.get? s := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- Whether as many claims were added as the plan counts is one at both states. -/
theorem claimsCounted_blind (nLin : Nat) (s : S) : claimsCounted nLin (wipeS s) = claimsCounted nLin s := by
  unfold claimsCounted
  rw [fork?_wipe]

/-- Whether the list of tables is still the list that was closed is one at both states. -/
theorem tablesHeld_blind (s : S) : tablesHeld (wipeS s) = tablesHeld s := by
  unfold tablesHeld
  rw [tl?_wipe, funs?_wipe]

/-- Each of the counts that a sort of segment asks is one at both states. -/
theorem countsAt_blind (k : SegSort) (nLin : Nat) (s : S) : ∀ c ∈ countsAt k nLin, c.2 (wipeS s) = c.2 s := by
  intro c hc
  cases k with
  | layers =>
    rcases List.mem_cons.1 hc with rfl | hc
    · exact claimsCounted_blind nLin s
    · rcases List.mem_cons.1 hc with rfl | hc
      · exact tablesHeld_blind s
      · cases hc
  | attention =>
    rcases List.mem_cons.1 hc with rfl | hc
    · exact claimsCounted_blind nLin s
    · rcases List.mem_cons.1 hc with rfl | hc
      · exact tablesHeld_blind s
      · cases hc
  | head =>
    rcases List.mem_cons.1 hc with rfl | hc
    · exact claimsCounted_blind nLin s
    · rcases List.mem_cons.1 hc with rfl | hc
      · show (((wipeS s).tl?.map (·.foldDrawn == 1)).getD false) = ((s.tl?.map (·.foldDrawn == 1)).getD false)
        rw [tl?_wipe]
      · rcases List.mem_cons.1 hc with rfl | hc
        · show (((wipeS s).tl?.map (1 + ·.groupsRun == 2)).getD false) = ((s.tl?.map (1 + ·.groupsRun == 2)).getD false)
          rw [tl?_wipe]
        · rcases List.mem_cons.1 hc with rfl | hc
          · exact tablesHeld_blind s
          · cases hc

/-- These counts, asked in a row, have one outcome at both states. -/
theorem countsHold_blind (k : SegSort) (nLin : Nat) (s : S) :
    countsHold (countsAt k nLin) (wipeS s) = countsHold (countsAt k nLin) s := by
  unfold countsHold
  refine forM_same _ _ _ fun c hc => ?_
  simp only [countsAt_blind k nLin s c hc]

/-- **The tests behind the adding (Link.tests) have one outcome at two states that are one once wiped.** -/
theorem tests_keeps (Z : ProofFile.Pub) (l : Nat) (t : S → Except String Unit) (h : ProofFile.k9Tests Z l = some t) :
    Test2 wipeS t := by
  unfold ProofFile.k9Tests at h
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 h
  refine Test2.of_blind fun s => ?_
  simp only [tGet_blind, countsHold_blind]

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.k8Window_blind
#print axioms ProofFile.Honest.K10.dueAtS_blind
#print axioms ProofFile.Honest.K10.eachAtS_blind
#print axioms ProofFile.Honest.K10.each_keeps
#print axioms ProofFile.Honest.K10.mergeOf_blind
#print axioms ProofFile.Honest.K10.tGet_blind
#print axioms ProofFile.Honest.K10.claimsCounted_blind
#print axioms ProofFile.Honest.K10.tablesHeld_blind
#print axioms ProofFile.Honest.K10.countsAt_blind
#print axioms ProofFile.Honest.K10.countsHold_blind
#print axioms ProofFile.Honest.K10.tests_keeps
