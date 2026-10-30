-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/RoomFor.lean: A COUNTING TEST ON THE INDEX MASKS' LEDGER, AND TWO LAWS ON IT.
The law "the pending row can be made of what K4's hearing leaves"
(Johnson/Road/K4/Total/RowReturns.lean) asks roomB: the ledger has an entry to take. roomB is no
invariant of the chain: each link that leaves a row takes an entry. What can ride from border to
border is a count. A definition with code, statements and proofs.

  `roomFor n s`: A TEST WITH CODE: the state's index masks' message has a ledger (ledgerAt,
    Johnson/Top/H0/Walk/FrameLaw.lean) that is open and has at least n entries left.
  `roomB_of_roomFor`: room for at least one entry gives roomB at the state's own letters.
  `roomFor_kept`: the test rides over a yes of K4's block: it reads the state's statement and its
    number of the index masks' message alone, which Rest keeps
    (Johnson/Desc/First/K4/ReadsAtS.lean).
No new argument: the texts unfolded.
**Limits.** roomFor IS A DEFINITION OF THIS FILE, AND NOT THE TABLE's ITEM: the name "pile.room" is
to say more: just how many entries are left; roomFor is what K4's law needs of it; it says nothing
on WHICH entry is next; n is a letter: that it is the number of rows still to come is said nowhere.
Who makes the test true at the chain's first link, and who carries it past a link's end, where an
entry is taken: not said here. Nothing on soundness. K04_law, the law of K4's block itself, IS NOT
PROVED. Met through Lean at no member; no run is cited here.


-/
import Johnson.Road.K4.Total.RowReturns
import Johnson.Desc.First.K4.ReadsAtS
import Johnson.Top.H0.Walk.FrameLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Total

open OnBytes
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Pend (takeEntry)
open Johnson.Desc.First.Walk.Law (ledgerAt)

/-- The index masks' message has a ledger that is open and has at least n entries left. -/
def roomFor (n : Nat) (s : S) : Bool :=
  (ledgerAt s).any fun l => !l.closed && decide (n ≤ l.left)

/-- Room for at least one entry: the ledger has an entry to take. -/
theorem roomB_of_roomFor {n : Nat} {s : S} (hn : 1 ≤ n) (h : roomFor n s = true) :
    roomB s.out.indexMasks s.st.oracles = true := by
  unfold roomFor at h
  cases hl : ledgerAt s with
  | none =>
    rw [hl] at h
    cases h
  | some l =>
    rw [hl] at h
    have h' : (!l.closed && decide (n ≤ l.left)) = true := h
    rw [Bool.and_eq_true] at h'
    have h2 : n ≤ l.left := of_decide_eq_true h'.2
    show ((ledgerAt s).bind takeEntry).isSome = true
    rw [hl]
    show (takeEntry l).isSome = true
    unfold takeEntry
    rw [if_pos (by
      rw [Bool.and_eq_true]
      exact ⟨h'.1, decide_eq_true (by omega)⟩)]
    rfl

/-- The test rides over a yes of K4's block. -/
theorem roomFor_kept {s s' : S} (R : Rest s s') (n : Nat) : roomFor n s' = roomFor n s := by
  unfold roomFor ledgerAt
  rw [R.st, R.out]

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.roomB_of_roomFor
#print axioms OnBytes.Desc.First.K4.Total.roomFor_kept
