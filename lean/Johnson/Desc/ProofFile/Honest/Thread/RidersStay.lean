-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/RidersStay.lean: THE COUNTING RIDER ON THE INDEX MASKS'
MESSAGE, AND WHEN THE FIRST CHAIN's THREE SORTS OF CLAUSE STAY. (1) `riderRoom`: the sentence on
the verifier's state that each taker of an entry of the index masks' message can carry on, so that
the batching of the pending rows finds entries enough: AFTER THE HASH BUILD's LEAN LINE's PAGE AND
ITS HOSTILE READER's SENTENCE ("the counting rider for taken"), in the library's own words
(`Walk.Law.ledgerAt`, `Walk.roomOf`, `P1L20.outOfGroupsB`): the message has a ledger; it is not
closed; the room that the request's rows take is at most what is left and the rows that lie on the
pile already; the message is a member of no group. It is constant in the border's number. (2)
`StaysBy` (Honest/Thread/Riders.lean) for `riderHead`, `riderPile`, `riderRoom`, each from one
sentence on the member's clause of `keeps` (the pile's also: the count does not move): whoever lays
the thread calls these at the members that neither lay nor turn the clause. Definitions: a premise's
form and a term; and conditional lemmas.

  `RoomLeft`, `riderRoom`
  `staysBy_head`, `staysBy_pile`, `staysBy_room`

What the rider wants beside it, by that reader (public premises of whoever spends it): more than
one link leaves a row (else the first test on the room says nothing on "closed"); the rider's kCol
is the plan's; the plan's number of rows is at most the number of links that leave a row. hi is
meant to be the border in front of the batching of the pending rows: behind it the sentence is
false in general. At a taker (one entry less, one row more) and at a closing (which shuts its own
group's members' ledgers) `staysBy_room` does not serve: these are laws of their own.

Limits. Nothing shows that the clause can be laid. None is one of the library's goals. This file
proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Riders
import Johnson.Top.H0.Walk.FrameLaw
import Johnson.P1L20R.RoomFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.First (S HeadOwn)

/-- **The index masks' ledger is open and has room for all that is still to be taken.** It is a
definition: a premise's form. -/
def RoomLeft (room : Nat) (s : S) : Prop :=
  ∃ l, Johnson.Desc.First.Walk.Law.ledgerAt s = some l ∧ l.closed = false ∧
    room ≤ l.left + s.out.pending.length

/-- **THE COUNTING RIDER.** fvs: for each link whether it leaves a row. kCol: the plan's number. -/
def riderRoom {W : Type} (lo hi : Nat) (fvs : List Bool) (kCol : Nat) : RiderCl W S :=
  ⟨lo, hi, fun _ _ s =>
    RoomLeft (Johnson.Desc.First.Walk.roomOf fvs kCol) s ∧ P1L20.outOfGroupsB s = true⟩

variable {Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- A fact on the head's own part stays where the member's clause leaves `here`. -/
theorem staysBy_head {b lo hi : Nat} {P : HeadOwn → Prop}
    (hk : ∀ s s', T.keeps b s s' → s'.here = s.here) : StaysBy T b (riderHead lo hi P) :=
  fun _ s s' hK ⟨a, ha, hP⟩ => ⟨a, (hk s s' hK).trans ha, hP⟩

/-- The pile's length stays where the clause leaves it and the count does not move. -/
theorem staysBy_pile {b lo hi : Nat} {n : Nat → Nat}
    (hk : ∀ s s', T.keeps b s s' → s'.out.pending.length = s.out.pending.length)
    (hn : n (b + 1) = n b) : StaysBy T b (riderPile lo hi n) := by
  intro _ s s' hK h0
  show s'.out.pending.length = n (b + 1)
  rw [hk s s' hK, hn]
  exact h0

/-- The counting rider stays where the clause leaves the statement and `out`. -/
theorem staysBy_room {b lo hi : Nat} {fvs : List Bool} {kCol : Nat}
    (hk : ∀ s s', T.keeps b s s' → s'.st = s.st ∧ s'.out = s.out) :
    StaysBy T b (riderRoom lo hi fvs kCol) := by
  intro _ s s' hK h0
  obtain ⟨e1, e2⟩ := hk s s' hK
  obtain ⟨⟨l, hl, hc, hr⟩, hg⟩ := h0
  refine ⟨⟨l, ?_, hc, ?_⟩, ?_⟩
  · unfold Johnson.Desc.First.Walk.Law.ledgerAt at hl ⊢
    rw [e1, e2]
    exact hl
  · rw [e2]
    exact hr
  · have e : P1L20.outOfGroupsB s' = P1L20.outOfGroupsB s :=
      P1L20.outOfGroupsB_same (by rw [e1]) (by rw [e2])
    rw [e]
    exact hg

end ProofFile.Honest

#print axioms ProofFile.Honest.staysBy_head
#print axioms ProofFile.Honest.staysBy_pile
#print axioms ProofFile.Honest.staysBy_room
