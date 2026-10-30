-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/KeepsFrame.lean: THE CLAUSE OF keeps AT ALL MEMBERS OF THE
KIND frame OF THE FIRST CHAIN, AS ONE WRITTEN TEXT. The thread's letter keeps goes by the member's
place, and by the place's kind (`kpBy`, Honest/Thread/KeepsBy.lean). The kind frame has no authors
of its own: its clause is ours. 77 members: the front; at each of 25 links «laid», «behind the
batching», «cleared»; the seal. Here: the clause by the place (`keepsFrame`); what it is at each
sort of place (four equations); the general payer at «cleared» (`keepsCleared_of`, from the
library's `ClearedRec`); and what readers of the state get of it.

WHAT THIS IS. Two definitions that fill a letter of the thread and that whoever rides past such a
member spends; lemmas on them. None of the library's goals.

  1  `keepsCleared`, `keepsFrame`
  2  `keepsFrame_out`, `keepsFrame_laid`, `keepsFrame_behind`, `keepsFrame_cleared`
  3  `keepsCleared_of`
  4  `keepsFrame_mark`, `keepsFrame_reply`, `keepsFrame_masks`, `keepsCleared_still`,
     `keepsCleared_take`

WHO PAYS IT WHERE. At «behind the batching»: `after_keeps` (Honest/Law/NoHouse/BehindShare.lean): IT
TAKES «no mark in front»: that member is a bare sub-protocol without a guard on the mark, so the
mark behind does not follow from its yes alone: whoever goes ONE STEP BACK from a reached state,
outside the thread, does not get the clause there. At «cleared»: `keepsCleared_of`, with the
library's `clearedGives` at every row of frames; that the row's flag is take l is a fact on the
public files, not shown here. At the front, «laid» and the seal: that a yes hands the state on:
files of another author of this folder.

Limits. Shown here at no member. This file proves nothing about soundness, completeness, hiding or
any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BehindKeeps
import Johnson.Top.H0.Walk.FrameGives
import Johnson.Desc.First.Link.Law.LinkPlacesFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.LinkJoin (hearN)
open Johnson.Desc.First.Walk.Tied (ClearedRec)

/-! ## 1 The clause -/

/-- **WHAT «LINK l: CLEARED» KEEPS AND TURNS.** take: the link leaves a pending row. The clauses of
the library's `ClearedRec` (Johnson/Top/H0/Walk/FrameGives.lean) that name none of its parameters
but the flag, with the mark inside: no mark behind; the chain stands between two links; the state of
the calls is the open link's copy; the book, the roots, the count of rows that is owed, the request,
the statement's codes and groups, its oracle messages but for their ledgers, the reply and the index
masks' message are as they were; where no row is left, what goes on to the later chains and the
statement are as they were, whole; where one is left, the pile has just that one row more. -/
def keepsCleared (take : Bool) (s t : S) : Prop :=
  t.failed = none ∧ t.atBetween = true ∧ t.check = s.live ∧ t.live = s.live ∧ t.book = s.book ∧
    t.roots = s.roots ∧ t.rowsOwed = s.rowsOwed ∧ t.req = s.req ∧ t.st.codes = s.st.codes ∧
    t.st.groups = s.st.groups ∧ t.st.oracles.size = s.st.oracles.size ∧
    (∀ i : Nat, (t.st.oracles[i]?).map (fun (x : OnBytes.Oracle) => { x with ledger := none }) =
      (s.st.oracles[i]?).map fun (x : OnBytes.Oracle) => { x with ledger := none }) ∧
    t.out.reply = s.out.reply ∧ t.out.indexMasks = s.out.indexMasks ∧
    (take = false → t.out = s.out ∧ t.st = s.st) ∧
    (take = true → ∃ r, t.out.pending = s.out.pending ++ [r])

/-- **THE CLAUSE OF keeps AT A MEMBER OF THE KIND frame OF THE FIRST CHAIN, BY ITS PLACE.** links:
the chain's sorts of segments; take l: link l leaves a pending row. Outside the links (the front;
the seal) and at a link's piece 0 («laid»): the state is handed on, with no mark. At the piece
behind the batching: `keepsBehind`. At a link's last piece («cleared»): `keepsCleared`. THE LAST ARM
TAKES EVERY OTHER PIECE FOR «cleared»: harmless where the clause is read at places of the kind frame
alone, which have no other piece: a closed fact on the written list, not shown here. -/
def keepsFrame (links : List ModelPart) (take : Nat → Bool) (p : Place) (s t : S) : Prop :=
  match p.link with
  | none => t = s ∧ t.failed = none
  | some l =>
    if p.piece = 0 then t = s ∧ t.failed = none
    else if p.piece = hearN links l + 2 then keepsBehind s t
    else keepsCleared (take l) s t

/-! ## 2 What it is at each sort of place -/

theorem keepsFrame_out (links : List ModelPart) (take : Nat → Bool) {p : Place} (hp : p.link = none)
    (s t : S) : keepsFrame links take p s t ↔ t = s ∧ t.failed = none := by
  unfold keepsFrame
  rw [hp]

theorem keepsFrame_laid (links : List ModelPart) (take : Nat → Bool) {p : Place} {l : Nat}
    (hp : p.link = some l) (h0 : p.piece = 0) (s t : S) :
    keepsFrame links take p s t ↔ t = s ∧ t.failed = none := by
  unfold keepsFrame
  rw [hp]
  simp only [h0, if_true]

theorem keepsFrame_behind (links : List ModelPart) (take : Nat → Bool) {p : Place} {l : Nat}
    (hp : p.link = some l) (h1 : p.piece = hearN links l + 2) (s t : S) :
    keepsFrame links take p s t ↔ keepsBehind s t := by
  unfold keepsFrame
  rw [hp]
  have h0 : p.piece ≠ 0 := by omega
  simp only [if_neg h0, if_pos h1]

theorem keepsFrame_cleared (links : List ModelPart) (take : Nat → Bool) {p : Place} {l : Nat}
    (hp : p.link = some l) (h0 : p.piece ≠ 0) (h1 : p.piece ≠ hearN links l + 2) (s t : S) :
    keepsFrame links take p s t ↔ keepsCleared (take l) s t := by
  unfold keepsFrame
  rw [hp]
  simp only [h0, h1, if_false]

/-! ## 3 The payer at «cleared» -/

/-- **From the library's `ClearedRec`, with no mark behind.** -/
theorem keepsCleared_of {X : Johnson.Desc.First.Walk.LinkPub}
    {left : S → Option OnBytes.Model.WsForkOut} {lay : OnBytes.Model.WsLay}
    {lin : OnBytes.Params.LinShape} {s t : S} (h : ClearedRec X left lay lin s t)
    (h0 : t.failed = none) : keepsCleared X.fv s t := by
  obtain ⟨a1, a2, a3, a4, a5, a6, -, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := h
  exact ⟨h0, a1, a2, a3, a4, a5, a6, a8, a9, a10, a11, a12, a13, a14, a15,
    fun hf => (a16 hf).elim fun r hr => ⟨r, hr.2⟩⟩

/-! ## 4 What readers get -/

/-- No mark behind, at whatever place. -/
theorem keepsFrame_mark {links : List ModelPart} {take : Nat → Bool} {p : Place} {s t : S}
    (h : keepsFrame links take p s t) : t.failed = none := by
  unfold keepsFrame at h
  split at h
  · exact h.2
  · split at h
    · exact h.2
    · split at h
      · exact h.2.2.1
      · exact h.1

/-- The reply is as it was, at whatever place. -/
theorem keepsFrame_reply {links : List ModelPart} {take : Nat → Bool} {p : Place} {s t : S}
    (h : keepsFrame links take p s t) : t.out.reply = s.out.reply := by
  unfold keepsFrame at h
  split at h
  · rw [h.1]
  · split at h
    · rw [h.1]
    · split at h
      · rw [keepsBehind_out h]
      · exact h.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The index masks' message is as it was, at whatever place. -/
theorem keepsFrame_masks {links : List ModelPart} {take : Nat → Bool} {p : Place} {s t : S}
    (h : keepsFrame links take p s t) : t.out.indexMasks = s.out.indexMasks := by
  unfold keepsFrame at h
  split at h
  · rw [h.1]
  · split at h
    · rw [h.1]
    · split at h
      · rw [keepsBehind_out h]
      · exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- At a link that leaves no row: what goes on to the later chains, and the statement, whole. -/
theorem keepsCleared_still {s t : S} (h : keepsCleared false s t) : t.out = s.out ∧ t.st = s.st :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

/-- **At a take: the pile is longer by one.** -/
theorem keepsCleared_take {s t : S} (h : keepsCleared true s t) :
    t.out.pending.length = s.out.pending.length + 1 := by
  obtain ⟨r, e⟩ := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 rfl
  rw [e, List.length_append]
  rfl

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.keepsFrame_out
#print axioms ProofFile.Honest.FirstThread.keepsFrame_laid
#print axioms ProofFile.Honest.FirstThread.keepsFrame_behind
#print axioms ProofFile.Honest.FirstThread.keepsFrame_cleared
#print axioms ProofFile.Honest.FirstThread.keepsCleared_of
#print axioms ProofFile.Honest.FirstThread.keepsFrame_mark
#print axioms ProofFile.Honest.FirstThread.keepsFrame_reply
#print axioms ProofFile.Honest.FirstThread.keepsFrame_masks
#print axioms ProofFile.Honest.FirstThread.keepsCleared_still
#print axioms ProofFile.Honest.FirstThread.keepsCleared_take
