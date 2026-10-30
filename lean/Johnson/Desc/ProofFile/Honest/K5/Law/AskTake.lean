-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AskTake.lean: THE FRAME's CALL THAT ASKS FIRST (`RowData.ask`,
Johnson/Desc/ProofFile/Honest/RowData.lean) DOES NOT READ BEYOND THE CHALLENGES THAT HAVE BEEN HEARD
WHEN THE MESSAGE's SENDING BEGINS. One theorem, at every filling, reader, list of challenges and
address. No premise.

What it is for. A form in which a kind states what it asks of a script's message reads the asker's
text at the first fx challenges alone. Where the text is this call, at fx := the filling's
`heardAt`, this law says that cutting the list there changes nothing.

Main name:
  `ask_take`: the call at the list cut at `D.heardAt a` is the call at the whole list.

How. Where at least that many challenges have been heard: the call's first test passes on both
sides, and its second test and `RowData.at_` read the list through that very cut. Where fewer have
been heard the cut returns the list itself.

Limits. Of what the call answers nothing is said. It is a lemma on the frame's routine: if the frame
has or wants its like, the frame's is the one to keep.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.RowData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5

/-- **The call that asks first reads the challenges through the cut at `heardAt` alone.** -/
theorem ask_take (D : RowData) (R : Readers) (hd : List Fmt.Drawn) (a : MsgAddr) (r j : ℕ) :
    D.ask R (hd.take (D.heardAt a)) a r j = D.ask R hd a r j := by
  by_cases h : D.heardAt a ≤ hd.length
  · simp [RowData.ask, RowData.heardOk, RowData.at_, List.take_take, List.length_take, h]
  · rw [List.take_of_length_le (by omega)]

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.ask_take
