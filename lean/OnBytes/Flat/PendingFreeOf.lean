-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/PendingFreeOf.lean: `PendingFree` (OnBytes/Flat/LinksFree.lean) holds: one of the four
statements from which that file has that the rounds of a proof's first chain do not hang on the
request.

`pendingRowH` (OnBytes/Model/StagesLinks.lean) makes the row that a sub-proof leaves on the table:
by `wsPending`, a pure function, and one call that takes the next free mask entry. At two values of
the merge that agree in all but the field elements of what is left of each claim, `wsPending`
refuses both or makes two rows that are equal in all but their weights, which have the same numbers
of variables (`wsPending_alike`, OnBytes/Flat/PendingSizes.lean). The call is one and the same.

Main theorem: `pendingFree : PendingFree`.

Not claimed: the other three statements. Nothing on a run on a view. Two refusals may bear two
names. For proofs only; no module of the program imports this file.


-/
import OnBytes.Flat.LinksFree
import OnBytes.Flat.PendingSizes

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model OnBytes.Model.Stages

/-- A weaker relation holds member by member too. -/
theorem All2.imp {α β : Type} {R R' : α → β → Prop} (h : ∀ a b, R a b → R' a b) {l : List α}
    {l' : List β} (hl : All2 R l l') : All2 R' l l' := by
  induction hl with
  | nil => exact .nil
  | cons h0 _ ih => exact .cons (h _ _ h0) ih

/-- **The row that a sub-proof leaves on the table**: at two values of the merge that are alike,
from every dry context both calls fail, or both return, with one context left and rows that are
alike. -/
theorem pendingFree : PendingFree := by
  intro wsLay im o o' n S h
  have hp := wsPending_alike wsLay h.1
    (h.2.imp fun c c' hc => (⟨hc.1, hc.2.imp fun _ _ hx => hx⟩ : RecSizes c c')) n S
  unfold pendingRowH
  revert hp
  cases wsPending wsLay o n S <;> cases wsPending wsLay o' n S <;> intro hp
  · intro c _
    trivial
  · exact hp.elim
  · exact hp.elim
  · rename_i p p'
    refine relB_same (by show Over.K (m := Blk) _; keeps) fun a => relB_pure ?_
    exact ⟨hp.1, congrArg (fun b => [((⟨im, a⟩ : Slot), b)]) hp.2.1, hp.2.2.1, hp.2.2.2⟩

end OnBytes.Flat
