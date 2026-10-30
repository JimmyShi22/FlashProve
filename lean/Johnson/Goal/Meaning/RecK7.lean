-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RecK7.lean: kind K7's block (the next token) at the first chain's record writes
neither the statement nor a copy of the frame of the links: it is Quiet
(Johnson/Goal/Meaning/RecQuiet.lean).

  k7_whole: A GENERAL RULE, at any record and seat: a relation that the seat's one laying (setReply)
    keeps is kept by the kind's block (Johnson/Desc/Kinds/ReplyBlock.lean). It has neither claims
    nor a run behind the batching.
  seatAt_set: the seat at the record (Johnson/Stored/ReplySeatAt.lean) lays Quietly:
    it writes the heard reply's one home, out.reply.
  entered_whole: the named test in front of a block's decide (entered) keeps what the block keeps.
  k7_quiet: Whole Quiet (Reply.blockAt l V). k7Of_quiet: Whole Quiet (Reply.blockOf W l).
With whole_rec and whole_grows each gives Whole (RecRel cs sh) and Whole (GrowsBy fun s => s.st).
Not claimed: anything on another kind's blocks.
OBJECT: the makers' blocks and steps that are named above. USERS: through whole_rec |
recRel_of_quiet the walk (Johnson/Goal/Meaning/RecWalk.lean: recAll_border, at the letters cs and
sh); through whole_grows | groundKeeps_grows the owed premise of Johnson/Desc/StatementGrows.lean
(ChainKeeps (GrowsBy st) c). Neither calls them yet. Which maker stands at which place of a seated
text is not said here.
-/
import Johnson.Goal.Meaning.RecK3
import Johnson.Stored.ReplySeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Keeps (Whole)

/-- **A relation that the seat's laying keeps is kept by K7's block.** -/
theorem k7_whole {T Cl : Type} (R : T → T → Prop) (L : Reply.Seat T)
    (hset : ∀ s h, R s (L.setReply s h)) (link piece V : Nat) :
    Whole R (Reply.kind (Cl := Cl) L link piece V) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hx => nomatch hx), (fun _ hx => nomatch hx)⟩
  have h' : Reply.decideE V L s rs = .ok s' := h
  unfold Reply.decideE at h'
  repeat' split at h'
  all_goals first
    | (cases h'; exact hset _ _)
    | cases h'

theorem seatAt_set (s : S) (h : E) : Quiet s (Reply.seatAt.setReply s h) := by
  simp only [Reply.seatAt]
  exact ⟨⟨rfl, fun _ hf => hf, rfl, rfl⟩, rfl, fun w => w, fun _ e => e⟩

/-- The named test in front of a block's decide keeps what the block keeps. -/
theorem entered_whole {R : S → S → Prop} {b : Block S Unit} (W : Whole R b) :
    Whole R (Reply.entered b) := by
  refine ⟨fun s rs gs s' h => ?_, W.2.1, W.2.2⟩
  simp only [Reply.entered] at h
  repeat' split at h
  all_goals first
    | exact W.1 _ _ _ _ h
    | cases h

/-- **K7's block at the record is Quiet.** -/
theorem k7_quiet (l V : Nat) : Whole Quiet (Reply.blockAt l V) :=
  entered_whole (k7_whole Quiet _ seatAt_set l 1 V)

theorem k7Of_quiet (W : Verify.Public) (l : Nat) : Whole Quiet (Reply.blockOf W l) :=
  k7_quiet l W.hS.V

#print axioms k7_whole
#print axioms k7_quiet
#print axioms k7Of_quiet

end Meaning.K2
