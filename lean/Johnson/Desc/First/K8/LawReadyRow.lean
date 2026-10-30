-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawReadyRow.lean: THE SMALLNESS TEST: WHAT EACH BLOCK IN FRONT OF THE DRAW
OWES, SO THAT THE BLOCK OF THE DRAW DOES NOT REFUSE: THE READINGS AND THE FORM, TYPED ONCE FOR ALL
KINDS.

The decision of the block of the draw says yes at a carried record if and only if seven clauses hold
there (`MeansAtS`, Johnson/Desc/First/K8/HearMeans.lean). Five of them speak of fields of the
smallness test's record that are laid when the link is entered and that no block in front may turn;
one of a mark that the closing of the list of tables lays; one of the count of rows that is owed.
  `Ready.keep s`: the five: the number of matrices, the matrices, the number of combinations, the
    field for the drawn matrix, the count of draws.
  `Ready.closedAt s`: the mark "the list of tables is closed".
  `Ready.LeavesFront b`: WHAT A BLOCK IN FRONT OWES: where its decision goes on, `keep` and
    `closedAt` are as they were (`Block.Leaves`, Johnson/Desc/Sound/FoldHeard.lean), and if no count
    waited in front, none waits behind.
  `Ready.leavesFront_of_tl`: a block that leaves the whole record of the smallness test (`S.tl?`)
    and the count that is owed (`S.rowsOwed`) as they were pays it.
Definitions, one statement and its proof.
Limits. NOTHING IS SAID OF ANY BLOCK HERE: each kind's files pay `LeavesFront` for their own. The
block that closes the list does not leave `closedAt`: it owes `keep`, the count, and the laying of
the mark. WHERE `S.tl?` ANSWERS none BOTH READINGS ARE none AND CARRY NOTHING: at the head's link
that is so until the link is opened: whoever opens it owes that `S.tl?` behind is the record that
was laid at the entry.

-/
import Johnson.Desc.First.State
import Johnson.Desc.Sound.FoldHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Ready

open OnBytes.Model

/-- The five fields that are laid at the link's entry and that no block in front may turn. -/
def keep (s : S) : Option (Nat × Array TMat × Nat × Array Int × Nat) :=
  s.tl?.map fun tl => (tl.NM, tl.mats, tl.tau, tl.cfF, tl.foldDrawn)

/-- The mark "the list of tables is closed". -/
def closedAt (s : S) : Option Bool := s.tl?.map (·.funClosed)

/-- What a block in front of the draw owes. -/
def LeavesFront {Cl : Type} (b : Block S Cl) : Prop :=
  b.Leaves keep ∧ b.Leaves closedAt ∧
    ∀ s rs gs s', b.decide s rs gs = .ok s' → s.noneWaits = true → s'.noneWaits = true

/-- A block that leaves the whole record of the smallness test and the count that is owed pays
it. -/
theorem leavesFront_of_tl {Cl : Type} (b : Block S Cl) (h1 : b.Leaves S.tl?)
    (h2 : b.Leaves fun s => s.rowsOwed) : LeavesFront b := by
  refine ⟨fun s rs gs s' h => ?_, fun s rs gs s' h => ?_, fun s rs gs s' h hw => ?_⟩
  · unfold keep
    rw [h1 s rs gs s' h]
  · unfold closedAt
    rw [h1 s rs gs s' h]
  · have e : s'.rowsOwed = s.rowsOwed := h2 s rs gs s' h
    unfold S.noneWaits at hw ⊢
    rw [e]
    exact hw

end VerifiableInference.Desc.First.K8.Ready

#print axioms VerifiableInference.Desc.First.K8.Ready.leavesFront_of_tl
