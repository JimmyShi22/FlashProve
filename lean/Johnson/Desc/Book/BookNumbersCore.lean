-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Book/BookNumbersCore.lean: "A TREE's NUMBER IS ITS PLACE" IS KEPT ALONG A CHAIN THAT
RECEIVES ALL ITS TREES: Numbered ft (Johnson/Desc/Book/BookNumbers.lean) as a member of the plain
ground's frame CoreRecv ft (Johnson/Desc/CoreKeeps.lean): a relation on the three that the
ground writes (statement, book of trees, count of roots) which the eight functions that write the
statement alone keep, and the receiving AT ft. Definitions, statements and proofs.
  NumberedC ft T  Numbered, said of the three.
  numbered_iff    Numbered ft d is NumberedC ft (coreOf d).
  coreRecv_numbered : CoreRecv ft (NumberedC in front gives NumberedC behind): the eight by the
                  frame's coreStill_same; the receiving by recvP_numbered.
What is not said. That a chain's blocks are made of these nine functions alone: the frame's own
files say it of K1 and K13. The taking over is no member (adopt_breaks). Nothing on soundness or on
hiding.
-/
import Johnson.Desc.CoreKeeps
import Johnson.Desc.Book.BookNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Book
open OnBytes Desc.Plain
open VerifiableInference.Desc.Ground (Core coreOf CoreStill CoreRecv coreStill_same)

/-- Numbered, said of the three. -/
def NumberedC (ft : Nat) (T : Core) : Prop :=
  T.roots = T.book.trees.size ∧
    ∀ (j : Nat) (t : Tree), T.book.trees[j]? = some t → t.number = ft + j ∧ t.src = .own j

theorem numbered_iff {L : Type} (ft : Nat) (d : DState L) :
    Numbered ft d ↔ NumberedC ft (coreOf d) := Iff.rfl

/-- Where book and roots are as they were it stays. -/
theorem numberedC_same (ft : Nat) (a b : Core) (h : b.book = a.book ∧ b.roots = a.roots)
    (hN : NumberedC ft a) : NumberedC ft b := by
  unfold NumberedC
  rw [h.1, h.2]
  exact hN

/-- **Along a chain that receives all its trees at ft, a tree's number stays its place.** -/
theorem coreRecv_numbered (ft : Nat) :
    CoreRecv ft fun a b => NumberedC ft a → NumberedC ft b where
  refl := fun _ => id
  trans := fun h k a => k (h a)
  newGroup := fun d d' c m n h => numberedC_same ft _ _ (coreStill_same.newGroup d d' c m n h)
  admit := fun d d' o r h => numberedC_same ft _ _ (coreStill_same.admit d d' o r h)
  join := fun d d' g o k h => numberedC_same ft _ _ (coreStill_same.join d d' g o k h)
  addRow := fun d d' g r h => numberedC_same ft _ _ (coreStill_same.addRow d d' g r h)
  takeMask := fun d d' o n h => numberedC_same ft _ _ (coreStill_same.takeMask d d' o n h)
  closeLedger := fun d d' o h => numberedC_same ft _ _ (coreStill_same.closeLedger d d' o h)
  spendAsMask := fun d d' o h => numberedC_same ft _ _ (coreStill_same.spendAsMask d d' o h)
  elsewhere := fun d d' m o t h => numberedC_same ft _ _ (coreStill_same.elsewhere d d' m o t h)
  recv := fun d d' sent ids h hN => recvP_numbered ft d d' sent ids h hN

end VerifiableInference.Desc.Book
