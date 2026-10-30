-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/Whole.lean: THE STEP BEHIND THE SENDING OF A CODE SWITCH RETURNS
(`switchBehind`, Johnson/Top/H0/Tw/K2/Switch.lean), WITH NO PREMISE LEFT IN THE FORM «… = .ok …»:
the law on the reading of the old rows (Returns/Read.lean) laid into the law on the step
(Returns/BehindAt.lean). One statement with its proof.

  `switchBehind_returns_whole`   PREMISES, all on what the step is handed: the old main code is in
                    the list · the text's conditions on the round "LOC" (`locOk`) · `ReadFits` at
                    the positions drawn · `FrontFits`. IT RETURNS: the statement `joinedAt` with the
                    made rows appended to the group's open rows; the book `bookAfter`; the columns
                    `leftAfter`. THE SYMBOLS y OF WHICH THE ROWS ARE MADE ARE THOSE THAT THE READING
                    GIVES: the conclusion holds that equation, and their count

Where the premises can be met. One input at which all of them hold together is typed:
Returns/MemberWhole.lean.

Limits. SOME PREMISES ARE BOOLS ON PUBLIC DATA, TAKEN WHOLE. Of the step's own text: `locOk`; the
test on the target (`FrontFits.check`); `readsMainOf` (`FrontFits.reads`); in `AllOpen`, tree by
tree, `leafOk` and `colsStand`. Of the library: `lengthsOk`; `formFits` at the claim's forms, and
`InOrder` at the stored sample rows' tensors (`TablesFit`). "No premise says that a routine returns"
means: none has the form "… = .ok …" or "… = some …" of a routine of the step. The symbols are no
term here: they are what `readOld` gives. Who must leave which premise: Returns/BehindAt.lean's
head. The law speaks of the bare step: where a block is seated, a run returns only if it also
leaves the reply as it was: not stated here. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.BehindAt
import Johnson.Desc.K2.Honest.Returns.Read

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Slice (withRows)
open _root_.Tw.K2 (SwIn switchBehind readOld)
open VerifiableInference.Desc.First.K2 (locOk outOf)

/-- **The step behind the sending returns**: no premise says that a routine returns. -/
theorem switchBehind_returns_whole (i : SwIn) (c : Code) (G : Group)
    (hCode : i.st.codes.base[i.old.code]? = some c) (hLoc : locOk i c.logN = true)
    (R : ReadFits i (Positions.ofDraws c.logN i.drawn.poss)) (F : FrontFits i c G) :
    ∃ y rows,
      readOld i (Positions.ofDraws c.logN i.drawn.poss) = .ok (bookAfter (treesOf i) i.book,
        leftAfter (Positions.ofDraws c.logN i.drawn.poss) i.book (treesOf i) i.opened, y) ∧
      y.size = (Positions.ofDraws c.logN i.drawn.poss).all.size * i.old.rows ∧
      Own.swRows (joinedAt i G) i.old i.T (i.ids.getD 0 noId)
        (i.ids.extract 1 (1 + i.T.kept.size)) (Positions.ofDraws c.logN i.drawn.poss) y =
        some rows ∧
      switchBehind i = .ok ⟨withRows (joinedAt i G) i.grp rows, bookAfter (treesOf i) i.book,
        leftAfter (Positions.ofDraws c.logN i.drawn.poss) i.book (treesOf i) i.opened,
        outOf i (Positions.ofDraws c.logN i.drawn.poss)⟩ := by
  obtain ⟨y, hRead, hsize⟩ := readOld_returns i _ R (ofDraws_all _ _)
  obtain ⟨S3, _, rows, rfl, _, _, _, _, _, _, _, h1, h2⟩ :=
    switchBehind_returns_at i c _ _ y G hCode hLoc hRead hsize F
  exact ⟨y, rows, hRead, hsize, h1, h2⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.switchBehind_returns_whole
