-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/FillRowFirst.lean: THE LAYER `fillRow` (FillRow.lean, beside this file)
AT THE READER THAT THE TABLE's FILES CHOOSE: `wordsFirst arr s.st s.book w`
(Johnson/Desc/Sound/WordsAt.lean): the table's one accessor, by seat, behind the state's book's
place. AT THE SMALL DOOR THE LAYER ASKS NOTHING. Definitions, and statements that hold by the make.
A file BESIDE the table of joints: it turns nothing of it.

  `wordsAtFirst arr`: the reader as the layer takes it: of the verifier's state it reads the
    statement and the book; of the strings nothing.
  `rowMore`: THE LAYER's ASKS AT THE DOOR: NONE. (The name stays, for whoever merges the layers'
    asks by name.)
  `fillRowFirst arr N Mg`: the layer: `row` is `rowSays N (wordsAtFirst arr)`; `more` is what was
    there merged with `rowMore`; every other letter as it was. `fillRowFirst_row`, `_more`: what it
    lays; `_pub`, `_pubP`, `_inOrder`, `_decodes`, `_pin`, `_carry`: six that it leaves.
Limits. (1) WHAT CLOSES THE READER's THREE SEAMS (Johnson/Desc/Sound/WordsAtPlan.lean:
below the number of the statement's messages the reader reads the witness's table at the plan's
shape and the book's place) IS NO ITEM OF THE DOOR: the three facts (the book in order; the
seats carried; the messages' shapes) are not on the table's list of extra public tests;
whoever spends them takes them from the structure of facts along the fold,
at a reached state. Nothing here does. (2) Nothing is proved of the reader here: that it gives the
same words at the messages in front across a sub-protocol (the premise hw of FillRow.lean's
`rowSays_back`) is `words_older` and its like, a number at a time. FillRow.lean's
limits stand, but for its first. Nothing on soundness.



-/
import Johnson.Desc.First.Close.Law.FillRow
import Johnson.Desc.Sound.WordsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

open OnBytes.Means (Words)
open OnBytes.Slice (GE)
open OnBytes.Maker Fo.Peel Cb Johnson.Pack
open VerifiableInference.Desc.Sound (wordsFirst MsgT)

variable {P Cells Tok : Type}

/-- The ruled reader, as the layer takes it. -/
noncomputable def wordsAtFirst (arr : ℕ → ℕ → ℕ) :
    P × S → Strs → Wit Cells Tok MsgT → Words GE :=
  fun a _ w => wordsFirst arr a.2.st a.2.book w

/-- **The layer's asks at the door: none.** -/
def rowMore : More where
  rows := fun _ _ => {}
  start := []

/-- **The layer, at the ruled reader.** -/
noncomputable def fillRowFirst (arr : ℕ → ℕ → ℕ) (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) : Meaning P (Wit Cells Tok MsgT) :=
  { fillRow N (wordsAtFirst arr) Mg with more := Mg.more.merge rowMore }

section
variable (arr : ℕ → ℕ → ℕ) (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT))

theorem fillRowFirst_row : (fillRowFirst arr N Mg).row = rowSays N (wordsAtFirst arr) := rfl
theorem fillRowFirst_more : (fillRowFirst arr N Mg).more = Mg.more.merge rowMore := rfl
theorem fillRowFirst_pub : (fillRowFirst arr N Mg).pub = Mg.pub := rfl
theorem fillRowFirst_pubP : (fillRowFirst arr N Mg).pubP = Mg.pubP := rfl
theorem fillRowFirst_inOrder : (fillRowFirst arr N Mg).inOrder = Mg.inOrder := rfl
theorem fillRowFirst_decodes : (fillRowFirst arr N Mg).decodes = Mg.decodes := rfl
theorem fillRowFirst_pin : (fillRowFirst arr N Mg).pin = Mg.pin := rfl
theorem fillRowFirst_carry : (fillRowFirst arr N Mg).carry = Mg.carry := rfl

end

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.fillRowFirst_row
#print axioms VerifiableInference.Desc.First.fillRowFirst_more
