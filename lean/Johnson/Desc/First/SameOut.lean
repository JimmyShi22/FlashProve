-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/SameOut.lean: WHAT RIDES PAST A BLOCK OF THE FIRST CHAIN, THE STATEMENT's SIDE: a
relation on two carried records ("all but the open link's own part is the same") and a sentence on a
sentence of the table of joints' meaning ("it reads nothing else"). Two definitions and three small
facts. It names no kind. Over Johnson/Desc/First/State.lean and Johnson/Top/H0/Walk/Stays.lean
(which stands over Johnson/Desc/Msg.lean) alone: WITHOUT MATHLIB. NO RESULT ON THE PROTOCOL.

Why. Where a block's extractor is the identity, an item that rides past the block is owed at ONE
witness: it is to say of the statement in front what it says of the statement behind. Many blocks
turn the open link's own part of the record and nothing else, and send trees from their base on and
none below. An item whose sentence reads neither rides past all of them: so that is asked ONCE of
the sentence, not at each block.

OBJECT: no text that runs: the carried record First.S and the strings Strs.
USER: Johnson/Desc/Sound/RidesSide.lean.
LETTERS: all free.
Compiled with the whole library.

Main names:
  `SameOut s s'`: NINE EQUATIONS: the record's eight fields but "here" are the same (st, book,
    roots, rowsOwed, failed, check, out, req), and so is the open link's context (link?).
  `SameOut.refl`, `SameOut.symm`, `SameOut.trans`.
  THE STRINGS' HALF IS ANOTHER FILE's: `Stays base y y'` (Johnson/Top/H0/Walk/Stays.lean): the
    stored table's cells are the same, and every tree below base. (The like on a frame's own
    strings: SameBelow, Johnson/Desc/First/Att/K05SeamOut.lean.)
  `ReadsOut base φ`: φ, a sentence on (what was handed to the chain, the record), the strings and a
    witness, reads of the record nothing that SameOut leaves free, and of the strings nothing that
    Stays base leaves free. ONE WAY: from (s', y') to (s, y).

Limits. "THE STRINGS ARE THE SAME" WOULD BE FALSE AS AN EQUATION behind a block that sends nothing:
a tree at or above the block's base does not stay (Johnson/Desc/Sound/StageCut.lean: sCol_eq).
ReadsOut is sufficient for riding, not necessary. A sentence that reads the open link's own part
(the ledger, what was heard) is not ReadsOut.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.State
import Johnson.Top.H0.Walk.Stays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Stays)

/-- **All but the open link's own part is the same.** -/
structure SameOut (s s' : S) : Prop where
  st : s'.st = s.st
  book : s'.book = s.book
  roots : s'.roots = s.roots
  rowsOwed : s'.rowsOwed = s.rowsOwed
  failed : s'.failed = s.failed
  check : s'.check = s.check
  out : s'.out = s.out
  req : s'.req = s.req
  link : s'.link? = s.link?

theorem SameOut.refl (s : S) : SameOut s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameOut.symm {s s' : S} (h : SameOut s s') : SameOut s' s :=
  ⟨h.st.symm, h.book.symm, h.roots.symm, h.rowsOwed.symm, h.failed.symm, h.check.symm, h.out.symm,
    h.req.symm, h.link.symm⟩

theorem SameOut.trans {s s' s'' : S} (h : SameOut s s') (k : SameOut s' s'') : SameOut s s'' :=
  ⟨k.st.trans h.st, k.book.trans h.book, k.roots.trans h.roots, k.rowsOwed.trans h.rowsOwed,
    k.failed.trans h.failed, k.check.trans h.check, k.out.trans h.out, k.req.trans h.req,
    k.link.trans h.link⟩

/-! ## The sentence -/

/-- **The sentence reads of the carried record nothing of the open link's own part but its context,
and of the strings the stored table and the trees below base.** One way. -/
def ReadsOut {P W : Type} (base : Nat) (φ : P × S → Strs → W → Prop) : Prop :=
  ∀ (z : P) (s s' : S) (y y' : Strs) (w : W), SameOut s s' → Stays base y y' →
    φ (z, s') y' w → φ (z, s) y w

end VerifiableInference.Desc.First
