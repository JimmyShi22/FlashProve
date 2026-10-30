-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartJ.lean: the one type of entries for all blocks of a segment, and how a tuple (message
of the encoded index, messages) is read on it.

Two definitions and two equations by definition. Glue for the files Cb/Part/LdPart*.lean; nothing of
a write-up of ours (lean/CREDITS.md) is rendered here.

Why: every block of a front has a type of entries
of its own with a reading of the tuples. A request that is built from a partition takes one type for
the lookup and all sumchecks of a segment, so that readings grow along the list of blocks as sets of
names, and so that the front's maps and the body's packed matrix read the same entries.

Main names:
  `LdPartJ I S`: (entries of the index's matrix) ⊕ (entries of the open messages):
    (I.Rw × (Fin I.k → Bool)) ⊕ S.Ent.
  `ldPartMsg I S um`: the reading: the matrix of the index's message on the left, the messages'
    entries on the right.

Limits: this file does not say that a block's own masks and the packed cells are entries of
messages, names on the right: no clause here enforces it. That a reading of cells or of the index
matrix (`LdPartRd`, Cb/Part/LdPart.lean) reads its own side alone is the matter of the files that
fill it (Cb/Part/LdPartCells.lean).

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Req1.LdSegRefAll

set_option autoImplicit false

namespace Cb

/-- the one type of entries -/
abbrev LdPartJ {E : Type} [Field E] (I : LdRefIx E) (S : Sig E) : Type :=
  (I.Rw × (Fin I.k → Bool)) ⊕ S.Ent

/-- the one reading of tuples -/
def ldPartMsg {E : Type} [Field E] (I : LdRefIx E) (S : Sig E) (um : I.C.Msg × S.Msg) :
    LdPartJ I S → E :=
  Sum.elim (I.mat um.1) (S.ents um.2)

theorem ldPartMsg_inl {E : Type} [Field E] (I : LdRefIx E) (S : Sig E)
    (um : I.C.Msg × S.Msg) (n : I.Rw × (Fin I.k → Bool)) :
    ldPartMsg I S um (.inl n) = I.mat um.1 n := rfl

theorem ldPartMsg_inr {E : Type} [Field E] (I : LdRefIx E) (S : Sig E)
    (um : I.C.Msg × S.Msg) (n : S.Ent) :
    ldPartMsg I S um (.inr n) = S.ents um.2 n := rfl

end Cb
