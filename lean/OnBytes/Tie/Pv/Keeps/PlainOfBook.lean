-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/PlainOfBook.lean: no opening in the rounds that the dry run of one of a file's
three chains' blocks returns bears the mark "stored".

A definition, statements and proofs: corollaries of OnBytes/Tie/Pv/Keeps/BookBlocks.lean. An opening
of a dry run's list is the note of a tree of the book, and such a note has the mark "stored" off, by
the definition of the note. The same fact is shown by a walk of its own through the routines in
OnBytes/Flat/Plain/ [not in this library].
Main names:
  `PlainRounds R`: no opening of R bears the mark "stored".
  `plain_of_opens`: of a list whose openings are notes of a book's trees.
  `plain_oneTime`, `plain_shared`, `plain_second`: a key file's first chain, the shared chain, the
    second chain, at every start. `plain_first`: a proof file's first chain, if the block of the
    links has `Book.BookB`.
Limits: one direction: from a dry run that returns.
-/
import OnBytes.Tie.Pv.Keeps.BookBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Keeps.Plain

open OnBytes OnBytes.Model

/-- No opening bears the mark "stored". -/
def PlainRounds (R : Params.Rounds) : Prop := ∀ r ∈ R, ∀ o ∈ r.1.opens, o.1.stored = false

/-- A note of a tree of the book has the mark "stored" off. -/
theorem plain_of_opens {R : Params.Rounds} {B : TreeBook} (o : Book.OpensIn R B) :
    PlainRounds R := fun r hr x hx => by
  obtain ⟨t, _, rfl⟩ := o r hr x hx
  rfl

/-- A key file's first chain's block. -/
theorem plain_oneTime (p : Params.OneTime) (s : Start) (R : Params.Rounds) (e : Proof.FirstEnd)
    (h : (Key.oneTime p).dryRun s = some (R, e)) : PlainRounds R :=
  plain_of_opens (Book.oneTime_opens h).2

/-- A shared chain's block. -/
theorem plain_shared (S : Params.LinShape) (key : TableKey) (s : Start) (R : Params.Rounds)
    (e : Proof.SharedEnd) (h : (Proof.sharedBlock S key).dryRun s = some (R, e)) : PlainRounds R :=
  plain_of_opens (Book.shared_opens h).2

/-- A second chain's block. -/
theorem plain_second (S : Params.LinShape) (first : LinFirst) (sh : Proof.SharedEnd) (s : Start)
    (R : Params.Rounds) (h : (Proof.secondBlock S first sh).rounds s = some R) : PlainRounds R := by
  obtain ⟨_, _, o⟩ := Book.second_opens h
  exact plain_of_opens o

/-- A proof file's first chain's block. -/
theorem plain_first (p : Params.First) (links : Blk Proof.LinksResult) (reply : E)
    (hl : Book.BookB links) (s : Start) (R : Params.Rounds) (e : Proof.FirstEnd)
    (h : (Proof.firstBlock p links reply).dryRun s = some (R, e)) : PlainRounds R :=
  plain_of_opens (Book.first_opens hl h).2

end OnBytes.Tie.Pv.Keeps.Plain

#print axioms OnBytes.Tie.Pv.Keeps.Plain.plain_oneTime
#print axioms OnBytes.Tie.Pv.Keeps.Plain.plain_shared
#print axioms OnBytes.Tie.Pv.Keeps.Plain.plain_second
#print axioms OnBytes.Tie.Pv.Keeps.Plain.plain_first
