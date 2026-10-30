-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/BookTests.lean: FIVE TESTS WITH CODE ON A BOOK OF TREES. Definitions with code;
no theorem
(the laws: Johnson/Desc/Sound/BookTestsLaw.lean).

Each is the Bool of a condition that our laws on the term "words" ask of a chain's book, so that a
ride
can evaluate it at a real record, and a filling of a table's book-keeping can hold it as a clause.

  `bookFitsB B`: `BookFits B` (Johnson/Desc/Book/BookFits.lean): every place names a tree that is
  there and a part of it that is
    the message.
  `placedB B`: every place names a tree that is there.
  `tenantB o`: in the shared chain's end's book Omega, if it has a place, is part 0 of its tree.
  `numberedBookB ft B`: a tree's number is ft + its place in the book.
  `numberedLastB t₁ t₂ ft B`: the last chain's book (`NumberedLast`, SeamAt.lean).

Limits. Tests on plain data. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Third.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes
open VerifiableInference.Desc.Third (SharedOut)

def bookFitsB (B : TreeBook) : Bool :=
  (List.range B.place.size).all fun i =>
    match B.place[i]? with
    | some q =>
      (match B.trees[q.1]? with
       | some t => decide (t.parts[q.2]? = some i)
       | none => false)
    | none => true

def placedB (B : TreeBook) : Bool :=
  (List.range B.place.size).all fun i =>
    match B.place[i]? with
    | some q => decide (q.1 < B.trees.size)
    | none => true

def tenantB (o : SharedOut) : Bool :=
  match o.book.place[o.omega]? with
  | some q => q.2 == 0
  | none => true

def numberedBookB (ft : Nat) (B : TreeBook) : Bool :=
  (List.range B.trees.size).all fun j =>
    match B.trees[j]? with
    | some t => t.number == ft + j
    | none => true

def numberedLastB (t₁ t₂ ft : Nat) (B : TreeBook) : Bool :=
  decide (ft ≤ t₁ + 1) &&
    (List.range B.trees.size).all fun z =>
      match B.trees[z]? with
      | some T => if z + 1 = ft then decide (T.number < t₂) else T.number == z
      | none => true

end VerifiableInference.Desc.Sound
