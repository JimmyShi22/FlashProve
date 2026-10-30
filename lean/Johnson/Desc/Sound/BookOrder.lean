-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/BookOrder.lean: **"THE BOOK IS IN ORDER": THE DEFINITIONS ALONE.** Four
definitions, two of them tests with code; no theorem; no Mathlib. Cut by a program out of
Johnson/Desc/Sound/BookInOrder.lean, to the letter but for "Nat" in the place of its sign, so that a
table, a walk or a layer can name the tests without the laws (and what lies beneath the laws).
  `BookOrd first B`: the tree at the place z of the book bears the number first + z.
  `bookOrdB`: the same as a test with code.
  `BookStep first B roots`: the book is in order AND the record counts as many roots as the book has
    trees. `bookStepB`: the same as a test with code.
That each test says what its sentence says (`bookOrd_iff`, `bookStep_iff`), who makes it and who
keeps it: BookInOrder.lean.
Limits: those of BookInOrder.lean. NO SOUNDNESS IS CLAIMED.

-/
import OnBytes.Iop.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes

/-- **The book is in order**: the tree at the place z bears the number first + z. -/
def BookOrd (first : Nat) (B : TreeBook) : Prop :=
  ∀ z T, B.trees[z]? = some T → T.number = first + z

/-- The same as a test with code. -/
def bookOrdB (first : Nat) (B : TreeBook) : Bool :=
  (List.range B.trees.size).all fun z => (B.trees[z]?).all fun T => T.number == first + z

/-- The book is in order, and the record counts as many roots as the book has trees. -/
def BookStep (first : Nat) (B : TreeBook) (roots : Nat) : Prop :=
  roots = B.trees.size ∧ BookOrd first B

def bookStepB (first : Nat) (B : TreeBook) (roots : Nat) : Bool :=
  roots == B.trees.size && bookOrdB first B

end VerifiableInference.Desc.Sound
