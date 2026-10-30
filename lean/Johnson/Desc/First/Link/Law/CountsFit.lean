-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/CountsFit.lean: THE PLAN's TWO COUNTS (how many commitment trees, how
many oracle messages, the blocks in front of a place have sent) ARE THE SAME AT TWO NEIGHBOURING
PLACES, PAST A BLOCK THAT TELLS NO ORACLE: from the yes of the table's own test on these numbers
(`bookFit`, Johnson/Desc/First/BookFit.lean). A theorem, and three blocks that tell none.

Why. The laws on a link's last blocks took the two equations as premises on the plan's numbers. They
follow from one Bool on the numbers and from what the block declares.

What is said.
  `counts_step`: **under `bookFit N ps told`, at a number k of the list whose block tells nothing:
    `N.treesAt ps[k + 1]? = N.treesAt ps[k]?`, and the like for the messages.** `behind_tells`,
    `equation_tells`, `shut_tells`: the frame's block behind the batching, the one equation's block
    and the shutting declare no oracle.

Limits. That `told` is what the description's blocks tell, and that the seated blocks declare what
the kinds' own texts declare, are other files'. The batching's block is a letter of the link: that
it tells nothing is not said here. Nothing on soundness.

-/
import Johnson.Desc.First.BookFit
import Johnson.Desc.First.Batch.Place
import Johnson.Desc.LinkLaw2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.First (S Numbers bookFit bookFit_at told_succ_nil)

/-- **The plan's two counts past a block that tells nothing.** -/
theorem counts_step (N : Numbers) (ps : List Place) (told : List (List Oracle))
    (hf : bookFit N ps told = true) (k : Nat) (hk : k < ps.length) (hn : told[k]? = some []) :
    N.treesAt ps[k + 1]? = N.treesAt ps[k]? ∧ N.msgsAt ps[k + 1]? = N.msgsAt ps[k]? := by
  have a := bookFit_at N ps told hf k (Nat.le_of_lt hk)
  have b := bookFit_at N ps told hf (k + 1) hk
  have c := told_succ_nil told k hn
  exact ⟨by rw [b.1, a.1, c.1], by rw [b.2, a.2, c.2]⟩

/-- The frame's block behind the batching declares no oracle. -/
theorem behind_tells {T Cl : Type} (L : Link T Cl) : L.behindB.oracles = [] := rfl

/-- The one equation's block declares no oracle. -/
theorem equation_tells {T Cl : Type} (X : K9.Lens T) (pw : K9.Where) :
    (K9.oneEquation (Cl := Cl) X pw).oracles = [] := rfl

/-- The shutting declares no oracle. -/
theorem shut_tells {Cl : Type} (pw : K9.Where) (piece : Nat) :
    (K9.shut (Cl := Cl) pw piece).oracles = [] := rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.counts_step
#print axioms VerifiableInference.Desc.LinkJoin.behind_tells
#print axioms VerifiableInference.Desc.LinkJoin.equation_tells
#print axioms VerifiableInference.Desc.LinkJoin.shut_tells
