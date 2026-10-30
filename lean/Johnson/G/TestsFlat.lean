-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/TestsFlat.lean: the shape of a chain's tree by its number, read off the list of all trees
that the chain's rounds send.

`OnBytes.Maker.treeShT ds n` walks along the rounds until it meets the tree number n. Where a test
asks for many trees of a long chain, Lean's kernel walks anew each time. With the list of the
chain's trees written out, and one evaluation that shows it to be the computed one, each later
question is a look into a short list. A proof.
Main names:
  `treeSh_flat : treeShT ds n = (ds.flatMap (·.trees))[n]?`.
Limits: general; no value is treated. Nothing on soundness.

-/
import OnBytes.Maker.Trees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes.Maker

theorem treeSh_flat (ds : List RDT) : ∀ n, treeShT ds n = (ds.flatMap (·.trees))[n]? := by
  induction ds with
  | nil => intro n; rfl
  | cons d ds ih =>
    intro n
    show (if n < d.trees.length then d.trees[n]? else treeShT ds (n - d.trees.length)) = _
    rw [List.flatMap_cons, List.getElem?_append, ih]

end Johnson.G

#print axioms Johnson.G.treeSh_flat
