-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/FenceFit.lean: EVERY OPEN PIN's TENANT SITS IN A TREE THAT WAS SENT IN FRONT. One
test on the table of joints and its numbers, and what its yes says. Small; no Mathlib. A file BESIDE
the table: it turns nothing of it.

Why. The promise's clauses on committed words ("shown", "no collision") ride past a block because a
tree that was sent in front of the block passes it unturned (`wordStays`,
Johnson/Desc/Sound/StringsStay.lean: for trees whose number is below the block's base). That the
tenants of which the promise speaks at a border DO sit in such trees is a fact on the plan: no
kind's. It is asked here once, as a test that runs.

What is said. `fenceFit`: A TEST: at every border, each tenant of an open pin with a sample
(`sampledIn`) has a tree's number below `Numbers.treesAt` at that border's place. `fenceFit_at`:
what its yes says.

Limits. (1) It holds the tenants against the letter `treesAt`; that this is the number of roots that
the blocks in front tell is `bookFit` (Johnson/Desc/First/BookFit.lean); that a piece's base is that
number is the pieces' make. (2) Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

/-- A TEST ON THE TABLE AND ITS NUMBERS: at every border, the chain's end among them, every tenant
of an open pin with a sample sits in a tree that the blocks in front have sent. -/
def fenceFit (N : Numbers) (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range (ps.length + 1)).all fun k =>
    (sampledIn N ((openSets links ps (start links))[k]?.getD [])).all fun x =>
      decide (x.1 < N.treesAt ps[k]?)

theorem fenceFit_at (N : Numbers) (links : List ModelPart) (ps : List Place)
    (h : fenceFit N links ps = true) (k : Nat) (hk : k ≤ ps.length) (x : Nat × Nat)
    (hx : x ∈ sampledIn N ((openSets links ps (start links))[k]?.getD [])) :
    x.1 < N.treesAt ps[k]? := by
  have h' := List.all_eq_true.1 h k (List.mem_range.2 (Nat.lt_succ_of_le hk))
  exact of_decide_eq_true (List.all_eq_true.1 h' x hx)

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.fenceFit_at
