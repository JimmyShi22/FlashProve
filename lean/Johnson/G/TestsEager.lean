-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/TestsEager.lean: twins of two functions that the makers' tests on a file's data read, in
which the carried number is evaluated at each step (Johnson/G/Eager.lean), so that Lean's kernel can
evaluate the tests at a long chain.

Definitions and proofs.
Main names:
  `sum_eq_sumE : l.sum = sumE 0 l`: for `OnBytes.Maker.WholeD.t₁` and `t₂`, which are sums over a
    chain's rounds.
  `treeShE`, `treeShE_eq : treeShT ds n = treeShE ds n`: the shape of a chain's tree number n.
Limits: general; no value is treated. Nothing on soundness.

-/
import Johnson.G.Eager
import OnBytes.Maker.Trees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes.Maker

theorem sum_eq_sumE (l : List Nat) : l.sum = sumE 0 l := by
  rw [sumE_eq]
  omega

/-- The shape of the chain's tree number n; the number is evaluated at each round. -/
def treeShE : List RDT → Nat → Option Fmt.Shape
  | [], _ => none
  | d :: ds, n =>
    if n < d.trees.length then d.trees[n]? else force (n - d.trees.length) fun v => treeShE ds v

theorem treeShE_eq (ds : List RDT) : ∀ n, treeShT ds n = treeShE ds n := by
  induction ds with
  | nil => intro n; rfl
  | cons d ds ih =>
    intro n
    show (if n < d.trees.length then d.trees[n]? else treeShT ds (n - d.trees.length)) = _
    simp only [treeShE, force_eq, ih]

end Johnson.G

#print axioms Johnson.G.sum_eq_sumE
#print axioms Johnson.G.treeShE_eq
