-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/BudRun.lean: the letter `bud` of Sim/ExactPlan.lean
(`budOpened`) at the positions that a session of the frame asks of a part. A session hands a part's
simulator, round by round and root by root, what is read in the whole run of the trees that the part
sends (`asksFrom`, Johnson/Desc/ProofFile/Honest/Law/Rule/Session.lean: tree: the positions read of
a tree, by its number in the chain; n: how many trees the chain has sent in front). Here that list
is written out at one round and its first root; so `budOpened` at it comes down to one clause, tree
by tree. That clause is a hypothesis. General in the list of stages, the challenges ds, the function
tree, the rounds' numbers of roots and the number n. Sim/BudOwn.lean calls `bud_of_asksFrom`.
Statements and proofs. No property is claimed.

Terms. Sim/ is this file's folder. The frame is Johnson/Desc/ProofFile/Honest/Frame.lean, with
Side.lean next to it. A letter is a free parameter. A part (`Part`, Frame.lean) is the prover's side
of a stretch of a sub-protocol's rounds; its simulator is the term of type `Sim` (Frame.lean) that
is paired with it, and such a term need not simulate anything. `bud` is a parameter of the frame's
structure `Good` (Side.lean): for each part, by its number, which positions may be read at given
challenges. `budOpened stages n ds asks` is written for that parameter. At n = 1, the number of a
proximity test's second part (`restMember`, Sim/Row.lean), it says: every position that asks has at
a round's root number 0 is in the list `openedTr` (Sim/CoreText.lean) at that round: the positions
that the next reading round samples. At every other n it asks nothing. A tree is a table that a
round sends as an oracle message; a round has one root for each of these, and a chain's trees are
numbered from 0. A session is the function `session` of Session.lean; it builds a part's list of
positions by `asksFrom` (in `cutRow`), with `treeAsks` (Bare.lean, next to Session.lean) for tree.
In "Limits", the test is the proximity test, and the file's whole plan is the description of all the
rounds of the three chains (`FileDescription`).

  `bud_of_asksFrom`: `budOpened stages 1 ds (asksFrom tree roots n)`, under one hypothesis, h: for
    every round i of the part that has a root: all that is read of the tree that it sends lies among
    the positions that the next reading round samples. In Lean: where `roots.getD i 0` is positive,
    every q in `tree (n + (roots.take i).sum)` is in `openedTr` at the challenges
    `laterOf stages ds` (Sim/ExactPlan.lean) and at the number
    `1 + ((sgOf s).h + (sgOf s).g) + i` in that function's own count of rounds, where s is the first
    stage (`stages.headD default`)
  `asksFrom_at`: what `asksFrom tree rs n` has at round number i, root number 0: what is read of the
    tree whose number is n and the roots of the rounds before i, added up; the empty list where the
    round has no root or there is no such round

By what. `asksFrom_at`: by recursion on the list rs, unfolding `asksFrom` (Session.lean).
`bud_of_asksFrom`: by `asksFrom_at`, after unfolding `budOpened` (Sim/ExactPlan.lean).

Limits.
- The clause is a hypothesis. It speaks of all that is read of the tree in the whole run, by
  whichever round of whichever chain: that no round outside the test reads a tree that the test's
  second part sends is a matter of the file's whole plan, and is shown nowhere; that the test's own
  rounds read it at the next reading round's positions alone is not shown here either.
- Neither statement names a session, a part or `treeAsks`: tree, roots and n are free parameters.
  That a session builds a part's list in this form is by reading `cutRow` and `theActs`
  (Session.lean); it is not stated here.
- Of each round only root number 0 is bound, as in `budOpened`.
- No member is given by name. Here a member is a choice of tree, roots and n at which h is proved.
- Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactPlan
import Johnson.Desc.ProofFile.Honest.Law.Rule.Session

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)

/-- What `asksFrom tree rs n` has at round number i, root number 0: `tree` at the number n and the
roots of the rounds before i, added up; the empty list where round i has no root or rs has no entry
number i. -/
theorem asksFrom_at (tree : ℕ → List ℕ) : ∀ (rs : List ℕ) (n i : ℕ),
    ((((asksFrom tree rs n)[i]?).getD [])[0]?).getD [] =
      if 0 < rs.getD i 0 then tree (n + (rs.take i).sum) else []
  | [], n, i => by simp [asksFrom]
  | r :: rs, n, 0 => by
    cases r with
    | zero => simp [asksFrom]
    | succ r => simp [asksFrom, List.range_succ_eq_map]
  | r :: rs, n, i + 1 => by
    have ih := asksFrom_at tree rs (n + r) i
    simp only [asksFrom, List.getElem?_cons_succ, List.getD_cons_succ, List.take_succ_cons,
      List.sum_cons]
    rw [ih, Nat.add_assoc]

/-- **`budOpened` at the positions that a session asks of the second part.** roots: each round's
number of roots. Under the hypothesis h: at every round i that has a root, each position that `tree`
lists for the round's first tree is in `openedTr` at that round. tree, roots and n are free
parameters: no session is named. -/
theorem bud_of_asksFrom (stages : List Fmt.M1.Stage) (ds : List Fmt.Drawn) (tree : ℕ → List ℕ)
    (roots : List ℕ) (n : ℕ)
    (h : ∀ i, 0 < roots.getD i 0 → ∀ q ∈ tree (n + (roots.take i).sum),
      q ∈ openedTr (laterOf stages ds) (stages.drop 1) (stages.headD default) 1
        (1 + ((sgOf (stages.headD default)).h + (sgOf (stages.headD default)).g) + i)) :
    budOpened stages 1 ds (asksFrom tree roots n) := by
  intro _ i q hq
  rw [asksFrom_at] at hq
  by_cases hr : 0 < roots.getD i 0
  · rw [if_pos hr] at hq
    exact h i hr q hq
  · rw [if_neg hr] at hq
    cases hq

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.asksFrom_at
#print axioms ProofFile.Honest.K12.bud_of_asksFrom
