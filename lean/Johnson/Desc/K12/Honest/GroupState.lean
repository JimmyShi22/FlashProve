-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/GroupState.lean: a group's trees as the list of trees that `stagesAll`
takes. `stagesAll` (Johnson/Desc/K12/Honest/Stages.lean) takes a list of trees (`Tree`: a depth and
a column function, which gives a list of words at each position). The theorem on what the first code
switch of a proximity test reads (`hy_group`, Johnson/Desc/K12/Honest/GroupReads.lean) is about
groups of dealt columns; a dealt column is a position with a list of words. This file defines the
list of the group's trees and proves that theorem's two hypotheses on the dealt columns, `hpos` and
`hcols`, at the groups that `groupsAt` (Stages.lean) makes from that list. One definition with code
and two theorems with their proofs, general in every parameter. It does not depend on the frame for
an honest side (Johnson/Desc/ProofFile/Honest/Frame.lean).

In the list: a group (`Gp`, OnBytes/Slice/KeyGroup.lean) is finitely many sent messages, its
members. The book (`TreeBook`, OnBytes/Iop/Ground.lean) lists the trees sent so far; a tree's place
is its index in that list. ts is a list of natural numbers. At `hy_group` it is `P.ts` (`GpData`,
OnBytes/Slice/BlkProxGp.lean): the places of the trees that the first switch opens, increasing under
`GpData.Pub`. `log t` and `c t` are used as the depth and the column function of the tree at the
place t, and `dAt t` (`PQ.RD`, Run/PlanQTypes.lean) as the data of the round that sent it. poss is
the list of the sampled positions. `groupsAt` makes one group for each tree: the pairs (x, `c t x`)
for x in `Fmt.listOf (poss.map (· % 2 ^ log t))` (Fmt/Rules6.lean): the sampled positions modulo
`2 ^ log t`, each once, increasing (`groupAt`, Johnson/Prover/Link/BodyAll.lean).

  `pos_groups`: if every position in poss is below `2 ^ a`, then for every ts, tree by tree, the
    positions of the group that `groupsAt (groupTrees ts log c) poss` makes for t are the tree's own
    list under the sampled positions, `(ownAt (log t) (Positions.ofDraws a poss)).toList` (`ownAt`,
    OnBytes/Slice/BlkProxMany.lean). That is `hpos` of `hy_group` at these groups
  `cols_groups`: if for each t in ts `PQ.posN (dAt t).tree` is `2 ^ log t` and `c t x` has the
    length `PQ.colW (dAt t).tree` at every x below `2 ^ log t`, then, tree by tree, each dealt
    column of the group for t is the column function's, at a position of the tree: its position x is
    below `PQ.posN (dAt t).tree`, `c t x` has that length, and its list of words is `c t x`. That is
    `hcols` of `hy_group` at these groups
  `groupTrees ts log c`: a definition: for each t in ts, in the order of ts, the pair of the depth
    `log t` and the column function `c t`

By what. Both theorems go by recursion on ts and by unfolding `groupsAt` and `groupAt`. `pos_groups`
rewrites by `ownAt_ofDraws` (Johnson/Desc/K12/Law/FirstRead.lean), which uses the bound on poss.
`cols_groups` uses `Fmt.listOf_mem` (Fmt/Rules6Laws.lean): whatever is in the list is one of the
sampled positions modulo `2 ^ log t`, and so below `2 ^ log t`.

Limits. `groupTrees` follows the order of ts, which at `hy_group` is the order of the trees in the
book. A caller's list of trees (the field of `TestJob` for the trees that the first round of
positions opens, Johnson/Desc/ProofFile/Honest/K12/Test.lean) follows the order of the declared
openings. That the two orders are the same is not shown here: it is left to the library's test `gpL`
(Johnson/Desc/K12/Law/FirstOk.lean), whose clauses opens.n, opens.key, opens.a and opens.W compare
the number of the declared openings and, in order, their keys, depths and widths with those of the
trees at the places `D.ts` of its plain data (`Plain`). `pos_groups` has the hypothesis that every
sampled position lies in the stage's range: is below `2 ^ a`. `cols_groups` has the hypothesis that
the data of the round that sent each tree state the tree's depth and the width of its columns.
Nothing here says that the column functions hold the members' symbols. Nothing on a decision, on
completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.GroupReads
import Johnson.Desc.K12.Honest.Stages

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb _root_.Run
open H2K.Sw H2K.JointK
open Johnson.Prover.Link (groupAt)

/-- The group's trees: for each t in ts, in the order of ts, the depth `log t` and the column
function `c t`. ts: the trees' places in the book. -/
def groupTrees (ts : List ℕ) (log : ℕ → ℕ) (c : ℕ → ℕ → List UInt64) : List Tree :=
  ts.map fun t => (log t, c t)

/-- **The dealt groups' positions are the trees' own lists** under the sampled positions. hr: every
sampled position is below `2 ^ a`. -/
theorem pos_groups (a : ℕ) (log : ℕ → ℕ) (c : ℕ → ℕ → List UInt64) (poss : List ℕ)
    (hr : ∀ x ∈ poss, x < 2 ^ a) : ∀ ts : List ℕ,
    List.Forall₂ (fun t (grp : List (ℕ × List UInt64)) => grp.map (·.1) =
      (ownAt (log t) (Positions.ofDraws a poss)).toList) ts (groupsAt (groupTrees ts log c) poss)
  | [] => List.Forall₂.nil
  | t :: ts => by
    refine List.Forall₂.cons ?_ (pos_groups a log c poss hr ts)
    rw [ownAt_ofDraws a (log t) poss hr]
    show ((Fmt.listOf (poss.map (· % 2 ^ log t))).map fun x => (x, c t x)).map (·.1) = _
    rw [List.map_map]
    exact List.map_id _

/-- **Each dealt column is the column function's, at a position of the tree.** The hypothesis: for
each tree the round's data `dAt t` state `2 ^ log t` positions, and the columns `c t x` have the
width that these data state. -/
theorem cols_groups (dAt : ℕ → PQ.RD) (log : ℕ → ℕ) (c : ℕ → ℕ → List UInt64) (poss : List ℕ) :
    ∀ ts : List ℕ, (∀ t ∈ ts, PQ.posN (dAt t).tree = 2 ^ log t ∧
      ∀ x, x < 2 ^ log t → (c t x).length = PQ.colW (dAt t).tree) →
    List.Forall₂ (fun t (grp : List (ℕ × List UInt64)) => ∀ x ∈ grp,
      x.1 < PQ.posN (dAt t).tree ∧ (c t x.1).length = PQ.colW (dAt t).tree ∧ x.2 = c t x.1) ts
      (groupsAt (groupTrees ts log c) poss)
  | [], _ => List.Forall₂.nil
  | t :: ts, h => by
    refine List.Forall₂.cons (fun x hx => ?_)
      (cols_groups dAt log c poss ts fun u hu => h u (List.mem_cons_of_mem _ hu))
    obtain ⟨h1, h2⟩ := h t (List.mem_cons_self ..)
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ _).1 hy)
    have hlt : z % 2 ^ log t < 2 ^ log t := Nat.mod_lt _ (Nat.two_pow_pos _)
    exact ⟨by rw [h1]; exact hlt, h2 _ hlt, rfl⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.pos_groups
#print axioms ProofFile.Honest.K12.cols_groups
#print axioms ProofFile.Honest.K12.groupTrees
