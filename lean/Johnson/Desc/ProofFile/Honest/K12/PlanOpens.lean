-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PlanOpens.lean: the groups of columns that declared rounds read,
written as a map over one list of the rounds' declared openings, for rounds that open no stored
tree. The groups are `colGroups` (Johnson/Desc/ProofFile/Honest/Small/ColGroups.lean), which is
defined round by round. By `regroup_cols` (same file) `colGroups` is the list of columns that the
frame (Johnson/Desc/ProofFile/Honest/Frame.lean) builds for declared rounds, cut into groups,
wherever the frame's `fillCols` returns with the empty list as its second argument. Here there is
one list of openings, each a triple (round, depth, source), and the group of each is written with
`groupAt` (Johnson/Prover/Link/BodyAll.lean), the function with which the term of a proximity test's
stages (`stagesAll`, Johnson/Desc/K12/Honest/Stages.lean) writes a group. `gs_stages`
(TermOpens.lean in this folder) writes that term's groups in the same form, and `cols_term`
(ColsTerm.lean in this folder) calls `colGroups_opens`. General in the declared rounds: the theorem
holds at every list of rounds and at all values of its other parameters. Two definitions and one
theorem.

In the list: a declared round (`Fmt.DeclaredRound`, Decl/Declared.lean) lists the stored trees that it
opens (its field `stored`) and the other trees that it opens (its field `opens`), each of the latter
as a shape (`Fmt.Shape`, Fmt/Plan.lean; its field `a` is the tree's depth) and a source. A source
(`Fmt.TreeSource`, Decl/Declared.lean) names the tree: `own n`, or `taken chain sent`. A challenge
(`Fmt.Drawn`, Fmt/Rules6Round.lean) is what a round draws; its field `poss` has the drawn positions.
The parameter `tree` returns for a source a place (`Place`, Johnson/Desc/Block.lean; not read here)
and a table (`Table`, the frame), or `none`. `groupAt a poss col` lists a position x with `col x`,
over the set of the positions poss modulo 2 ^ a, in increasing order.

  `colGroups_opens`: under the three hypotheses below, `colGroups stored tree decls Rs` is the list
    `planOpens decls i`, in order, with each opening (round, depth, source) replaced by its group:
    `groupAt` at the depth, at the positions of the challenge that D has at the round's number, and
    at the column `colAt tree` of the source
  `planOpens decls i`: a definition: the declared openings of the rounds decls, round by round,
    within a round in the order of its field `opens`: for each the triple (the round's number, the
    depth, the source). The first round has the number i, the next i + 1, and so on
  `colAt tree σ x`: a definition: the column at position x (`Table.col`, the frame) of the table
    that `tree σ` returns; the empty list where `tree σ` is `none`

By what. Recursion on the two lists. `colGroups` and `planOpens` are unfolded by one round; with the
round's field `stored` empty, its groups are those of its field `opens`, and these are `groupAt` at
`colAt` by unfolding (`rfl`). No lemma of another file of the library is called.

Hypotheses of `colGroups_opens`. (1) No round of decls opens a stored tree: `d.stored = []` for
every d in decls. (2) There are as many challenges as rounds: `Rs.length = decls.length`. (3) D has
the challenges by the round's number: entry n of Rs is `D (i + n)`.

Limits. Nothing on which tables are at hand. `tree` is a free parameter: where it returns `none` for
a declared source, that opening's group has the empty list at every position, and no statement of
this file excludes that case. `colGroups_opens` is an equation of two lists; it holds also at values
that no run reaches. It says nothing of rounds that open a stored tree, nor of lists of rounds and
challenges of different lengths. No statement of this file names the frame's `readsOf` or
`fillCols`, the term `stagesAll`, or a proximity test: `regroup_cols` has a hypothesis of its own,
which is not treated here. Nothing on a decision, on completeness, on soundness or on what is
hidden.
-/
import Johnson.Desc.ProofFile.Honest.Small.ColGroups
import Johnson.Prover.Link.BodyAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc (Place)
open Johnson.Prover.Link (groupAt)
open ProofFile.Honest.Small (colGroups)

/-- The declared openings of a list of rounds: for each entry of a round's field `opens` the triple
(the round's number, the shape's depth, the source). i: the first round's number. -/
def planOpens : List Fmt.DeclaredRound → ℕ → List (ℕ × ℕ × Fmt.TreeSource)
  | [], _ => []
  | d :: ds, i => d.opens.map (fun o => (i, o.1.a, o.2)) ++ planOpens ds (i + 1)

/-- The column at position x of the table that `tree` returns for the source σ; the empty list where
`tree σ` is `none`. -/
def colAt (tree : Fmt.TreeSource → Option (Place × Table)) (σ : Fmt.TreeSource) (x : ℕ) : List UInt64 :=
  ((tree σ).map (·.2.col x)).getD []

/-- **`colGroups` is the list of the declared openings' groups, in order.** Hypotheses: no round
opens a stored tree; there are as many challenges as rounds; entry n of Rs is `D (i + n)`. i: the
first round's number. -/
theorem colGroups_opens (stored : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (D : ℕ → Fmt.Drawn) :
    ∀ (decls : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn) (i : ℕ),
      (∀ d ∈ decls, d.stored = []) → Rs.length = decls.length →
      (∀ n (h : n < Rs.length), Rs[n] = D (i + n)) →
      colGroups stored tree decls Rs =
        (planOpens decls i).map fun x => groupAt x.2.1 (D x.1).poss (colAt tree x.2.2)
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, h, _ => by cases h
  | d :: ds, R :: Rs, i, hs, hl, hD => by
    have h0 : R = D i := hD 0 (by simp)
    subst h0
    have ih := colGroups_opens stored tree D ds Rs (i + 1)
      (fun d' hd' => hs d' (List.mem_cons_of_mem _ hd')) (by simpa using hl)
      (fun n hn => by
        have k := hD (n + 1) (by simpa using hn)
        rw [show i + (n + 1) = i + 1 + n by omega] at k
        simpa using k)
    unfold colGroups planOpens
    rw [ih, hs d (by simp), List.map_nil, List.nil_append, List.map_append, List.map_map]
    rfl

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.colGroups_opens
#print axioms ProofFile.Honest.K12.planOpens
#print axioms ProofFile.Honest.K12.colAt
