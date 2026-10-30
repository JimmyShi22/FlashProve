-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ChainTrees.lean: THE TREES THAT THE ROUNDS OF THE COPY's FILE's PROTOCOL SEND,
BY ROUND: depth and width, at the written letters dsFull | dsSmall (OnBytes/Flat/LinkSibAt.lean), as
written lists. Statements and proofs; each by the kernel's evaluation.

  treesOf       a list of rounds' data: for each round its trees' (depth, width)
  fr_trees      the full size: 41 rounds, five trees: at the rounds 1, 15, 23, 30, 37
  sr_trees      the small size: 24 rounds, three trees: at the rounds 1, 13, 20
  fr_one, sr_one   a round sends at most one tree

Each stands under "set_option maxRecDepth 100000 in", as the library's own closed facts at these
letters do (Johnson/Desc/K15/TypedV.lean): a limit of elaboration is raised; the kernel checks the
term.

Limits. Public numbers alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Flat.LinkSibAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes.Flat (dsFull dsSmall)
open TypedOracleCompiler.Run.PQ (RD)

/-- For each round: its trees' depth and width. -/
def treesOf (ds : List RD) : List (List (ℕ × ℕ)) := ds.map (·.trees.map fun s => (s.a, s.W))

set_option maxRecDepth 100000 in
theorem fr_trees : treesOf dsFull =
    [[], [(24, 645)]] ++ List.replicate 13 [] ++ [[(21, 120)]] ++ List.replicate 7 [] ++
      [[(17, 72)]] ++ List.replicate 6 [] ++ [[(13, 72)]] ++ List.replicate 6 [] ++
      [[(14, 12)]] ++ List.replicate 3 [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem sr_trees : treesOf dsSmall =
    [[], [(17, 111)]] ++ List.replicate 11 [] ++ [[(14, 72)]] ++ List.replicate 6 [] ++
      [[(14, 12)]] ++ List.replicate 3 [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem fr_one : ∀ d ∈ dsFull, d.trees.length ≤ 1 := fun d hd =>
  of_decide_eq_true (List.all_eq_true.1
    (show (dsFull.all fun d => decide (d.trees.length ≤ 1)) = true by decide +kernel) d hd)

set_option maxRecDepth 100000 in
theorem sr_one : ∀ d ∈ dsSmall, d.trees.length ≤ 1 := fun d hd =>
  of_decide_eq_true (List.all_eq_true.1
    (show (dsSmall.all fun d => decide (d.trees.length ≤ 1)) = true by decide +kernel) d hd)

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.fr_trees
#print axioms Johnson.Prover.Link.sr_trees
#print axioms Johnson.Prover.Link.fr_one
#print axioms Johnson.Prover.Link.sr_one
