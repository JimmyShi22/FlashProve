-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/WantedLater.lean: the key file's shared chain and last chain: their rows of
Block.lean's two tables `wanted` (for every block of the flat list its place and its number of
rounds) and `owed` (which messages a drawing block must name in `before`), MADE OFF THE PUBLIC
VALUES: the item "the test on the table" (`LinShape`) and the one-time chain's values. Definitions
with code. No theorem. Nothing on soundness.

Block.lean asks that these tables are made by another file than the one that writes the blocks,
independently of it. This file imports none of the files that write or lay the two chains' blocks.
The first chain's rows: Johnson/Desc/Key/WantedFirst.lean.

What the rounds are read off: the verifier program's own order of calls (OnBytes/Iop/Lin.lean).
  `linSharedVerify`: the point "LIN point" is drawn (1 round); two groups are made; o_u is sent (a
    sending: seed, answer: 2) and the stored table is read at drawn positions ("LOC": 1); Omega is
    sent, with the split's mask message where the shape splits (2); the messages join their groups;
    "LIN zeta" is drawn (1); where the shape splits, the row (Fold) is split ("SPLIT": 1).
  `linSharedTestsVerify`: the proximity test on o_u's group; where the shape splits, the one on
    Omega's group. Then the caller seals the chain (1).
  `linSecondVerify`, `linSecondTestsVerify`: Omega is adopted and the row (Dot) is laid (no round);
    the proximity test on the request's own group. The chain has no seal.
The planner's lists say the same (OnBytes/Params/PlanListsChains.lean: `sharedChainList`,
`secondChainList`).

Main names.
  `proximityRounds`: the rounds of a proximity test, from its stages.
  `wantedShared`, `wantedSecond`: the rows of `wanted`.
  `treeOfW`: the number, among the first chain's trees, of the tree of W.
  `owedShared`, `owedSecond`: the rows of `owed`, as (chain, tree). In the shared chain o_u's tree
    is 0, Omega's 1, the split's mask message's 2. A block draws behind what its challenge must not
    be fitted to:
      "LIN point": the first chain's index-mask message and W (the program's words: the shared
        point comes "after every claim, every W and every answer");
      "LOC": o_u;
      "LIN zeta": o_u, Omega and, where the shape splits, the split's mask message;
      the test on o_u's group, the test on Omega's group, the own test: the trees of the group's
        members.

Limits. THE LABELS (chain, link, piece, kind) ARE A CONVENTION OF THE BLOCKS' FILES: they are
written here by hand, after `FileDescription.places` at two stored key files; which block bears a label no
table says (Block.lean's own limit). NO BLIND SECOND READING: the rows of `wanted` and of `owed`
were written with the blocks' numbers of rounds and `before` lists in sight; they were then read
off the program's order, which says the same. `owedOk` asks that a block names what its row owes:
a row that owes too little passes, and no test can tell.
The numbers of rounds are this file's reading of the program;
that the plan's declared rounds are these is asked by `planOk` of the blocks' rounds and by
`wantedOk` of these rows against the blocks'. WHERE THE SHAPE DOES NOT SPLIT THE ROW (Fold) no key
file has been seen: the rows there are read off the program alone. WHERE THE SHAPE SPLITS THE ROW
(Dot) (`ownSplitNeeded`) the program has a round and a test more in the last chain; these tables
have the plain arm's rows there too. A row of `owed` that names a message of an earlier chain is
idle as a test of the order (Block.lean). `treeOfW` counts: the index-mask message's tree, the
lookups' own message's, the ranges' test's own mask's where masks do not ride, one for each stage of
that test but the first. A sending's block draws too; it has no row: it is held at its first draw,
and what it sends itself cannot be owed by it. "SPLIT" draws nothing.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Block
import OnBytes.Params.Chains
import OnBytes.Iop.Lin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes OnBytes.Params

/-- The rounds of a proximity test: the batching round; for every stage but the last a fold's
challenge, its k rounds, the next message's seed and the code switch; the base case's two. -/
def proximityRounds (st : List IoppStage) : Nat := 1 + (st.dropLast.map fun s => s.k + 3).sum + 2

/-- **The shared chain's rows of `wanted`.** -/
def wantedShared (S : LinShape) : List (Place × Nat) :=
  [(⟨2, none, 0, .frame⟩, 0), (⟨2, none, 1, .K14⟩, 1), (⟨2, none, 2, .K1⟩, 2),
    (⟨2, none, 3, .K14⟩, 0), (⟨2, none, 4, .K14⟩, 1), (⟨2, none, 5, .K1⟩, 2),
    (⟨2, none, 6, .K14⟩, 0), (⟨2, none, 7, .K14⟩, 1),
    (⟨2, none, 8, .K14⟩, if S.sharedSplitNeeded then 1 else 0),
    (⟨2, none, 9, .K12⟩, proximityRounds S.testU)] ++
    (if S.sharedSplitNeeded then [(⟨2, none, 10, .K12⟩, proximityRounds S.testOmega)] else []) ++
    [(⟨2, none, 11, .frame⟩, 1)]

/-- **The last chain's rows of `wanted`.** -/
def wantedSecond (S : LinShape) : List (Place × Nat) :=
  [(⟨3, none, 0, .K14⟩, 0), (⟨3, none, 1, .frame⟩, 0),
    (⟨3, none, 2, .K12⟩, proximityRounds S.testOwn), (⟨3, none, 3, .frame⟩, 0)]

/-- The number, among the first chain's trees, of the tree of W. -/
def treeOfW (one : OneTime) : Nat :=
  2 + (if one.ranges.choice.masksRide then 0 else 1) + (one.ranges.stages.length - 1)

/-- **The shared chain's rows of `owed`.** -/
def owedShared (one : OneTime) (S : LinShape) : List (Place × List (Nat × Nat)) :=
  let sp : List (Nat × Nat) := if S.sharedSplitNeeded then [(2, 2)] else []
  [(⟨2, none, 1, .K14⟩, [(1, 0), (1, treeOfW one)]), (⟨2, none, 4, .K14⟩, [(2, 0)]),
    (⟨2, none, 7, .K14⟩, [(2, 0), (2, 1)] ++ sp),
    (⟨2, none, 9, .K12⟩, if S.sharedSplitNeeded then [(2, 0), (2, 2)] else [(2, 0), (2, 1)])] ++
    (if S.sharedSplitNeeded then [(⟨2, none, 10, .K12⟩, [(2, 1), (2, 2)])] else [])

/-- **The last chain's rows of `owed`.** -/
def owedSecond (one : OneTime) : List (Place × List (Nat × Nat)) :=
  [(⟨3, none, 2, .K12⟩, [(1, 0), (1, treeOfW one), (2, 1)])]

end VerifiableInference.Desc.Key
