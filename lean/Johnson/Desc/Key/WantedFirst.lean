-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Key/WantedFirst.lean: the key file's first chain: its rows of Block.lean's two tables
`wanted` (for every block of the flat list its place and its number of rounds) and `owed` (which
messages a drawing block must name in `before`), MADE OFF THE PUBLIC VALUES OF THE ONE-TIME CHAIN.
Definitions with code. No theorem. Nothing on soundness.

Block.lean asks that these tables are made by another file than the one that writes the blocks,
independently of it. The first chain's blocks stand in Johnson/Desc/Key/Chain1.lean, Link.lean,
One.lean. This file imports none of these, nor Where.lean: it
reads `OneTime` (OnBytes/Key/OneTime.lean) and the program's own `Wf.lookupsOf`, `Wf.matrixOf`,
`Lkp.roundsOf` and `linMessageW`.

Main names.
  `testRounds`: the rounds of a proximity test, from its stages: the batching round; for every stage
    but the last a fold's challenge, its k rounds, the next message's seed and the code switch; the
    base case's two.
  `wantedFirst`: the rows of `wanted`: the two sendings (two rounds each: seed, answer); for each
    lookup six rows, of which the third alone has rounds, as many as `Lkp.roundsOf` lists; the
    laying of the lookups' rows (none); the ranges' test; the batching of the rows on the table
    (BAT-sigma, PSC epsilon, one round for each of the matrix's column variables:
    OnBytes/Iop/Batt.lean); W's sending, where the shape has a message with W (`linMessageW`); the
    seal (one).
  `owedFirst`: the rows of `owed`: a lookup's argument draws behind the index-mask message and the
    lookups' own message; the ranges' test behind the own message; the batching of the rows on the
    table behind the index-mask message. As (chain, tree): the two messages are the chain's trees 0
    and 1.

Limits. THE LABELS (chain, link, piece, kind) ARE A CONVENTION OF THE BLOCKS' FILES: they are
written here by hand, after their words and after `FileDescription.places` at two stored key files; which
block bears a label no table says (Block.lean's own limit). A link's pieces 4 and 5 are no written
numbers there: `Link.blocksInOrder` stamps them behind what the link hears and closes; they are 4 and 5
because a lookup's link hears two blocks and closes none. The numbers of rounds are this file's
reading of the protocol; that the plan's declared rounds are these is asked by `planOk` of the
blocks' rounds and by `wantedOk` of these rows against the blocks'. `owedFirst` names what the
key file's table of borders holds as pinned in front of each drawing block (its rows' context); a
block may name more. Chains 2 and 3 have no row here.

-/
import Johnson.Desc.Block
import OnBytes.Key.OneTime
import OnBytes.Iop.Lkp
import OnBytes.Iop.Wf
import OnBytes.Iop.Lin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes OnBytes.Params

/-- The rounds of a proximity test, its batching round among them. -/
def testRounds (st : List IoppStage) : Nat := 1 + (st.dropLast.map fun s => s.k + 3).sum + 2

/-- A lookup's link's six rows; n: the rounds of the lookup's argument. -/
def wantedLink (l n : Nat) : List (Place × Nat) :=
  [(⟨1, some l, 0, .frame⟩, 0), (⟨1, some l, 1, .frame⟩, 0), (⟨1, some l, 2, .K3⟩, n),
    (⟨1, some l, 3, .frame⟩, 0), (⟨1, some l, 4, .frame⟩, 0), (⟨1, some l, 5, .frame⟩, 0)]

/-- **The first chain's rows of `wanted`.** -/
def wantedFirst (one : OneTime) : List (Place × Nat) :=
  let m := Wf.matrixOf one.lin
  [(⟨1, none, 1, .K1⟩, 2), (⟨1, none, 2, .K1⟩, 2)] ++
    ((Wf.lookupsOf one.ranges m).zipIdx.flatMap fun x =>
      wantedLink x.2 (Lkp.roundsOf 0 x.1).length) ++
    [(⟨1, none, 4, .frame⟩, 0), (⟨1, none, 5, .K12⟩, testRounds one.ranges.stages),
      (⟨1, none, 13, .K13⟩, 2 + m.kCol)] ++
    (if (linMessageW one.lin).isSome then [(⟨1, none, 14, .K1⟩, 2)] else []) ++
    [(⟨1, none, 15, .frame⟩, 1)]

/-- **The first chain's rows of `owed`.** -/
def owedFirst (one : OneTime) : List (Place × List (Nat × Nat)) :=
  ((List.range (Wf.lookupsOf one.ranges (Wf.matrixOf one.lin)).length).map fun l =>
      ((⟨1, some l, 2, .K3⟩ : Place), [(1, 0), (1, 1)])) ++
    [(⟨1, none, 5, .K12⟩, [(1, 1)]), (⟨1, none, 13, .K13⟩, [(1, 0)])]

end VerifiableInference.Desc.Key
