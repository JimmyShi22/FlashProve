-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Names/TreeName.lean: «THE OPEN LEDGER's ARRAYS HAVE THE PLAN's NAMES»: AN
ARRAY's NAME AS A READING OF AN ARRAY, AND THE WRITINGS THAT LEAVE IT. MADE BY PROGRAM FROM THE
LIBRARY's Johnson/Desc/First/Batch/Law/Look.lean, WITH AN ARRAY's NAME (`treeName`,
Johnson/Desc/K8/Honest/Names/TreeName.lean) IN THE PLACE OF ITS LOOK: every declaration of that file
that the instance `seatKeeps_arrNames` (Names/ArrNamesSeat.lean) wants and that names the looks, or
leans on one that does, under a new name; the others are called where they lie: that file is
imported. NO NEW ARGUMENT: the library's proofs, token for token, but for the turns that are named
here. None of the library's goals.
Why. The smallness test's second computation asks that the digits' array bears the name "ZZ"
(`piecesTile`, OnBytes/Model/Tail.lean). The library carries each array's look (kind, rows, columns,
number of virtual rows) from the planned ledger to every reached state; a look holds no name. Spent
in Johnson/Desc/K8/Honest/NamesAtBatch.lean.
KEPT AND RENAMED (5): look → treeName · look_rows_map → arrName_rows_map · look_rows_modify →
arrName_rows_modify · ofFrame → ofFrameN · look_frame → arrName_frame.
NOT WANTED BY THE INSTANCE, AND SO NOT MADE (2): looks_of_frame · widths_of_looks.
THE GENERAL TURNS: look → treeName · Look → String · …looks… → …arrNames… · …Looks… → …ArrNames… ·
shOfBuilt → anOfBuilt · shOf_at → anOf_at · Stays → StaysN · the tactic stays → staysN · every other
kept name gets an N behind; the letter shOf stays, at the type ℕ → List String; in comments "look" →
"name". Lines over 100 signs are broken.
TURNED BY HAND, THREE: the type `Look` falls (String stands in its place) · `treeName X := X.name` ·
`ofFrameN x := x.1.name`.
Limits. ITS SOURCE's LIMITS ARE ITS OWN: one direction, from a yes or from a return; nothing says
that any state is reached. It is no second text of its source: it speaks of another field of an
array, and no law ties the two. The comments on the declarations are the source's, turned by the
same program: they were not written for this file. It stands in the source's own namespace, so that
every name resolves as there. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.First.Batch.Law.Look

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model

/-- An array's name. -/
def treeName (X : HTree) : String := X.name

theorem arrName_rows_map (X : HTree) (f : HRow → HRow) :
    treeName { X with rows := X.rows.map f } = treeName X := by
  simp [treeName]

theorem arrName_rows_modify (X : HTree) (r : Nat) (f : HRow → HRow) :
    treeName { X with rows := X.rows.modify r f } = treeName X := by
  simp [treeName]

/-- The name, off an array's frame. -/
def ofFrameN (x : HTree × Array (HRow × Nat)) : String := x.1.name

theorem arrName_frame (X : HTree) : ofFrameN X.frame = treeName X := by
  simp [ofFrameN, HTree.frame, treeName]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.arrName_rows_map
#print axioms VerifiableInference.Desc.LinkJoin.arrName_rows_modify
#print axioms VerifiableInference.Desc.LinkJoin.arrName_frame
