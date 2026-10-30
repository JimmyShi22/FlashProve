-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Names/ArrNamesFill.lean: «THE OPEN LEDGER's ARRAYS HAVE THE PLAN's NAMES»:
THE FILLING OF THE WEIGHTS LEAVES THE ARRAYS' NAMES. MADE BY PROGRAM FROM THE LIBRARY's
Johnson/Desc/First/Batch/Law/FitsAtS.lean, WITH AN ARRAY's NAME (`treeName`,
Johnson/Desc/K8/Honest/Names/TreeName.lean) IN THE PLACE OF ITS LOOK: every declaration of that file
that the instance `seatKeeps_arrNames` (Names/ArrNamesSeat.lean) wants and that names the looks, or
leans on one that does, under a new name; the others are called where they lie: that file is
imported. NO NEW ARGUMENT: the library's proofs, token for token, but for the turns that are named
here. None of the library's goals.
Why. The smallness test's second computation asks that the digits' array bears the name "ZZ"
(`piecesTile`, OnBytes/Model/Tail.lean). The library carries each array's look (kind, rows, columns,
number of virtual rows) from the planned ledger to every reached state; a look holds no name. Spent
in Johnson/Desc/K8/Honest/NamesAtBatch.lean.
KEPT AND RENAMED (1): fold_looks → fold_arrNames.
CALLED WHERE THEY LIE (9): Pub9 · pubOf · fixed9 · good9 · later_of_same · widths_of_frame ·
fold_widths · fill_widths · drawn_later.
NOT WANTED BY THE INSTANCE, AND SO NOT MADE (15): GoesOn · Fx9 · more9 · O9 · goesOn_refl ·
goesOn_trans · goesOn_looks · goesOn_widths · fill_looks · drawn_looks · goesOn_set · fitsM_atS ·
part_of_more · fx_of_more · kept_of_more.
THE GENERAL TURNS: look → treeName · Look → String · …looks… → …arrNames… · …Looks… → …ArrNames… ·
shOfBuilt → anOfBuilt · shOf_at → anOf_at · Stays → StaysN · the tactic stays → staysN · every other
kept name gets an N behind; the letter shOf stays, at the type ℕ → List String; in comments "look" →
"name". Lines over 100 signs are broken.
TURNED BY HAND: nothing.
Limits. ITS SOURCE's LIMITS ARE ITS OWN: one direction, from a yes or from a return; nothing says
that any state is reached. It is no second text of its source: it speaks of another field of an
array, and no law ties the two. The comments on the declarations are the source's, turned by the
same program: they were not written for this file. It stands in the source's own namespace, so that
every name resolves as there. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.First.Batch.Law.FitsAtS
import Johnson.Desc.K8.Honest.Names.TreeName

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open OnBytes.PscRun (Later)
open VerifiableInference.Desc.K9 (atS Where drawnClean drawn)
open VerifiableInference.Desc.First (S)

variable {α K : Type}

theorem fold_arrNames : ∀ (l : List Nat) (tr : Array HTree),
    (l.foldl (fun trees ti => trees.modify ti fillOne) tr).map LinkJoin.treeName =
      tr.map LinkJoin.treeName
  | [], _ => rfl
  | ti :: l, tr => by
    rw [List.foldl_cons, fold_arrNames l]
    exact map_modify_same LinkJoin.treeName fillOne (fun X => LinkJoin.arrName_rows_map X _) tr ti

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.fold_arrNames
