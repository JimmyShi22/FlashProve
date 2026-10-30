-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/WalkTie.lean: the format page's walk through a Merkle opening compared with the library's
pruned walk: tests at the page's own cases.

The format page (docs/format/FORMAT.md, which comes with the programs, the C++ implementation that
comes with this Lean code) says in its section 7 how a reader walks from opened leaves and given
digests to a root; Fmt/Rules7.lean renders it (`Fmt.walkW`). The library has its own pruned walk
(Hash/Octopus.lean). This file holds two definitions for the tests, and tests. No theorem here; the
theorems are in Run/WalkTieProofs.lean.

A pruned walk recomputes the root of a Merkle tree from several opened leaves and one shared list
of sibling digests, level by level.

Sources. Section 7 of the format page, rules R7.6 to R7.10 on the walk; this file has not been held
against the page as it ships, and may differ from it.


Why. The compiled verifier (`verifyOneProtocol`, Compile/Batch/Verifier.lean) walks with `Octopus.octC` over
whole paths that a parser makes by `Octopus.fill` from the digests in a file. The reader of a file
walks with `Fmt.walkW`. If the two walks differed in which digest they take where, a file that the
one accepts could be refused by the other.

1. What the file contains. Two definitions that serve the tests.

2. What is checked when the file compiles, at the page's tree and its four lists, and for the count
also at a toy file's list (2, 9, 14 at depth 4).
   The number of digests that the page's walk takes (`Fmt.walkPlaces`) is `Octopus.need`.
   `Octopus.octC` at the page's vertex, on the opened leaves and on the given digests that
   `Fmt.readOpening` returns, ends in one value: the root that `Fmt.readOpening` returns, which is
   the tree's.
   `Octopus.fill` on these given digests makes one whole path of the tree's depth for each
   position, and the pruned set read off them (`Octopus.reads`) is the list of given digests again.
   That each path has the tree's depth is tested at the list 1, 3, 6 alone; at the lists 0, 2, 4, 6
   and 2, 3 the number of paths is tested. The set read off is compared at these three lists, not
   at the list 5.

3. Theorems. None.

Notation:
  `.two`: one of the format's two fields (`Fld.two`, Fmt/Rules1.lean);
  `40`: the salt's length (`Fmt.readOpening`, Fmt/Rules7.lean);
  `164`: the number under which the leaves of a run's tree are hashed (`Fmt.leafNo`);
  `5` in `Fmt.leaf 164 5 3 x`: the tree's number (`Fmt.Shape.tree`, Fmt/Plan.lean);
  `3` there and in `octC .. 3 xs`, `fill 3 xs`: the tree's depth (`Fmt.Shape.a`);
  `xs`: the list of opened positions (`Fmt.readOpening`).

4. What is not claimed.
   The tests are evaluations at five lists, made when the file is compiled: they leave no theorem.
   Nothing on leaves (on the page's side their hash is bound to run, tree and position).
   Nothing on `verifyOneProtocol` itself.
   Octopus reads a message that is too short as if it were filled up; the page refuses it. The
   count is the parser's duty.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules7
import Hash.OctopusFacts

namespace Run.WalkTie
open Octopus

/-! ### Tests -/

#guard (Fmt.walkPlaces 3 [1, 3, 6]).length = need 3 [1, 3, 6] ∧ need 3 [1, 3, 6] = 4
#guard (Fmt.walkPlaces 3 [5]).length = need 3 [5] ∧ need 3 [5] = 3
#guard (Fmt.walkPlaces 3 [0, 2, 4, 6]).length = need 3 [0, 2, 4, 6] ∧ need 3 [0, 2, 4, 6] = 4
#guard (Fmt.walkPlaces 3 [2, 3]).length = need 3 [2, 3] ∧ need 3 [2, 3] = 2
#guard (Fmt.walkPlaces 4 [2, 9, 14]).length = need 4 [2, 9, 14] ∧ need 4 [2, 9, 14] = 7

/-- the library's walk at the page's vertex, on the page's tree's own leaves at xs and the given
digests that the page's reader returns for it: the values after three levels, and beside them the
reader's root -/
def wtOct (xs : List Nat) : Option (List ByteArray × ByteArray) :=
  (Fmt.readOpening Fmt.k7Cfg .two 40 Fmt.k7Shape Fmt.k7Start xs (Fmt.k7Open xs) 0).map fun o =>
    (Id.run (octC (M := Id) (fun l r => pure (Fmt.vertex Fmt.k7Cfg l r)) 3 xs
          (xs.map fun x => Fmt.leaf 164 5 3 x Fmt.k7Start (Fmt.k7Column x) (Fmt.k7SaltAt x))
          o.given),
      o.root)

#guard (wtOct [1, 3, 6]).map (fun r => decide (r.1 = [r.2] ∧ r.2 = Fmt.k7Root)) = some true
#guard (wtOct [5]).map (fun r => decide (r.1 = [r.2] ∧ r.2 = Fmt.k7Root)) = some true
#guard (wtOct [0, 2, 4, 6]).map (fun r => decide (r.1 = [r.2] ∧ r.2 = Fmt.k7Root)) = some true
#guard (wtOct [2, 3]).map (fun r => decide (r.1 = [r.2] ∧ r.2 = Fmt.k7Root)) = some true

/-- whole paths from what the page's reader returns, and the pruned set read off them again -/
def wtPaths (xs : List Nat) : Option (List (List ByteArray) × List ByteArray × List ByteArray) :=
  (Fmt.readOpening Fmt.k7Cfg .two 40 Fmt.k7Shape Fmt.k7Start xs (Fmt.k7Open xs) 0).map
    fun o => (fill 3 xs o.given, reads 3 (xs.zip (fill 3 xs o.given)), o.given)

#guard (wtPaths [1, 3, 6]).map (fun r => decide (r.1.length = 3 ∧ (r.1.all fun p => p.length == 3) = true ∧ r.2.1 = r.2.2)) = some true
#guard (wtPaths [0, 2, 4, 6]).map (fun r => decide (r.1.length = 4 ∧ r.2.1 = r.2.2)) = some true
#guard (wtPaths [2, 3]).map (fun r => decide (r.1.length = 2 ∧ r.2.1 = r.2.2)) = some true
-- one position: the whole path is the list of given digests
#guard (wtPaths [5]).map (fun r => decide (r.1 = [r.2.2])) = some true

end Run.WalkTie
