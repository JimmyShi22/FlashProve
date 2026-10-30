-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/ReadPub.lean: `ReadAsks` (Johnson/Desc/K12/Honest/ReadWhole.lean) cut in
two: what hangs on the statement, the book and the single rows' own numbers, and what hangs on the
view (the sampled positions and the dealt columns' form). The first half reads no field element and
no column. `ReadAsks` is the structure of hypotheses under which `read_yes_trees` (ReadWhole.lean)
proves that `Tw.L9.readOld` (Johnson/Top/H0/Tw/L9/Switch.lean) returns `.ok`. `readOld` is the step
of a proximity test's code switch that reads the symbols of the carried single rows out of the dealt
columns. This file defines each half as a structure of hypotheses and proves that the two together
give `ReadAsks`: three definitions and one theorem, general in every parameter. Each half is derived
in a file that imports this one, under hypotheses of its own: `ReadPub` by `readPub_sh`
(Johnson/Desc/K12/Honest/Shape/ReadShape.lean), `ReadView` by `readView_term`
(Johnson/Desc/K12/Honest/ReadViewTerm.lean). Johnson/Desc/K12/Honest/Shape/ReadFirst.lean calls the
theorem. Nothing here uses the frame for an honest side (Johnson/Desc/ProofFile/Honest/Frame.lean),
and the file does not import it, directly or through its imports.

In the list: the statement S (`Statement`, OnBytes/Iop/Ground.lean) holds the codes, the oracle
messages and the groups. The book B0 (`TreeBook`, Ground.lean) holds the trees sent so far and each
oracle message's place: the index of its tree and its place among that tree's parts. The single rows
old (`SingleRows`, OnBytes/Iop/Fold.lean) are the rows that a proximity test carries between its
steps; their layout (`GroupLayout`, Ground.lean) names the oracle messages whose rows are folded
(the members). pos (`Positions`, Ground.lean) has a range (`logN`), the sampled positions (`draws`)
and the listed positions (`all`), by which trees are opened. A dealt column (`Tw.L9.Col`) is a key,
a position and a list of words. places is an array of places; by the field `placed` it lists the
places of the oracle messages that are opened to read old (`singleRowsOracles old`, Fold.lean).
`treesAt places` (ReadWhole.lean) lists the indices of their trees, each once, increasing. TT and cs
are functions of a tree's index: TT t is a tree, cs t a list of columns.

  `readAsks_of_halves`: the two halves give `ReadAsks i pos places TT cs`, at every input i of a
    code switch (`Tw.L9.SwIn`) and all pos, places, TT and cs
  `ReadPub S B0 old logN places TT`: a definition: the first half: the clauses of `ReadAsks` on
    places, trees, oracle messages and the rows' numbers. logN: the positions' range. Its fields
    `placed`, `whole`, `oracle`, `shape`, `masks`, `noKept`, `kept`, `main`, `mask` and `fresh` have
    the text of the fields of `ReadAsks` with these names, with S, B0 and old for `i.st`, `i.book`
    and `i.old`. Its field `tree` has `TreePub` where that of `ReadAsks` has `TreeAsks`
    (Johnson/Desc/K12/Honest/ReadTrees.lean)
  `ReadView F pos places TT cs opened`: a definition: the second half: every listed position is
    among the sampled ones · each tree's dealt columns (`Dealt`,
    Johnson/Desc/K12/Honest/ReadTrees.lean) · the dealt columns are the trees', tree after tree, and
    no more. These are its fields `listed`, `dealt` and `opened`. `Dealt F pos (TT t) (cs t)` says:
    cs t has as many columns as the list at which the tree is opened under pos (`Blk.ownList`,
    Ground.lean) has positions; the j-th column has the key `(TT t).number - F`, the list's j-th
    position, and as many words as the tree is wide. `Dealt` says nothing of the words themselves.
    F: the number of the first tree
  `TreePub S logN B0 t T`: a definition: of one tree, the fields of `TreeAsks` without `dealt`, with
    logN for `pos.logN`. `there`: T is in the book, at index t. `share`: `shareOk S T`
    (ReadTrees.lean), the test on what shares a leaf, passes. `once`: where T may be opened at one
    list only (`oneList`), it has not been opened. `short`: T is not longer than the range

By what. The proof builds `ReadAsks` field by field out of the fields of the two hypotheses; at each
tree it builds `TreeAsks` out of `TreePub` and the field `dealt` of `ReadView`. It calls no lemma.

Hypotheses. P: `ReadPub` at `i.st`, `i.book`, `i.old` and `pos.logN`. V: `ReadView` at
`i.firstTree`, pos and `i.opened`. Both are at the same places and TT.

Limits. Both halves are hypotheses: this file shows neither at any value. That the first half reads
no field element and no column is seen from its text; no theorem of this file states it. Its
parameters S and old hold field elements; of the list `old.gamma` the test `Own.shapeFits`
(Johnson/Desc/Own/Symbols.lean) reads the length. The converse, that `ReadAsks` gives the two
halves, is not stated. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.ReadWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes
open VerifiableInference.Desc
open Tw.L9 (SwIn)

/-- Of one tree: the fields of `TreeAsks` (Johnson/Desc/K12/Honest/ReadTrees.lean) without `dealt`,
with logN for `pos.logN`. -/
structure TreePub (S : Statement) (logN : Nat) (B0 : TreeBook) (t : Nat) (T : Tree) : Prop where
  there : B0.trees[t]? = some T
  share : shareOk S T = true
  once : (!T.oneList || T.lists == 0) = true
  short : T.shape.logN ≤ logN

/-- The first half: the clauses of `ReadAsks` on places, trees, oracle messages and the rows'
numbers. logN: the positions' range. -/
structure ReadPub (S : Statement) (B0 : TreeBook) (old : SingleRows) (logN : Nat)
    (places : Array (Nat × Nat)) (TT : Nat → Tree) : Prop where
  placed : ((singleRowsOracles old).mapM fun o => B0.place[o]?) = some places
  whole : ((treesAt places).all fun t =>
    ((B0.trees[t]?).map (·.parts)).getD #[] |>.all (singleRowsOracles old).contains) = true
  tree : ∀ t ∈ treesAt places, TreePub S logN B0 t (TT t)
  oracle : ∀ o ∈ (singleRowsOracles old).toList, ∃ x, S.oracles[o]? = some x
  shape : Own.shapeFits old = true
  masks : old.masks = 2
  noKept : old.keptRows = 0
  kept : ∀ w, w < old.layout.members.size → old.layout.kept.getD w false = false
  main : ∀ w (hw : w < old.layout.members.size) (x : Oracle),
    S.oracles[old.layout.members[w]]? = some x → x.shape.mainRows = 0 ∨
      ∃ f, old.layout.mainFirst.getD w none = some f ∧ f + x.shape.mainRows ≤ 2 ^ old.layout.k
  mask : ∀ w (hw : w < old.layout.members.size) (x : Oracle),
    S.oracles[old.layout.members[w]]? = some x → x.shape.maskRows = 0 ∨
      ∃ f, old.layout.maskFirst.getD w none = some f ∧ f + x.shape.maskRows ≤ 2 ^ old.layout.h
  fresh : ∀ x : Oracle, S.oracles[old.fresh]? = some x → x.shape.maskRows = 2 ^ old.layout.h

/-- The second half: the fields `listed` and `opened` of `ReadAsks`, and `dealt` of `TreeAsks` at
each tree. F: the number of the first tree. -/
structure ReadView (F : Nat) (pos : Positions) (places : Array (Nat × Nat)) (TT : Nat → Tree)
    (cs : Nat → List Tw.L9.Col) (opened : List Tw.L9.Col) : Prop where
  listed : ∀ x ∈ pos.all.toList, x ∈ pos.draws.toList
  dealt : ∀ t ∈ treesAt places, Dealt F pos (TT t) (cs t)
  opened : opened = (treesAt places).flatMap cs

/-- **The two halves give `ReadAsks`.** -/
theorem readAsks_of_halves (i : SwIn) (pos : Positions) (places : Array (Nat × Nat))
    (TT : Nat → Tree) (cs : Nat → List Tw.L9.Col)
    (P : ReadPub i.st i.book i.old pos.logN places TT)
    (V : ReadView i.firstTree pos places TT cs i.opened) : ReadAsks i pos places TT cs :=
  ⟨P.placed, P.whole, fun t ht =>
    ⟨(P.tree t ht).there, (P.tree t ht).share, (P.tree t ht).once, (P.tree t ht).short,
      V.dealt t ht⟩,
    V.opened, P.oracle, V.listed, P.shape, P.masks, P.noKept, P.kept, P.main, P.mask, P.fresh⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.readAsks_of_halves
#print axioms ProofFile.Honest.K12.TreePub
#print axioms ProofFile.Honest.K12.ReadPub
#print axioms ProofFile.Honest.K12.ReadView
