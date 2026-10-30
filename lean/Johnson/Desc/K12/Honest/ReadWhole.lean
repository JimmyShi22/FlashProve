-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/ReadWhole.lean: the reading of the old rows in a code switch accepts at a
list of trees: the whole reading. A code switch of a proximity test reads the symbols of its old
rows (the carried rows, the field `old` of `SwIn`) out of dealt columns. `Tw.L9.readOld`
(Johnson/Top/H0/Tw/L9/Switch.lean) finds the places of the rows' oracle messages, opens their trees
one after the other, finds each message's symbols and makes the rows' symbols of them by the layout.
Here its acceptance follows from clauses on the statement, the book, the rows' own numbers and the
form of the dealt columns: whatever words the columns hold. Any number of members, in any number of
trees, of any depths up to the positions' range; a fresh mask table; no kept member. Two definitions
and one theorem. The file does not depend on the frame for an honest side
(Johnson/Desc/ProofFile/Honest/Frame.lean).

In the list: i (`SwIn`, Switch.lean) is what the code switch reads. Of its fields the reading uses
these. `i.st` is the statement (`Statement`, OnBytes/Iop/Ground.lean), which holds the oracle
messages, each under a number. `i.book` is the book (`TreeBook`, Ground.lean): the trees, and for
each oracle message its place, that is the place of its tree in the book and its number among that
tree's parts. `i.firstTree` is the number of the chain's first tree. `i.opened` is the list of dealt
columns (`Col`, Switch.lean: a key, a position and a list of words). `i.old` is the old rows
(`SingleRows`, OnBytes/Iop/Fold.lean) with their layout (`GroupLayout`, Ground.lean). The layout's
members are the oracle messages whose rows are folded; its main table has 2 ^ `k` rows and its mask
table 2 ^ `h` rows. The messages asked for are `singleRowsOracles i.old` (Fold.lean): where
`i.old.masks` is 2, the members and then `i.old.fresh`, the oracle message whose mask rows are the
fresh mask table. pos (`Positions`, Ground.lean) has a range (`logN`), the sampled positions
(`draws`) and the listed positions (`all`: the list by which trees are opened). places, TT and cs
are free parameters, which `ReadAsks` ties to i: places to the places of the messages asked for and,
for each t in `treesAt places`, `TT t` to the tree at place t of the book and `cs t` to that tree's
dealt columns.

  `read_yes_trees`: under `ReadAsks i pos places TT cs` there is a y such that `readOld i pos` is
    `.ok (bump i.book (treesAt places), [], y)`: the reading accepts, leaves no column, and counts
    one list more at each tree (`bump`, Johnson/Desc/K12/Honest/ReadTrees.lean)
  `ReadAsks i pos places TT cs`: a definition: the hypothesis of `read_yes_trees`, a structure of
    clauses. Of the book: every message asked for has a place, and places lists these (`placed`);
    the trees to be opened hold no other message (`whole`); `TreeAsks` (ReadTrees.lean) holds at
    each of them, with the tree `TT t` and the columns `cs t` (`tree`). Of the dealt columns: they
    are the trees' dealt columns `cs t`, tree after tree, and no more (`opened`). Of the statement:
    every message asked for is there (`oracle`). Of the positions: every listed one is among the
    sampled ones (`listed`). Of the rows: their own numbers pass their test; two mask rows; no kept
    row; no kept member; each member's rows have a first row in the layout and fit the two tables,
    or are none; the fresh table has as many rows as the mask table. The fields for these, in this
    order: `shape` (the test is `Own.shapeFits`, Johnson/Desc/Own/Symbols.lean), `masks`, `noKept`,
    `kept`, `main` with `mask`, `fresh`
  `treesAt places`: a definition: the places of the trees to be opened, each once, increasing:
    `listOfT` (OnBytes/Chain/Draws.lean) of the first components of places

By what. `open_all` (ReadTrees.lean) gives the loop over the trees; that the trees are pairwise
different follows from `listOfT_eq` (Draws.lean) and `Fmt.listOf_incr` (Fmt/Rules6Laws.lean).
`symbols_there` and `mapM_all` (Johnson/Desc/K12/Honest/ReadSymbols.lean) give each message's
symbols; that a message's tree is among the opened ones follows from `listOfT_eq` and
`Fmt.listOf_mem` (Rules6Laws.lean). From the sizes that `symbols_there` states and the fields
`kept`, `main`, `mask` and `fresh` the proof derives `ColsFit`
(Johnson/Desc/K12/Honest/ReadRows.lean), and `rows_there` (ReadRows.lean) then gives y.
`OnBytes.Slice.array_mapM_inv` (OnBytes/Slice/BlkOpenN.lean) gives the size and the entries of an
array that `mapM` returns. The last step unfolds `readOld`.

Limits. `ReadAsks` is a hypothesis: this file proves it at no i, pos, places, TT and cs.
`read_first_any` (Johnson/Desc/K12/Honest/Shape/ReadFirst.lean) derives it inside its proof, under
hypotheses of its own. No theorem of the library states it at written values.
`ReadAsks` is sufficient for the acceptance; that it is necessary is not stated, and its field
`opened` is not: the text of `readOld` has no test that no column is left. Through the field `once`
of `TreeAsks` it holds a hypothesis on the book's state: a tree that may be opened at one list only
has not been opened. Nothing on what is read. Of y the theorem says only that there is one. Nothing
on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.ReadSymbols
import Johnson.Desc.K12.Honest.ReadRows
import OnBytes.Slice.BlkOpenN

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes
open VerifiableInference.Desc
open Tw.L9 (Col SwIn readOld openOne)

/-- The places in the book of the trees to be opened: the first components of `places`, each once,
increasing. -/
def treesAt (places : Array (Nat × Nat)) : List Nat := listOfT (places.map (·.1)).toList

/-- The hypothesis of `read_yes_trees`. `places`: the places of the messages asked for
(`singleRowsOracles i.old`). `TT t` and `cs t`: the tree at place t of the book and its dealt
columns. -/
structure ReadAsks (i : SwIn) (pos : Positions) (places : Array (Nat × Nat)) (TT : Nat → Tree)
    (cs : Nat → List Col) : Prop where
  placed : ((singleRowsOracles i.old).mapM fun o => i.book.place[o]?) = some places
  whole : ((treesAt places).all fun t =>
    ((i.book.trees[t]?).map (·.parts)).getD #[] |>.all (singleRowsOracles i.old).contains) = true
  tree : ∀ t ∈ treesAt places, TreeAsks i.st i.firstTree pos i.book t (TT t) (cs t)
  opened : i.opened = (treesAt places).flatMap cs
  oracle : ∀ o ∈ (singleRowsOracles i.old).toList, ∃ x, i.st.oracles[o]? = some x
  listed : ∀ x ∈ pos.all.toList, x ∈ pos.draws.toList
  shape : Own.shapeFits i.old = true
  masks : i.old.masks = 2
  noKept : i.old.keptRows = 0
  kept : ∀ w, w < i.old.layout.members.size → i.old.layout.kept.getD w false = false
  main : ∀ w (hw : w < i.old.layout.members.size) (x : Oracle),
    i.st.oracles[i.old.layout.members[w]]? = some x → x.shape.mainRows = 0 ∨
      ∃ f, i.old.layout.mainFirst.getD w none = some f ∧ f + x.shape.mainRows ≤ 2 ^ i.old.layout.k
  mask : ∀ w (hw : w < i.old.layout.members.size) (x : Oracle),
    i.st.oracles[i.old.layout.members[w]]? = some x → x.shape.maskRows = 0 ∨
      ∃ f, i.old.layout.maskFirst.getD w none = some f ∧ f + x.shape.maskRows ≤ 2 ^ i.old.layout.h
  fresh : ∀ x : Oracle, i.st.oracles[i.old.fresh]? = some x →
    x.shape.maskRows = 2 ^ i.old.layout.h

/-- **The reading accepts.** Under `ReadAsks`, `readOld i pos` returns the book with one list more
counted at each opened tree, no column, and some y. -/
theorem read_yes_trees (i : SwIn) (pos : Positions) (places : Array (Nat × Nat)) (TT : Nat → Tree)
    (cs : Nat → List Col) (A : ReadAsks i pos places TT cs) :
    ∃ y, readOld i pos = .ok (bump i.book (treesAt places), [], y) := by
  have hids : singleRowsOracles i.old = i.old.layout.members.push i.old.fresh := by
    unfold singleRowsOracles
    rw [A.masks]
    rfl
  obtain ⟨z1, z2⟩ := OnBytes.Slice.array_mapM_inv _ _ _ A.placed
  have hnd : (treesAt places).Nodup := by
    unfold treesAt
    rw [listOfT_eq]
    exact (Fmt.listOf_incr _).imp fun h => Nat.ne_of_lt h
  -- the loop over the trees
  have hloop := open_all i.st i.firstTree pos i.book TT cs (treesAt places) i.book [] #[] hnd A.tree
    fun _ _ => rfl
  rw [List.append_nil, ← A.opened] at hloop
  -- each message's symbols are found
  have hsym : ∀ k (hk : k < ((singleRowsOracles i.old).zip places).size), ∃ (x : Oracle)
      (c : Array Column), i.st.oracles[((singleRowsOracles i.old).zip places)[k].1]? = some x ∧
      Own.symbolsAt i.st i.book pos ((treesAt places).map fun t => laidBy pos t (TT t) (cs t))
        ((singleRowsOracles i.old).zip places)[k].1 ((singleRowsOracles i.old).zip places)[k].2 =
        some c ∧ c.size = pos.all.size ∧
      ∀ col ∈ c.toList, col.main.size = x.shape.mainRows ∧ col.mask.size = x.shape.maskRows := by
    intro k hk
    have hk1 : k < (singleRowsOracles i.old).size := by
      rw [Array.size_zip] at hk
      omega
    have hk2 : k < places.size := by
      rw [Array.size_zip] at hk
      omega
    rw [Array.getElem_zip]
    obtain ⟨x, hx⟩ := A.oracle _ (Array.mem_toList_iff.2 (Array.getElem_mem hk1))
    have hp : (places[k]).1 ∈ treesAt places := by
      unfold treesAt
      rw [listOfT_eq, Fmt.listOf_mem, Array.toList_map]
      exact List.mem_map.2 ⟨_, Array.mem_toList_iff.2 (Array.getElem_mem hk2), rfl⟩
    obtain ⟨c, e1, e2, e3⟩ := symbols_there i.st i.firstTree pos i.book TT cs (treesAt places) _
      places[k] x hp (A.tree _ hp) hx A.listed
    exact ⟨x, c, hx, e1, e2, e3⟩
  obtain ⟨bs, hbs, -, -⟩ := mapM_all
    (fun y : Nat × Nat × Nat => Own.symbolsAt i.st i.book pos
      ((treesAt places).map fun t => laidBy pos t (TT t) (cs t)) y.1 y.2) (fun _ => True)
    ((singleRowsOracles i.old).zip places).toList fun y hy => by
      obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.1 hy)
      obtain ⟨_, c, _, e, _⟩ := hsym k hk
      exact ⟨c, e, trivial⟩
  have hop : (((singleRowsOracles i.old).zip places).mapM fun y => Own.symbolsAt i.st i.book pos
      ((treesAt places).map fun t => laidBy pos t (TT t) (cs t)) y.1 y.2) = some bs.toArray := by
    rw [Array.mapM_eq_mapM_toList, hbs]
    rfl
  obtain ⟨w1, w2⟩ := OnBytes.Slice.array_mapM_inv _ _ _ hop
  have hzs : ((singleRowsOracles i.old).zip places).size = i.old.layout.members.size + 1 := by
    rw [Array.size_zip, z1, Nat.min_self, hids, Array.size_push]
  -- the found symbols fit the layout
  have hat : ∀ w (hw : w < i.old.layout.members.size + 1), ∃ (x : Oracle) (c : Array Column),
      i.st.oracles[(i.old.layout.members.push i.old.fresh)[w]'(by simpa using hw)]? = some x ∧
      bs.toArray[w]? = some c ∧ c.size = pos.all.size ∧
      ∀ col ∈ c.toList, col.main.size = x.shape.mainRows ∧ col.mask.size = x.shape.maskRows := by
    intro w hw
    obtain ⟨x, c, a1, a2, a3, a4⟩ := hsym w (by rw [hzs]; exact hw)
    refine ⟨x, c, ?_, by rw [← w2 w (by rw [hzs]; exact hw)]; exact a2, a3, a4⟩
    rw [Array.getElem_zip] at a1
    simpa [hids] using a1
  have hin : ∀ (w : Nat) (k : Nat) (col : Column) (c : Array Column), bs.toArray[w]? = some c →
      (bs.toArray[w]?).bind (·[k]?) = some col → col ∈ c.toList := by
    intro w k col c h1 h2
    rw [h1, Option.bind_some] at h2
    exact Array.mem_toList_iff.2 (Array.mem_of_getElem? h2)
  have hfit : ColsFit i.old.layout bs.toArray pos.all.size := by
    refine ⟨fun w hw k hk => ?_, A.kept, fun w hw k col h => ?_, fun w hw k col h => ?_,
      fun k col h => ?_⟩
    · obtain ⟨_, c, _, a2, a3, _⟩ := hat w (Nat.lt_succ_of_le hw)
      exact ⟨c[k]'(by rw [a3]; exact hk), by
        rw [a2, Option.bind_some, Array.getElem?_eq_getElem (by rw [a3]; exact hk)]⟩
    · obtain ⟨x, c, a1, a2, _, a4⟩ := hat w (Nat.lt_succ_of_lt hw)
      rw [Array.getElem_push_lt hw] at a1
      rw [(a4 col (hin w k col c a2 h)).1]
      exact A.main w hw x a1
    · obtain ⟨x, c, a1, a2, _, a4⟩ := hat w (Nat.lt_succ_of_lt hw)
      rw [Array.getElem_push_lt hw] at a1
      rw [(a4 col (hin w k col c a2 h)).2]
      exact A.mask w hw x a1
    · obtain ⟨x, c, a1, a2, _, a4⟩ := hat i.old.layout.members.size (Nat.lt_succ_self _)
      rw [Array.getElem_push_eq] at a1
      rw [(a4 col (hin _ k col c a2 h)).2]
      exact A.fresh x a1
  obtain ⟨y, hy⟩ := rows_there i.old bs.toArray pos.all.size A.shape A.masks A.noKept hfit
  refine ⟨y, ?_⟩
  have hw' : (!((listOfT (places.map (·.1)).toList).all fun t =>
      ((i.book.trees[t]?).map (·.parts)).getD #[] |>.all (singleRowsOracles i.old).contains)) =
      false := by
    have k := A.whole
    unfold treesAt at k
    rw [k]
    rfl
  have hloop' : (listOfT (places.map (·.1)).toList).foldlM
      (fun s t => openOne i.st i.firstTree pos i.book t s) (i.book, i.opened, #[]) =
      .ok (bump i.book (treesAt places), [],
        #[] ++ ((treesAt places).map fun t => laidBy pos t (TT t) (cs t)).toArray) := hloop
  have hop' : (((singleRowsOracles i.old).zip places).mapM fun y => Own.symbolsAt i.st i.book pos
      (#[] ++ ((treesAt places).map fun t => laidBy pos t (TT t) (cs t)).toArray).toList y.1 y.2) =
      some bs.toArray := by
    simpa using hop
  unfold readOld
  simp only [A.placed, hw', Bool.false_eq_true, if_false, hloop', hop', hy]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.read_yes_trees
#print axioms ProofFile.Honest.K12.treesAt
#print axioms ProofFile.Honest.K12.ReadAsks
