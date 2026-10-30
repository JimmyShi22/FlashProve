-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/ReadSymbols.lean: one step of the reading of the old rows in a code switch,
at a list of trees: each oracle message's symbols are found in what the loop over the trees has set
aside (`Own.symbolsAt`, Johnson/Desc/Own/Symbols.lean, at `laidBy`,
Johnson/Desc/K12/Honest/ReadTrees.lean), at a tree as long as the positions' range and at a shorter
one. The reading is `Tw.L9.readOld` (Johnson/Top/H0/Tw/L9/Switch.lean), by which a code switch of a
proximity test reads the symbols of its old rows out of dealt columns: it finds the places of the
rows' oracle messages, opens their trees one after the other, finds each message's symbols and makes
the rows' symbols of them by the layout. Johnson/Desc/K12/Honest/ReadWhole.lean calls
`symbols_there` and `mapM_all` for the whole reading. Statements and proofs, whatever words the
columns hold. General in the statement, the book, the positions, the trees and the columns. The file
does not depend on the frame for an honest side (Johnson/Desc/ProofFile/Honest/Frame.lean).

In the list: S is the statement (`Statement`, OnBytes/Iop/Ground.lean), which holds the oracle
messages, each under a number; o is such a number and x the message under it. B0 is the book
(`TreeBook`, Ground.lean), which holds the trees, each at a place. pos (`Positions`, Ground.lean)
has a range (`logN`), the sampled positions (`draws`) and the listed positions (`all`: the list by
which trees are opened). A tree's own list is `Blk.ownList` (Ground.lean): the listed positions at a
tree as long as the range; at any other tree the sampled positions modulo the tree's length, each
once, increasing. ts is a list of places: the opened trees. TT and cs are free parameters: `TT t` is
a tree and `cs t` a list of dealt columns (`Col`, Switch.lean: a key, a position and a list of
words). `laidBy pos t (TT t) (cs t)` is the place t, the own list of `TT t` and the words of the
columns `cs t`. p is a pair: `p.1` is the place of a tree, and `p.2` is read as the number of a part
of that tree.

  `symbols_there`: the message's tree is among the opened ones, with `TreeAsks` · the message is in
    the statement · every listed position is among the sampled ones ⟹ its symbols are found: one
    column for each listed position, with as many main and mask symbols as the message has rows. The
    value found is `Own.symbolsAt` at S, B0, pos, the list of `laidBy` over ts, o and p
  `here_there`: each listed position has its place in the tree's own list: where every listed
    position is among the sampled ones, `Own.whereOpened` (Symbols.lean) at the i-th listed position
    returns an index below that list's length. At every tree, whatever its length
  `find_cols`: what was set aside for a tree of the list is found under the tree's place: for u in
    ts, the search for an entry whose first component is u, in the list of `laidBy` over ts, returns
    `laidBy` at u
  `mapM_all`: where a function f into `Option` has, at each member of a list, a value with the
    property Q, `mapM f` of the list is `some` of a list of the same length whose members all have Q

By what. `mapM_all` and `find_cols` go by recursion on the list. `here_there` unfolds
`Own.whereOpened` and `Blk.ownList`. At a tree as long as the range the index is i. At any other
tree the position modulo the tree's length is in the own list by `listOfT_eq`
(OnBytes/Chain/Draws.lean) and `Fmt.listOf_mem` (Fmt/Rules6Laws.lean); `OnBytes.Means.find_of_mem`
and `OnBytes.Means.find_some` (Johnson/Desc/Means/Layout.lean), called at a layout whose members are
that list, give the index and its bound. `symbols_there` unfolds `Own.symbolsAt`, rewrites by the
field `there` of `TreeAsks`, by `hx` and by `find_cols`, and calls `mapM_all` with `here_there`. The
first clause of the field `dealt` gives that a column was set aside at the index. The sizes follow
by unfolding `Blk.columnOf` (Ground.lean).

Hypotheses. At `symbols_there`: `hp`: `p.1` is in ts. `A`:
`TreeAsks S F pos B0 p.1 (TT p.1) (cs p.1)` (ReadTrees.lean); of its fields the proof uses that the
tree at place `p.1` of the book is `TT p.1` (`there`) and that `cs p.1` has as many columns as that
tree's own list has entries (`dealt`). `hx`: x is the oracle message under the number o in S.
`hall`: every listed position is among the sampled ones.

Limits. One step of the reading only: the step at which `readOld` calls `Own.symbolsAt` for each
message asked for. The finding of the places, the loop over the trees (ReadTrees.lean), the making
of the rows' symbols by the layout (Johnson/Desc/K12/Honest/ReadRows.lean) and the whole reading
(ReadWhole.lean) are not in this file. The hypotheses of `symbols_there` are proved at no arguments
in this file. That p is the place of the message o in the book (`B0.place`) is no hypothesis:
nothing here ties p to o. Of the columns found `symbols_there` states their number and their sizes
only. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.ReadTrees
import Johnson.Desc.Means.Layout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes
open VerifiableInference.Desc
open Tw.L9 (Col)

theorem mapM_all {α β : Type} (f : α → Option β) (Q : β → Prop) : ∀ l : List α,
    (∀ a ∈ l, ∃ b, f a = some b ∧ Q b) →
    ∃ bs, l.mapM f = some bs ∧ bs.length = l.length ∧ ∀ b ∈ bs, Q b
  | [], _ => ⟨[], by simp, rfl, by simp⟩
  | a :: l, h => by
    obtain ⟨b, hb, qb⟩ := h a (List.mem_cons_self ..)
    obtain ⟨bs, hbs, hl, hq⟩ := mapM_all f Q l fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨b :: bs, by rw [List.mapM_cons, hb, hbs]; rfl, by simp [hl], fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact qb
    · exact hq y hy

theorem find_cols (pos : Positions) (TT : Nat → Tree) (cs : Nat → List Col) (u : Nat) :
    ∀ ts : List Nat, u ∈ ts →
    (ts.map fun t => laidBy pos t (TT t) (cs t)).find? (·.1 == u) =
      some (laidBy pos u (TT u) (cs u))
  | [], h => by cases h
  | t :: ts, h => by
    rw [List.map_cons, List.find?_cons]
    by_cases e : t = u
    · subst e
      simp [laidBy]
    · have e' : ((laidBy pos t (TT t) (cs t)).1 == u) = false := by
        simpa [laidBy] using e
      rw [e']
      exact find_cols pos TT cs u ts ((List.mem_cons.1 h).resolve_left fun k => e k.symm)

/-- Each listed position has its place in the tree's own list (`Blk.ownList`): `Own.whereOpened` at
the i-th listed position returns an index below that list's length. `hall`: every listed position is
among the sampled ones. -/
theorem here_there (pos : Positions) (T : Tree)
    (hall : ∀ x ∈ pos.all.toList, x ∈ pos.draws.toList) (i : Nat) (hi : i < pos.all.size) :
    ∃ here, Own.whereOpened (T.shape.logN == pos.logN) (Blk.ownList T pos) (2 ^ T.shape.logN) i
      (pos.all.getD i 0) = some here ∧ here < (Blk.ownList T pos).size := by
  unfold Own.whereOpened Blk.ownList
  by_cases e : (T.shape.logN == pos.logN) = true
  · rw [if_pos e, if_pos e]
    exact ⟨i, rfl, hi⟩
  · rw [if_neg e, if_neg e]
    have hx : pos.all.getD i 0 ∈ pos.all.toList := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
      exact Array.mem_toList_iff.2 (Array.getElem_mem hi)
    have hm : pos.all.getD i 0 % 2 ^ T.shape.logN ∈
        listOfT (pos.draws.map (· % 2 ^ T.shape.logN)).toList := by
      rw [listOfT_eq, Fmt.listOf_mem, Array.toList_map]
      exact List.mem_map.2 ⟨_, hall _ hx, rfl⟩
    obtain ⟨here, hh⟩ := OnBytes.Means.find_of_mem
      (L := { members := (listOfT (pos.draws.map (· % 2 ^ T.shape.logN)).toList).toArray }) hm
    exact ⟨here, hh, (OnBytes.Means.find_some hh).1⟩

/-- **A message's symbols are found.** `Own.symbolsAt` at the list of `laidBy` over ts returns one
column for each listed position, each of the sizes that the message x states. `p.1`: the place of
the message's tree in the book. `p.2`: read as the number of a part of that tree. -/
theorem symbols_there (S : Statement) (F : Nat) (pos : Positions) (B0 : TreeBook) (TT : Nat → Tree)
    (cs : Nat → List Col) (ts : List Nat) (o : Nat) (p : Nat × Nat) (x : Oracle) (hp : p.1 ∈ ts)
    (A : TreeAsks S F pos B0 p.1 (TT p.1) (cs p.1)) (hx : S.oracles[o]? = some x)
    (hall : ∀ x ∈ pos.all.toList, x ∈ pos.draws.toList) :
    ∃ c : Array Column,
      Own.symbolsAt S B0 pos (ts.map fun t => laidBy pos t (TT t) (cs t)) o p = some c ∧
      c.size = pos.all.size ∧
      ∀ col ∈ c.toList, col.main.size = x.shape.mainRows ∧ col.mask.size = x.shape.maskRows := by
  unfold Own.symbolsAt
  rw [A.there, hx, find_cols pos TT cs p.1 ts hp]
  dsimp only
  obtain ⟨bs, h1, h2, h3⟩ := mapM_all
    (fun i => (Own.whereOpened ((TT p.1).shape.logN == pos.logN)
        (laidBy pos p.1 (TT p.1) (cs p.1)).2.1 (2 ^ (TT p.1).shape.logN) i
        (pos.all.getD i 0)).bind fun here =>
      ((laidBy pos p.1 (TT p.1) (cs p.1)).2.2[here]?).map
        (Blk.columnOf x (((TT p.1).shape.mainSymbols.extract 0 p.2).foldl (· + ·) 0)
          ((TT p.1).shape.mainWidth + ((TT p.1).shape.maskSymbols.extract 0 p.2).foldl (· + ·) 0)))
    (fun col => col.main.size = x.shape.mainRows ∧ col.mask.size = x.shape.maskRows)
    (List.range pos.all.size) fun i hi => by
      obtain ⟨here, e1, e2⟩ := here_there pos (TT p.1) hall i (List.mem_range.1 hi)
      have e3 : here < (laidBy pos p.1 (TT p.1) (cs p.1)).2.2.size := by
        show here < ((cs p.1).map fun y => y.2.2.toArray).toArray.size
        rw [List.size_toArray, List.length_map, A.dealt.1]
        exact e2
      refine ⟨_, by
        show (Own.whereOpened _ (Blk.ownList (TT p.1) pos) _ i _).bind _ = _
        rw [e1, Option.bind_some, Array.getElem?_eq_getElem e3]
        rfl, ?_, ?_⟩ <;> simp [Blk.columnOf]
  refine ⟨bs.toArray, by rw [h1]; rfl, by simp [h2], fun col hc => h3 col (by simpa using hc)⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.mapM_all
#print axioms ProofFile.Honest.K12.find_cols
#print axioms ProofFile.Honest.K12.here_there
#print axioms ProofFile.Honest.K12.symbols_there
