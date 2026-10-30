-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/Read.lean: THE READING OF THE OLD ROWS RETURNS (`readOld`,
Johnson/Top/H0/Tw/K2/Switch.lean) wherever premises on the make of what it is handed hold; the book
and the columns that it leaves are terms; the symbols are as many as positions times rows. One
statement, `readOld_returns`, with its proof and lemmas, over Returns/ReadOpen.lean,
Returns/ReadSymbols.lean, Returns/ReadLay.lean and the library's `readOld_of`
(Johnson/Top/H0/Tw/K2C/AsksWhole.lean).

  `idsOf`, `placesOf`, `treesOf`, `shapeAt`   the messages that are opened; each one's place in the
                    book; the trees that hold them, each once, rising; a message's shape
  `ReadFits`        ALL PREMISES: two masks · the carried rows' own numbers fit each other (five
                    facts) · every opened message has a place in the book and stands in the
                    statement · an opened tree holds opened messages alone · the trees open one
                    after the other at the handed columns (`AllOpen`) · each member's rows fit the
                    layout's two tables · the kept members' main rows add up to the carried rows'
                    count · the fresh mask has 2 ^ h mask rows
  `mapM_map`, `allOpen_tree`, `trees_nodup`, `mem_trees`   tools
  `readOld_returns`   the law; beside `ReadFits`: every listed position is among the draws (of the
                    positions that a round's draws make: `ofDraws_all`, Returns/ReadSymbols.lean)

Limits. No member of `ReadFits` is typed here. Nothing on the symbols' values. That a group's layout
as the closing lays it meets `fits`, `keptRows` and `fresh` is not shown here (`layFits_of_close`,
Returns/ClosedReached.lean). `masks` and `keptRows` say again what the step's other premises say of
the same numbers. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.ReadLay
import Johnson.Desc.K2.Honest.Returns.ReadOpen
import Johnson.Desc.K2.Honest.Returns.ReadSymbols
import Johnson.Top.H0.Tw.K2C.AsksWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open _root_.Tw.K2 (SwIn readOld)
open VerifiableInference.Desc.First.K2 (readOld_of)
open VerifiableInference.Desc.LinkJoin (ColFits keptCount colAt)
open VerifiableInference.Desc.Own (shapeFits symbolsAt)

/-- The messages that are opened. -/
def idsOf (i : SwIn) : Array Nat := singleRowsOracles i.old

/-- Each one's place in the book: its tree, and its number among the tree's parts. -/
def placesOf (i : SwIn) : Array (Nat × Nat) := (idsOf i).map fun o => i.book.place.getD o (0, 0)

/-- The trees that hold them: each once, rising. -/
def treesOf (i : SwIn) : List Nat := listOfT ((placesOf i).map (·.1)).toList

/-- A message's shape in the statement. -/
def shapeAt (i : SwIn) (o : Nat) : OracleShape := (i.st.oracles.getD o default).shape

/-- **All premises.** -/
structure ReadFits (i : SwIn) (pos : Positions) : Prop where
  masks : i.old.masks = 2
  challenges : i.old.gamma.length = i.old.layout.k
  maskVars : i.old.layout.h ≤ i.old.layout.k
  keptSize : i.old.layout.kept.size = i.old.layout.members.size
  mainSize : i.old.layout.mainFirst.size = i.old.layout.members.size
  maskSize : i.old.layout.maskFirst.size = i.old.layout.members.size
  placed : ∀ o ∈ (idsOf i).toList, o < i.book.place.size
  stated : ∀ o ∈ (idsOf i).toList, o < i.st.oracles.size
  own : ∀ t ∈ treesOf i, ∀ tree, i.book.trees[t]? = some tree →
    ∀ q ∈ tree.parts.toList, q ∈ (idsOf i).toList
  opens : AllOpen i.st i.firstTree pos i.book (treesOf i) i.opened
  fits : ∀ w (hw : w < i.old.layout.members.size), ColFits i.old.layout w
    (shapeAt i i.old.layout.members[w]).mainRows (shapeAt i i.old.layout.members[w]).maskRows
    (2 ^ i.old.layout.k) (2 ^ i.old.layout.h)
  keptRows : keptCount i.old.layout (fun w => (shapeAt i (i.old.layout.members.getD w 0)).mainRows)
    (List.range i.old.layout.members.size) = i.old.keptRows
  fresh : (shapeAt i i.old.fresh).maskRows = 2 ^ i.old.layout.h

/-- A loop in which every step answers, as a plain image. -/
theorem mapM_map {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ l : List α, (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => by simp
  | a :: l, h => by
    rw [List.mapM_cons, h a List.mem_cons_self,
      mapM_map f g l fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

/-- A tree of the list is in the book. -/
theorem allOpen_tree (S : Statement) (firstTree : Nat) (pos : Positions) (B0 : TreeBook) :
    ∀ (ts : List Nat) (c : List _root_.Tw.K2.Col) (t : Nat), t ∈ ts →
      AllOpen S firstTree pos B0 ts c → ∃ tree, B0.trees[t]? = some tree
  | t' :: ts, c, t, hm, hA => by
    obtain ⟨tree, h0, _, _, _, _, _, hrest⟩ := hA
    rcases List.mem_cons.1 hm with h | h
    · exact ⟨tree, h ▸ h0⟩
    · exact allOpen_tree S firstTree pos B0 ts _ t h hrest

theorem trees_nodup (i : SwIn) : (treesOf i).Nodup := by
  unfold treesOf
  rw [listOfT_eq]
  exact (Fmt.listOf_incr _).imp fun h => Nat.ne_of_lt h

/-- The tree of an opened message is among the trees. -/
theorem mem_trees (i : SwIn) {w : Nat} (hw : w < (placesOf i).size) :
    (placesOf i)[w].1 ∈ treesOf i := by
  unfold treesOf
  rw [listOfT_eq]
  refine (Fmt.listOf_mem _ _).2 ?_
  rw [Array.toList_map]
  exact List.mem_map.2 ⟨_, Array.getElem_mem_toList hw, rfl⟩

/-- **The reading of the old rows returns.** -/
theorem readOld_returns (i : SwIn) (pos : Positions) (F : ReadFits i pos)
    (hall : ∀ x ∈ pos.all.toList, x ∈ pos.draws.toList) :
    ∃ y, readOld i pos = .ok (bookAfter (treesOf i) i.book,
        leftAfter pos i.book (treesOf i) i.opened, y) ∧ y.size = pos.all.size * i.old.rows := by
  have hso : idsOf i = i.old.layout.members.push i.old.fresh := by
    unfold idsOf singleRowsOracles
    simp [F.masks]
  have hsz : (idsOf i).size = i.old.layout.members.size + 1 := by rw [hso, Array.size_push]
  have hpz : (placesOf i).size = (idsOf i).size := by unfold placesOf; rw [Array.size_map]
  -- the places
  have hPlaces : (idsOf i).mapM (fun o => i.book.place[o]?) = some (placesOf i) := by
    rw [Array.mapM_eq_mapM_toList, mapM_map _ (fun o => i.book.place.getD o (0, 0)) _ fun o ho => by
      show i.book.place[o]? = some (i.book.place.getD o (0, 0))
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (F.placed o ho), Option.getD_some]]
    show some _ = some _
    congr 1
    apply Array.toList_inj.1
    unfold placesOf
    simp
  -- an opened tree holds opened messages alone
  have hAll : ((treesOf i).all fun t =>
      ((i.book.trees[t]?).map (·.parts)).getD #[] |>.all (idsOf i).contains) = true := by
    rw [List.all_eq_true]
    intro t ht
    cases e : i.book.trees[t]? with
    | none => simp
    | some tree =>
      show tree.parts.all (idsOf i).contains = true
      rw [← Array.all_toList, List.all_eq_true]
      intro q hq
      have := F.own t ht tree e q hq
      simpa using this
  -- the trees
  have hOpen := open_returns i.st i.firstTree pos i.book (treesOf i) i.book i.opened #[]
    (trees_nodup i) (fun _ _ => rfl) F.opens
  -- each message's symbols
  have hSym : ∀ w (hw : w < (idsOf i).size), ∃ out,
      symbolsAt i.st i.book pos (takenAfter pos i.book (treesOf i) i.opened) (idsOf i)[w]
        ((placesOf i)[w]'(hpz ▸ hw)) = some out ∧ ∀ n < pos.all.size, ∃ c, out[n]? = some c ∧
          c.main.size = (shapeAt i (idsOf i)[w]).mainRows ∧
          c.mask.size = (shapeAt i (idsOf i)[w]).maskRows := by
    intro w hw
    have hm := mem_trees i (hpz ▸ hw : w < (placesOf i).size)
    obtain ⟨tree, ht⟩ := allOpen_tree _ _ _ _ _ _ _ hm F.opens
    obtain ⟨cs, hf, hz⟩ := taken_find _ _ _ _ _ _ _ hm F.opens
    have hlt := F.stated _ (Array.getElem_mem_toList hw)
    have hx : i.st.oracles[(idsOf i)[w]]? = some (i.st.oracles.getD (idsOf i)[w] default) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some]
    rw [← ownAt_eq ht] at hf hz
    exact symbolsAt_returns ht hx hf hz hall
  have hz2 : ((idsOf i).zip (placesOf i)).size = (idsOf i).size := by
    rw [Array.size_zip, hpz, Nat.min_self]
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (_root_.Tw.K2.mapM_some
    (fun y : Nat × Nat × Nat =>
      symbolsAt i.st i.book pos (takenAfter pos i.book (treesOf i) i.opened) y.1 y.2)
    ((idsOf i).zip (placesOf i)).toList fun y hy => by
      obtain ⟨w, hw, rfl⟩ := List.getElem_of_mem hy
      have hw' : w < (idsOf i).size := by
        rw [Array.length_toList, hz2] at hw
        exact hw
      obtain ⟨out, ho, _⟩ := hSym w hw'
      rw [Array.getElem_toList, Array.getElem_zip]
      show (symbolsAt _ _ _ _ _ _).isSome = true
      rw [ho]
      rfl)
  have hSymbols : ((idsOf i).zip (placesOf i)).mapM (fun y =>
      symbolsAt i.st i.book pos ((#[] : Array Taken) ++
        (takenAfter pos i.book (treesOf i) i.opened).toArray).toList y.1 y.2) =
      some r.toArray := by
    have et : ((#[] : Array Taken) ++ (takenAfter pos i.book (treesOf i) i.opened).toArray).toList =
        takenAfter pos i.book (treesOf i) i.opened := by simp
    rw [et, Array.mapM_eq_mapM_toList, hr]
    rfl
  obtain ⟨_, k2⟩ := OnBytes.Slice.list_mapM_inv _ _ r hr
  -- a column of each message at each position
  have hCol : ∀ w (hw : w < (idsOf i).size), ∀ n < pos.all.size, ∃ c,
      colAt r.toArray n w = some c ∧ c.main.size = (shapeAt i (idsOf i)[w]).mainRows ∧
        c.mask.size = (shapeAt i (idsOf i)[w]).maskRows := by
    intro w hw n hn
    obtain ⟨out, ho, hc⟩ := hSym w hw
    obtain ⟨c, c1, c2, c3⟩ := hc n hn
    have hw2 : w < ((idsOf i).zip (placesOf i)).toList.length := by
      rw [Array.length_toList, hz2]
      exact hw
    have h3 := k2 w hw2
    rw [Array.getElem_toList, Array.getElem_zip] at h3
    refine ⟨c, ?_, c2, c3⟩
    unfold colAt
    rw [List.getElem?_toArray, ← h3]
    show (symbolsAt _ _ _ _ _ _).bind _ = _
    rw [ho]
    exact c1
  -- the laying
  have hs : shapeFits i.old = true := by
    unfold shapeFits
    simp [F.challenges, F.maskVars, F.keptSize, F.mainSize, F.maskSize]
  obtain ⟨y, hy, hsize⟩ := rowsSymbols_returns (opened := r.toArray) F.masks hs _ F.keptRows
    pos.all.size fun n hn =>
      { members := fun w hw => by
          have hlt := List.mem_range.1 hw
          obtain ⟨c, c1, c2, c3⟩ := hCol w (by omega) n hn
          have eo : (idsOf i)[w]'(by omega) = i.old.layout.members[w] := by
            simp only [hso]
            exact Array.getElem_push_lt hlt
          have eg : i.old.layout.members.getD w 0 = i.old.layout.members[w] := by
            rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
            rfl
          rw [eo] at c2 c3
          refine ⟨c, c1, ?_, ?_⟩
          · show c.main.size = (shapeAt i (i.old.layout.members.getD w 0)).mainRows
            rw [c2, eg]
          · rw [c2, c3]
            exact F.fits w hlt
        fresh := by
          obtain ⟨c, c1, _, c3⟩ := hCol i.old.layout.members.size (by omega) n hn
          have eo : (idsOf i)[i.old.layout.members.size]'(by omega) = i.old.fresh := by
            simp only [hso]
            exact Array.getElem_push_eq
          rw [eo] at c3
          exact ⟨c, c1, c3.trans F.fresh⟩ }
  exact ⟨y, readOld_of ⟨hPlaces, hAll, hOpen, hSymbols, hy⟩, hsize⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.readOld_returns
