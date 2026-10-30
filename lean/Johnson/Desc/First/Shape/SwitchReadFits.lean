-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/SwitchReadFits.lean: WHAT "THE READING OF THE OLD ROWS RETURNS" ASKS
(ReadFits, Johnson/Desc/K2/Honest/Returns/Read.lean), AS TESTS WITH CODE ON SHAPES. General laws;
nothing is evaluated.

What it is for. A code switch reads the rows of the segment that was closed in front of it. The law
readOld_returns of that file leads to a return of that reading from the thirteen fields of ReadFits
and one premise more (every listed position is among the draws), which is not treated here. None of
the thirteen reads a field element. Here twelve are one Bool on the statement's shape, the book's
shape and the make of the carried single rows; the thirteenth, "opens" (AllOpen,
Johnson/Desc/K2/Honest/Returns/ReadOpen.lean), is a Bool on the two shapes, the positions and the
handed columns.

  1 `ids_sh`; `placesOfS` | `places_sh`; `treesOfS` | `trees_sh`: the messages that are opened
    (oldOraclesS, Switch.lean), their places in the book, the trees that hold them: off shapes. A
    message's shape is shapeAtS (SwitchRowsMk.lean).
  2 `colFitsB` | `colFitsB_iff`: "a member fits the layout's two tables" (ColFits,
    Johnson/Desc/First/Link/Law/FrontAnswers.lean), with code.
  3 **`readFitsB a b old`**: THE TWELVE, in the fields' order: masks · challenges · maskVars ·
    keptSize · mainSize · maskSize · placed · stated · own · fits · keptRows · fresh.
  4 `leafGroupsS` | `leafGroups_sh`, `leafOkS` | `leafOk_sh`, `ownAtS` | `ownAt_sh`:
    what "opens" reads of a tree and of the statement.
    **`allOpenB a b firstTree pos`** | **`allOpenB_iff`**: AllOpen's own recursion, with code. Of
    its six clauses at a tree four read the two shapes and the positions' range (the tree is in the
    book · what shares a leaf · a tree with a mask has not been opened · the tree is not longer than
    the range); two read the columns (they are as many as the tree's list; each has its key, its
    position and its width). No clause reads a column's words.
  5 **`readFits_iff`**: ReadFits i pos just if readFitsB accepts at the shapes of i and AllOpen
    holds. `readFits_of_B`: the way from the Bool and AllOpen. **`readFits_iffB`**: just if both
    Bools accept.

Limits. No input is shown here at which a Bool accepts. The tree's list (ownAtS) is made of the
positions
themselves, which are drawn: allOpenB is no function of shapes alone. That a group's layout as the
closing lays it meets fits, keptRows and fresh is not shown. Nothing on the symbols that are read.
Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.K2.Honest.Returns.Read
import Johnson.Desc.First.Shape.Switch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.Ground.Sh (StSh stSh orc_get orc_size tree_get place_size)
open _root_.Tw.K2 (SwIn Col leafOk leafGroups)
open VerifiableInference.Desc.K2.Honest.Returns (idsOf treesOf shapeAt ReadFits AllOpen ownAt)
open VerifiableInference.Desc.LinkJoin (ColFits keptCount)

/-! ## 1 The messages, their places, their trees -/

theorem ids_sh (i : SwIn) : oldOraclesS (singleSh i.old) = idsOf i := rfl

/-- Each opened message's place in the book. -/
def placesOfS (b : Ground.Sh.BookSh) (old : SingleSh) : List (Nat × Nat) :=
  (oldOraclesS old).toList.map fun o => b.place.getD o (0, 0)

theorem places_sh (i : SwIn) :
    placesOfS (Ground.Sh.bookSh i.book) (singleSh i.old) =
      (K2.Honest.Returns.placesOf i).toList := by
  unfold placesOfS K2.Honest.Returns.placesOf
  rw [ids_sh, Array.toList_map]
  apply List.map_congr_left
  intro o _
  show i.book.place.toList.getD o (0, 0) = i.book.place.getD o (0, 0)
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

/-- The trees that hold them: each once, rising. -/
def treesOfS (b : Ground.Sh.BookSh) (old : SingleSh) : List Nat :=
  listOfT ((placesOfS b old).map (·.1))

theorem trees_sh (i : SwIn) :
    treesOfS (Ground.Sh.bookSh i.book) (singleSh i.old) = treesOf i := by
  unfold treesOfS treesOf
  rw [places_sh, Array.toList_map]

/-! ## 2 A member fits the layout's two tables -/

/-- ColFits, with code. -/
def colFitsB (L : GroupLayout) (w nM nZ K H : Nat) : Bool :=
  (nZ == 0 ||
      match L.maskFirst.getD w none with
      | some f => decide (f + nZ ≤ H)
      | none => false) &&
    (L.kept.getD w false || (nM == 0 ||
      match L.mainFirst.getD w none with
      | some f => decide (f + nM ≤ K)
      | none => false))

theorem colFitsB_iff (L : GroupLayout) (w nM nZ K H : Nat) :
    colFitsB L w nM nZ K H = true ↔ ColFits L w nM nZ K H := by
  unfold colFitsB ColFits
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
  refine and_congr (or_congr Iff.rfl ?_) (or_congr Iff.rfl (or_congr Iff.rfl ?_))
  · cases L.maskFirst.getD w none with
    | none => simp
    | some f => simp
  · cases L.mainFirst.getD w none with
    | none => simp
    | some f => simp

/-! ## 3 The twelve -/

/-- **ReadFits but "opens", as one Bool.** a: the statement's shape; b: the book's; old: the make of
the carried single rows. -/
def readFitsB (a : StSh) (b : Ground.Sh.BookSh) (old : SingleSh) : Bool :=
  old.masks == 2 && old.gamma == old.layout.k && decide (old.layout.h ≤ old.layout.k) &&
    old.layout.kept.size == old.layout.members.size &&
    old.layout.mainFirst.size == old.layout.members.size &&
    old.layout.maskFirst.size == old.layout.members.size &&
    ((oldOraclesS old).toList.all fun o => decide (o < b.place.length)) &&
    ((oldOraclesS old).toList.all fun o => decide (o < a.oracles.length)) &&
    ((treesOfS b old).all fun t =>
      match b.trees[t]? with
      | some T => T.parts.all fun q => (oldOraclesS old).toList.contains q
      | none => true) &&
    ((List.range old.layout.members.size).all fun w =>
      colFitsB old.layout w (shapeAtS a (old.layout.members.getD w 0)).mainRows
        (shapeAtS a (old.layout.members.getD w 0)).maskRows (2 ^ old.layout.k)
        (2 ^ old.layout.h)) &&
    keptCount old.layout (fun w => (shapeAtS a (old.layout.members.getD w 0)).mainRows)
      (List.range old.layout.members.size) == old.keptRows &&
    (shapeAtS a old.fresh).maskRows == 2 ^ old.layout.h

/-! ## 4 "Opens" -/

/-- The groups of a tree's sampled parts. -/
def leafGroupsS (a : StSh) (T : Ground.Sh.TreeSh) : List (List Nat) :=
  T.parts.filterMap fun o =>
    (a.oracles[o]?).bind fun x => if x.shape.answers == 0 then none else some x.groups

theorem leafGroups_sh (S : Statement) (tree : Tree) :
    leafGroups S tree = leafGroupsS (stSh S) (Ground.Sh.treeSh tree) := by
  unfold leafGroups leafGroupsS
  show _ = tree.parts.toList.filterMap _
  congr 1
  funext o
  rw [orc_get]
  cases S.oracles[o]? <;> rfl

/-- What shares a leaf: the sampled parts belong to the same groups; in a tree with a mask to one
group at most. -/
def leafOkS (a : StSh) (T : Ground.Sh.TreeSh) : Bool :=
  match leafGroupsS a T with
  | [] => true
  | x :: l => l.all (· == x) && (!T.oneList || decide (x.length ≤ 1))

theorem leafOk_sh (S : Statement) (tree : Tree) :
    leafOk S tree = leafOkS (stSh S) (Ground.Sh.treeSh tree) := by
  unfold leafOk leafOkS
  rw [leafGroups_sh]
  rfl

/-- The list at which the tree at place t is opened; empty where the book has no such tree. -/
def ownAtS (pos : Positions) (b : Ground.Sh.BookSh) (t : Nat) : Array Nat :=
  match b.trees[t]? with
  | some T =>
    if T.shape.logN == pos.logN then pos.all
    else (listOfT (pos.draws.map (· % 2 ^ T.shape.logN)).toList).toArray
  | none => #[]

theorem ownAt_sh (pos : Positions) (B0 : TreeBook) (t : Nat) :
    ownAt pos B0 t = ownAtS pos (Ground.Sh.bookSh B0) t := by
  unfold ownAt ownAtS
  rw [tree_get]
  cases B0.trees[t]? <;> rfl

/-- **AllOpen, with code.** c: the columns that are left when the first tree's turn comes. -/
def allOpenB (a : StSh) (b : Ground.Sh.BookSh) (firstTree : Nat) (pos : Positions) :
    List Nat → List Col → Bool
  | [], _ => true
  | t :: ts, c =>
    (match b.trees[t]? with
      | some T =>
        leafOkS a T && (!T.oneList || T.lists == 0) && decide (T.shape.logN ≤ pos.logN) &&
          decide ((ownAtS pos b t).size ≤ c.length) &&
          Own.colsStand (T.number - firstTree) (T.shape.mainWidth + T.shape.maskWidth)
            (c.take (ownAtS pos b t).size) (ownAtS pos b t).toList
      | none => false) &&
      allOpenB a b firstTree pos ts (c.drop (ownAtS pos b t).size)

theorem allOpenB_iff (S : Statement) (firstTree : Nat) (pos : Positions) (B0 : TreeBook) :
    ∀ (ts : List Nat) (c : List Col),
      allOpenB (stSh S) (Ground.Sh.bookSh B0) firstTree pos ts c = true ↔
        AllOpen S firstTree pos B0 ts c
  | [], _ => ⟨fun _ => trivial, fun _ => rfl⟩
  | t :: ts, c => by
    unfold allOpenB AllOpen
    rw [Bool.and_eq_true, allOpenB_iff S firstTree pos B0 ts, tree_get, ← ownAt_sh]
    cases e : B0.trees[t]? with
    | none =>
      constructor
      · rintro ⟨h, -⟩
        exact nomatch h
      · rintro ⟨_, h, -⟩
        exact nomatch h
    | some tree =>
      show ((leafOkS (stSh S) (Ground.Sh.treeSh tree) && (!tree.oneList || tree.lists == 0) &&
        decide (tree.shape.logN ≤ pos.logN) && decide ((ownAt pos B0 t).size ≤ c.length) &&
        Own.colsStand (tree.number - firstTree) (tree.shape.mainWidth + tree.shape.maskWidth)
          (c.take (ownAt pos B0 t).size) (ownAt pos B0 t).toList) = true ∧ _) ↔ _
      rw [← leafOk_sh]
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
        decide_eq_true_eq]
      constructor
      · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
        refine ⟨tree, rfl, h1, fun ho => ?_, h3, h4, h5, h6⟩
        rcases h2 with h2 | h2
        · rw [ho] at h2
          exact nomatch h2
        · exact h2
      · rintro ⟨tree', e', h1, h2, h3, h4, h5, h6⟩
        obtain rfl := Option.some.inj e'
        refine ⟨⟨⟨⟨⟨h1, ?_⟩, h3⟩, h4⟩, h5⟩, h6⟩
        cases ho : tree.oneList with
        | false => exact Or.inl rfl
        | true => exact Or.inr (h2 ho)

/-! ## 5 ReadFits -/

/-- **ReadFits just if the Bool on the three shapes accepts and the trees open.** -/
theorem readFits_iff (i : SwIn) (pos : Positions) :
    ReadFits i pos ↔
      readFitsB (stSh i.st) (Ground.Sh.bookSh i.book) (singleSh i.old) = true ∧
        AllOpen i.st i.firstTree pos i.book (treesOf i) i.opened := by
  have eS : ∀ o, shapeAtS (stSh i.st) o = shapeAt i o := fun o => (shapeAt_sh i.st o).symm
  have eM : ∀ w (hw : w < i.old.layout.members.size),
      i.old.layout.members.getD w 0 = i.old.layout.members[w] := fun w hw => by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hw]
    rfl
  unfold readFitsB
  rw [trees_sh, ids_sh]
  simp only [eS, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, colFitsB_iff, place_size, orc_size]
  constructor
  · intro F
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨F.masks, F.challenges⟩, F.maskVars⟩, F.keptSize⟩, F.mainSize⟩,
      F.maskSize⟩, F.placed⟩, F.stated⟩, fun t ht => ?_⟩, fun w hw => ?_⟩, F.keptRows⟩, F.fresh⟩,
      F.opens⟩
    · rw [tree_get]
      cases e : i.book.trees[t]? with
      | none => rfl
      | some tree =>
        show (tree.parts.toList.all fun q => (idsOf i).toList.contains q) = true
        rw [List.all_eq_true]
        intro q hq
        exact List.contains_iff_mem.2 (F.own t ht tree e q hq)
    · have hw' : w < i.old.layout.members.size := hw
      have := F.fits w hw'
      rw [← eM w hw'] at this
      exact this
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, ho⟩
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun t ht tree e q hq => ?_, ho, fun w hw => ?_, h11,
      h12⟩
    · have := h9 t ht
      rw [tree_get, e] at this
      have h' : (tree.parts.toList.all fun q => (idsOf i).toList.contains q) = true := this
      exact List.contains_iff_mem.1 (List.all_eq_true.1 h' q hq)
    · have h' : ColFits i.old.layout w (shapeAt i (i.old.layout.members.getD w 0)).mainRows
          (shapeAt i (i.old.layout.members.getD w 0)).maskRows (2 ^ i.old.layout.k)
          (2 ^ i.old.layout.h) := h10 w hw
      rw [eM w hw] at h'
      exact h'

/-- From the Bool and "the trees open". -/
theorem readFits_of_B {i : SwIn} {pos : Positions}
    (h : readFitsB (stSh i.st) (Ground.Sh.bookSh i.book) (singleSh i.old) = true)
    (ho : AllOpen i.st i.firstTree pos i.book (treesOf i) i.opened) : ReadFits i pos :=
  (readFits_iff i pos).2 ⟨h, ho⟩

/-- **ReadFits just if both Bools accept.** -/
theorem readFits_iffB (i : SwIn) (pos : Positions) :
    ReadFits i pos ↔
      (readFitsB (stSh i.st) (Ground.Sh.bookSh i.book) (singleSh i.old) &&
        allOpenB (stSh i.st) (Ground.Sh.bookSh i.book) i.firstTree pos
          (treesOfS (Ground.Sh.bookSh i.book) (singleSh i.old)) i.opened) = true := by
  rw [readFits_iff, Bool.and_eq_true, trees_sh, allOpenB_iff]

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.ids_sh
#print axioms VerifiableInference.Desc.First.Shape.places_sh
#print axioms VerifiableInference.Desc.First.Shape.trees_sh
#print axioms VerifiableInference.Desc.First.Shape.colFitsB_iff
#print axioms VerifiableInference.Desc.First.Shape.leafGroups_sh
#print axioms VerifiableInference.Desc.First.Shape.leafOk_sh
#print axioms VerifiableInference.Desc.First.Shape.ownAt_sh
#print axioms VerifiableInference.Desc.First.Shape.allOpenB_iff
#print axioms VerifiableInference.Desc.First.Shape.readFits_iff
#print axioms VerifiableInference.Desc.First.Shape.readFits_of_B
#print axioms VerifiableInference.Desc.First.Shape.readFits_iffB
