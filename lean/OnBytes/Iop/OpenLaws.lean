-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/OpenLaws.lean: what a block reads of a view's opened columns.

Blk.readOpened opens the trees of some oracle messages at a list of positions and cuts each leaf's
column into the symbols of the oracle messages in it. The laws say, for a run on a view:
 - which of the view's opened columns the call uses up: the next ones, tree by tree in the order of
   the trees' places in the book, each tree at its own list, under the tree's key (treeKey). A key
   is a difference of natural numbers and does not tell apart the trees that a chain has taken over
   from an earlier chain. A view holds no roots, so nothing here says of which tree a column is a
   leaf: the strict reader has checked that before there is a view;
 - that the result is a pure function (symbolsOf) of these columns;
 - that the call leaves as it was what Blk.Frame names (among it the statement, the rounds not yet
   closed, the plan's entries, and whether a named test has failed) and, of the book of trees, what
   Blk.BookKept names. The call does change the book: it counts each opening of a tree, and no law
   here says so. Nothing is stated on the intermediate values (Ctx.notes).
readStored_inv says the same of Blk.readStored, which reads the columns of a stored table under the
key Fmt.storedKey.

Main definitions: Blk.Frame, Blk.BookKept, Blk.treeKey, viewColumns.
Main theorems: takeColumns_inv, readStored_inv, countOpening_inv, openTrees_inv, readOpened_inv.

What is not claimed. Nothing on the dry run. Nothing on a call that fails. The laws do not pass on
all that the calls test: not the columns' width, not the rule on what shares a leaf (countOpening),
not that the oracle messages asked for are all that their trees hold (readOpened). Nothing on
soundness. The program does not import this file.
-/
import OnBytes.Iop.GroundLaws

namespace OnBytes

namespace Blk

/-- What a call that reads opened columns leaves as it was. -/
structure Frame (c c' : Ctx) : Prop where
  st : c'.st = c.st
  failed : c'.failed = c.failed
  dry : c'.ch.dry = c.ch.dry
  entries : c'.ch.entries = c.ch.entries
  pending : c'.ch.pending = c.ch.pending
  last : c'.ch.last = c.ch.last
  asked : c'.ch.askedRows = c.ch.askedRows
  firstTree : c'.ch.firstTree = c.ch.firstTree
  roots : c'.ch.roots = c.ch.roots
  samples : c'.ch.samples = c.ch.samples

/-- Frame is reflexive. -/
theorem Frame.refl (c : Ctx) : Frame c c := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Frame is transitive. -/
theorem Frame.trans {a b c : Ctx} (h1 : Frame a b) (h2 : Frame b c) : Frame a c :=
  ⟨h2.st.trans h1.st, h2.failed.trans h1.failed, h2.dry.trans h1.dry,
    h2.entries.trans h1.entries, h2.pending.trans h1.pending, h2.last.trans h1.last,
    h2.asked.trans h1.asked, h2.firstTree.trans h1.firstTree, h2.roots.trans h1.roots,
    h2.samples.trans h1.samples⟩

end Blk

/-- The columns of one tree as a view holds them: under the tree's key, at the positions of the
list, each column as a list of words. -/
def viewColumns (key : Nat) (xs : Array Nat) (cols : Array (Array F)) :
    List (Nat × Nat × List UInt64) :=
  (xs.toList.zip cols.toList).map fun y => (key, y.1, y.2.toList)

/-- columnsFit is one condition on each pair of a column and a position, as far as both lists go. -/
theorem columnsFit_eq (key W : Nat) : ∀ (got : List (Nat × Nat × List UInt64)) (xs : List Nat),
    Blk.columnsFit key W got xs =
      (got.zip xs).all fun y => y.1.1 == key && y.1.2.1 == y.2 && y.1.2.2.length == W
  | [], _ => by simp [Blk.columnsFit]
  | _ :: _, [] => by simp [Blk.columnsFit]
  | g :: got, x :: xs => by
    simp only [Blk.columnsFit, List.zip_cons_cons, List.all_cons, columnsFit_eq key W got xs]

/-- A list of columns that meets columnsFit's condition and is as long as the list of positions is
determined by the key, the positions and the columns' words. -/
theorem rebuild (key W : Nat) : ∀ (got : List (Nat × Nat × List UInt64)) (xs : List Nat),
    got.length = xs.length →
    ((got.zip xs).all fun y => y.1.1 == key && y.1.2.1 == y.2 && y.1.2.2.length == W) = true →
    got = (xs.zip (got.map fun y => y.2.2.toArray)).map fun y => (key, y.1, y.2.toList)
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | g :: got, x :: xs, h, ha => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at ha
    obtain ⟨⟨⟨h1, h2⟩, _⟩, h4⟩ := ha
    have ih := rebuild key W got xs (by simpa using h) h4
    simp only [List.map_cons, List.zip_cons_cons, List.cons.injEq]
    exact ⟨Prod.ext h1 (Prod.ext h2 (by simp)), ih⟩

namespace Blk

/-- Columns that were taken were the view's next opened columns: under the key
t.number - c.ch.firstTree, at the positions of the list, one for each position. The key is a
difference of natural numbers: it is 0 for every tree whose number is not above that of the chain's
first tree, so it does not tell apart the trees that were taken over from an earlier chain. Not
stated here: that each column has the tree's width, which the call also tests. -/
theorem takeColumns_inv (t : Tree) (xs : Array Nat) (cols : Array (Array F)) (c c' : Ctx)
    (hd : c.ch.dry = false) (h : (takeColumns t xs).Yields c cols c') :
    c.ch.opened = viewColumns (t.number - c.ch.firstTree) xs cols ++ c'.ch.opened ∧
      cols.size = xs.size ∧ Frame c c' ∧ c'.book = c.book := by
  rw [yields_iff] at h
  unfold takeColumns at h
  simp only [hd, Bool.false_eq_true, if_false] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨hl, ha⟩ := hc
    rw [columnsFit_eq] at ha
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hr := rebuild (t.number - c.ch.firstTree) (t.shape.mainWidth + t.shape.maskWidth)
      (c.ch.opened.take xs.size) xs.toList (by simpa using hl) ha
    refine ⟨?_, by simpa using hl, ⟨rfl, rfl, hd.symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
    unfold viewColumns
    simp only
    rw [← hr, List.take_append_drop]
  · cases h

/-- Columns of a stored table that were read were the view's next opened columns: under the key
Fmt.storedKey t.item, which is 2^16 + t.item, at the list of the table's part of the draws (each
modulo 2^a, where a = t.sh.a), one for each position. Not stated here: that each has the table's
width, which the call also tests. -/
theorem readStored_inv (t : Fmt.Stored) (pos : Positions) (xs : Array Nat)
    (cols : Array (Array F)) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : (readStored t pos).Yields c (xs, cols) c') :
    xs = (Fmt.listOf ((Fmt.partOf t pos.draws.toList).map (· % 2 ^ t.sh.a))).toArray ∧
      c.ch.opened = viewColumns (Fmt.storedKey t.item) xs cols ++ c'.ch.opened ∧
      cols.size = xs.size ∧ Frame c c' ∧ c'.book = c.book := by
  rw [yields_iff] at h
  unfold readStored at h
  simp only [hd, Bool.false_eq_true, if_false] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨hl, ha⟩ := hc
    rw [columnsFit_eq] at ha
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    have hr := rebuild (Fmt.storedKey t.item) t.sh.W _ _ hl ha
    refine ⟨by rw [listOfT_eq], ?_, by simpa using hl,
      ⟨rfl, rfl, hd.symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
    unfold viewColumns
    simp only
    rw [← hr, List.take_append_drop]
  · cases h

/-- What a call that reads opened columns leaves of the book of trees: where each oracle message is,
how many trees there are, and of each tree all but the count of the lists at which it was opened. -/
structure BookKept (B B' : TreeBook) : Prop where
  place : B'.place = B.place
  size : B'.trees.size = B.trees.size
  trees : ∀ (t : Nat) (T : Tree), B.trees[t]? = some T →
    ∃ T' : Tree, B'.trees[t]? = some T' ∧ T'.shape = T.shape ∧
    T'.number = T.number ∧ T'.parts = T.parts ∧ T'.src = T.src ∧ T'.oneList = T.oneList

/-- BookKept is reflexive. -/
theorem BookKept.refl (B : TreeBook) : BookKept B B :=
  ⟨rfl, rfl, fun _ T h => ⟨T, h, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- BookKept is transitive. -/
theorem BookKept.trans {A B C : TreeBook} (h1 : BookKept A B) (h2 : BookKept B C) :
    BookKept A C :=
  ⟨h2.place.trans h1.place, h2.size.trans h1.size, fun t T h => by
    obtain ⟨T1, a, a1, a2, a3, a4, a5⟩ := h1.trees t T h
    obtain ⟨T2, b, b1, b2, b3, b4, b5⟩ := h2.trees t T1 a
    exact ⟨T2, b, b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5⟩⟩

/-- Counting an opening leaves what Frame names, the opened columns that are still to be read, and
of the book what BookKept names. (The call changes one tree's count of openings. The statement does
not say so: BookKept is silent on the counts.) -/
theorem countOpening_inv (t : Nat) (c c' : Ctx) (h : (countOpening t).Yields c () c') :
    Frame c c' ∧ c'.ch.opened = c.ch.opened ∧ BookKept c.book c'.book := by
  unfold countOpening at h
  obtain ⟨S, c1, h1, h⟩ := (yields_bind _ _ _ _ _).1 h
  obtain ⟨rfl, rfl⟩ := (yields_statement _ _ _).1 h1
  obtain ⟨B, c2, h2, h⟩ := (yields_bind _ _ _ _ _).1 h
  obtain ⟨rfl, rfl⟩ := (yields_theBook _ _ _).1 h2
  obtain ⟨tree, c3, h3, h⟩ := (yields_bind _ _ _ _ _).1 h
  obtain ⟨_, rfl⟩ := (yields_get _ _ _ _).1 h3
  dsimp only at h
  obtain ⟨_, c4, h4, h⟩ := (yields_bind _ _ _ _ _).1 h
  obtain ⟨_, rfl⟩ := (yields_must _ _ _).1 h4
  obtain ⟨_, c5, h5, h⟩ := (yields_bind _ _ _ _ _).1 h
  obtain ⟨_, rfl⟩ := (yields_must _ _ _).1 h5
  rw [yields_setBook] at h
  subst h
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp, ?_⟩
  intro u T hu
  by_cases e : t = u
  · subst e
    exact ⟨{ T with lists := T.lists + 1 }, by simp [Array.getElem?_modify, hu], rfl, rfl, rfl, rfl,
      rfl⟩
  · exact ⟨T, by simp [Array.getElem?_modify, e, hu], rfl, rfl, rfl, rfl, rfl⟩

/-- The key under which a view holds the columns of the tree at the place t of the book B: the
tree's number (Tree.number, which is not its place in the book) minus first, the number of the first
tree that the chain sends. A difference of natural numbers: see takeColumns_inv. -/
def treeKey (B : TreeBook) (first t : Nat) : Nat :=
  ((B.trees[t]?).map (·.number)).getD 0 - first

/-- The loop of openTrees: what it returns is acc and then what it has opened, of which
openTrees_inv's clauses hold. -/
theorem openTreesInto_inv (B : TreeBook) (pos : Positions) :
    ∀ (ts : List Nat) (acc : Array (Nat × Array Nat × Array (Array F)))
      (all : List (Nat × Array Nat × Array (Array F))) (c c' : Ctx),
    c.ch.dry = false → (openTreesInto B pos ts acc).Yields c all c' →
    ∃ out, all = acc.toList ++ out ∧
      c.ch.opened =
        (out.flatMap fun y => viewColumns (treeKey B c.ch.firstTree y.1) y.2.1 y.2.2) ++
          c'.ch.opened ∧
      out.map (·.1) = ts ∧
      (∀ y ∈ out, ∃ tree, B.trees[y.1]? = some tree ∧ tree.shape.logN ≤ pos.logN ∧
        y.2.1 = ownList tree pos ∧ y.2.2.size = y.2.1.size) ∧
      Frame c c' ∧ BookKept c.book c'.book
  | [], acc, all, c, c', _, h => by
    unfold openTreesInto at h
    obtain ⟨rfl, rfl⟩ := (yields_pure _ _ _ _).1 h
    exact ⟨[], by simp, by simp, rfl, by simp, Frame.refl _, BookKept.refl _⟩
  | t :: ts, acc, all, c, c', hd, h => by
    unfold openTreesInto at h
    obtain ⟨_, c1, h1, k1⟩ := (yields_bind _ _ _ _ _).1 h
    obtain ⟨f1, o1, b1⟩ := countOpening_inv _ _ _ h1
    obtain ⟨tree, c2, h2, k2⟩ := (yields_bind _ _ _ _ _).1 k1
    obtain ⟨ht, e2⟩ := (yields_get _ _ _ _).1 h2
    subst e2
    obtain ⟨_, c3, h3, k3⟩ := (yields_bind _ _ _ _ _).1 k2
    obtain ⟨hn, e3⟩ := (yields_must _ _ _).1 h3
    subst e3
    obtain ⟨cols, c4, h4, k4⟩ := (yields_bind _ _ _ _ _).1 k3
    obtain ⟨o4, s4, f4, b4⟩ := takeColumns_inv _ _ _ _ _ (f1.dry.trans hd) h4
    obtain ⟨rest, e5, o5, m5, a5, f5, b5⟩ :=
      openTreesInto_inv B pos ts _ all c4 c' (f4.dry.trans (f1.dry.trans hd)) k4
    refine ⟨(t, ownList tree pos, cols) :: rest, by rw [e5]; simp, ?_, by simp [m5], ?_,
      (f1.trans f4).trans f5, b1.trans (b4 ▸ b5)⟩
    · rw [← o1, o4, o5, f4.firstTree, f1.firstTree]
      simp [treeKey, ht, List.append_assoc]
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨tree, ht, by simpa using hn, rfl, s4⟩
      · exact a5 y hy

/-- Trees that were opened. ts: their places in the book B. The view's next opened columns were
under these trees' keys (treeKey), each tree's at its own list, tree by tree in the given order. -/
theorem openTrees_inv (B : TreeBook) (pos : Positions)
    (ts : List Nat) (out : List (Nat × Array Nat × Array (Array F))) (c c' : Ctx)
    (hd : c.ch.dry = false) (h : (openTrees B pos ts).Yields c out c') :
    c.ch.opened =
        (out.flatMap fun y => viewColumns (treeKey B c.ch.firstTree y.1) y.2.1 y.2.2) ++
          c'.ch.opened ∧
      out.map (·.1) = ts ∧
      (∀ y ∈ out, ∃ tree, B.trees[y.1]? = some tree ∧ tree.shape.logN ≤ pos.logN ∧
        y.2.1 = ownList tree pos ∧ y.2.2.size = y.2.1.size) ∧
      Frame c c' ∧ BookKept c.book c'.book := by
  obtain ⟨o, e, r⟩ := openTreesInto_inv B pos ts #[] out c c' hd h
  have e' : out = o := by simpa using e
  subst e'
  exact r

/-- What readOpened reads and returns. The view's next opened columns were under the keys (treeKey)
of the oracle messages' trees, in the increasing order of the trees' places in the book, each tree
once. The result is symbolsOf of these columns, oracle message by oracle message. Of the rest, what
Frame and BookKept name stays as it was. -/
theorem readOpened_inv (ids : Array Nat) (pos : Positions) (out : Array (Array Column))
    (c c' : Ctx) (hd : c.ch.dry = false) (h : (readOpened ids pos).Yields c out c') :
    ∃ (places : Array (Nat × Nat)) (cols : List (Nat × Array Nat × Array (Array F))),
      (ids.mapM fun o => c.book.place[o]?) = some places ∧
      c.ch.opened =
        (cols.flatMap fun y => viewColumns (treeKey c.book c.ch.firstTree y.1) y.2.1 y.2.2) ++
          c'.ch.opened ∧
      cols.map (·.1) = Fmt.listOf (places.map (·.1)).toList ∧
      (∀ y ∈ cols, ∃ tree, c.book.trees[y.1]? = some tree ∧ tree.shape.logN ≤ pos.logN ∧
        y.2.1 = ownList tree pos ∧ y.2.2.size = y.2.1.size) ∧
      ((ids.zip places).mapM fun y => symbolsOf c.st c.book pos cols y.1 y.2) = some out ∧
      Frame c c' ∧ BookKept c.book c'.book := by
  unfold readOpened at h
  obtain ⟨S, c1, h1, h⟩ := (yields_bind _ _ _ _ _).1 h
  obtain ⟨rfl, rfl⟩ := (yields_statement _ _ _).1 h1
  obtain ⟨B, c2, h2, h⟩ := (yields_bind _ _ _ _ _).1 h
  obtain ⟨rfl, rfl⟩ := (yields_theBook _ _ _).1 h2
  obtain ⟨places, c3, h3, h⟩ := (yields_bind _ _ _ _ _).1 h
  obtain ⟨hp, rfl⟩ := (yields_get _ _ _ _).1 h3
  dsimp only at h
  obtain ⟨_, c4, h4, h⟩ := (yields_bind _ _ _ _ _).1 h
  obtain ⟨_, rfl⟩ := (yields_must _ _ _).1 h4
  obtain ⟨cols, c5, h5, h⟩ := (yields_bind _ _ _ _ _).1 h
  obtain ⟨o5, m5, a5, f5, b5⟩ := openTrees_inv _ _ _ _ _ _ hd h5
  obtain ⟨hs, rfl⟩ := (yields_get _ _ _ _).1 h
  exact ⟨places, cols, hp, o5, by rw [m5, listOfT_eq], a5, hs, f5, b5⟩

end Blk

end OnBytes

#print axioms OnBytes.Blk.takeColumns_inv
#print axioms OnBytes.Blk.readStored_inv
#print axioms OnBytes.Blk.readOpened_inv
