-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkSeat.lean: the columns that the program reads are columns that the view shows.

A block of the program reads opened columns by one call, `Blk.readOpened`. On a view the call takes
the next entries of the view's list of opened columns, after it has tested the key and the position
of each (OnBytes/Iop/OpenLaws.lean). So a column that was read is an entry of that list. This file
says so in the form in which a proof that goes through a run block by block needs it: whatever is
known of all entries of the view's list under a tree's key holds of the columns that were read of
that tree.

Main definitions.
 `OnView`   the run is a run on the view: what is left for it to read of opened columns is in the
            view's list.
 `Shows`    under the key n the view's list holds only values of the function f.
 `BookKeeps`   a later book has each oracle message at its place and each tree with its shape,
            number and parts.
 `ReadKeeps`   that, with the number of roots received and the number of answers to a sample.
 `Seat`     some oracle messages are the parts of one tree, with given shapes.
Main theorems.
 `mem_viewColumns`    a column of a tree, with key and position, is among the tree's entries.
 `readOpened_shows`   the call leaves a run on the view a run on the view; each tree that it opens
                      is opened at its own list of positions, and each column that it takes of a
                      tree with the number n is the value of f at its position, if the view shows f
                      under n; the result is the program's own cut of these columns.
 `readOpened_keeps`   the call keeps what is public of the book, the number of roots received and
                      the number of answers to a sample.
 `Seat.keeps`         a seat stays a seat as long as book and statement keep what is public.

Not claimed. Nothing on how a column is cut into the symbols of the oracle messages.
-/
import OnBytes.Iop.OpenLaws

set_option autoImplicit false

namespace OnBytes.Slice

/-- The run is a run on the view V: it is no dry run, the chain's first tree has the number 0,
and every opened column that is left to be read is in the view's list. -/
structure OnView (V : Fmt.View) (c : Ctx) : Prop where
  /-- it is no dry run -/
  dry : c.ch.dry = false
  /-- the chain's first tree has the number 0 in its session -/
  first : c.ch.firstTree = 0
  /-- what is left to be read of opened columns is in the view's list -/
  opened : ∀ o ∈ c.ch.opened, o ∈ V.opened

/-- Under the key n the view's list of opened columns holds only values of the function f. -/
def Shows (V : Fmt.View) (n : Nat) (f : Nat → Option (List UInt64)) : Prop :=
  ∀ o ∈ V.opened, o.1 = n → f o.2.1 = some o.2.2

/-- A column of a tree, with the tree's key and its position, is among the tree's entries. -/
theorem mem_viewColumns (key : Nat) (xs : Array Nat) (cols : Array (Array F)) (i : Nat)
    (h1 : i < xs.size) (h2 : i < cols.size) :
    (key, xs.getD i 0, (cols.getD i #[]).toList) ∈ viewColumns key xs cols := by
  unfold viewColumns
  refine List.mem_map.2 ⟨(xs.getD i 0, cols.getD i #[]), ?_, rfl⟩
  have hl : i < (xs.toList.zip cols.toList).length := by
    rw [List.length_zip, Array.length_toList, Array.length_toList]
    exact Nat.lt_min.2 ⟨h1, h2⟩
  refine List.mem_iff_getElem.2 ⟨i, hl, ?_⟩
  simp [Array.getD, h1, h2]

/-- What the program reads of opened columns is what the view shows. -/
theorem readOpened_shows (V : Fmt.View) (ids : Array Nat) (pos : Positions)
    (out : Array (Array Column)) (a a' : Ctx) (hv : OnView V a)
    (h : (Blk.readOpened ids pos).Yields a out a') :
    OnView V a' ∧ Blk.Frame a a' ∧
    ∃ (places : Array (Nat × Nat)) (cols : List (Nat × Array Nat × Array (Array F))),
      (ids.mapM fun o => a.book.place[o]?) = some places ∧
      cols.map (·.1) = Fmt.listOf (places.map (·.1)).toList ∧
      (∀ y ∈ cols, ∃ tree, a.book.trees[y.1]? = some tree ∧ tree.shape.logN ≤ pos.logN ∧
        y.2.1 = Blk.ownList tree pos ∧ y.2.2.size = y.2.1.size ∧
        ∀ f, Shows V tree.number f → ∀ i, i < y.2.1.size →
          f (y.2.1.getD i 0) = some (y.2.2.getD i #[]).toList) ∧
      ((ids.zip places).mapM fun y => Blk.symbolsOf a.st a.book pos cols y.1 y.2) = some out := by
  obtain ⟨places, cols, hpl, hop, hmap, hall, hsym, hfr, _⟩ :=
    Blk.readOpened_inv ids pos out a a' hv.dry h
  refine ⟨⟨hfr.dry.trans hv.dry, hfr.firstTree.trans hv.first, fun o ho => hv.opened o ?_⟩, hfr,
    places, cols, hpl, hmap, fun y hy => ?_, hsym⟩
  · rw [hop]
    exact List.mem_append_right _ ho
  · obtain ⟨tree, ht, hlog, hown, hsz⟩ := hall y hy
    refine ⟨tree, ht, hlog, hown, hsz, fun f hf i hi => ?_⟩
    have hkey : Blk.treeKey a.book a.ch.firstTree y.1 = tree.number := by
      unfold Blk.treeKey
      rw [ht, hv.first]
      rfl
    have hmem : (tree.number, y.2.1.getD i 0, (y.2.2.getD i #[]).toList) ∈ a.ch.opened := by
      rw [hop]
      refine List.mem_append_left _ (List.mem_flatMap.2 ⟨y, hy, ?_⟩)
      rw [hkey]
      exact mem_viewColumns _ _ _ i hi (by rw [hsz]; exact hi)
    exact hf _ (hv.opened _ hmem) rfl

/-! ## What a reading leaves of the book -/

/-- The book B' keeps what is public of the book B: the place of each oracle message, and each
tree's shape, number and parts. -/
structure BookKeeps (B B' : TreeBook) : Prop where
  /-- each oracle message keeps its place -/
  place : ∀ (o : Nat) (p : Nat × Nat), B.place[o]? = some p → B'.place[o]? = some p
  /-- each tree keeps its shape, its number and its parts -/
  tree : ∀ (t : Nat) (T : Tree), B.trees[t]? = some T →
    ∃ T', B'.trees[t]? = some T' ∧ T'.shape = T.shape ∧ T'.number = T.number ∧ T'.parts = T.parts

/-- A book keeps what is public of itself. -/
theorem BookKeeps.refl (B : TreeBook) : BookKeeps B B :=
  ⟨fun _ _ h => h, fun _ T h => ⟨T, h, rfl, rfl, rfl⟩⟩

/-- The relation goes through a book between. -/
theorem BookKeeps.trans {A B C : TreeBook} (h1 : BookKeeps A B) (h2 : BookKeeps B C) :
    BookKeeps A C :=
  ⟨fun o p h => h2.place o p (h1.place o p h), fun t T h => by
    obtain ⟨T1, k1, a1, b1, c1⟩ := h1.tree t T h
    obtain ⟨T2, k2, a2, b2, c2⟩ := h2.tree t T1 k1
    exact ⟨T2, k2, a2.trans a1, b2.trans b1, c2.trans c1⟩⟩

/-- An equal book keeps all. -/
theorem BookKeeps.of_eq {B B' : TreeBook} (h : B' = B) : BookKeeps B B' := by
  rw [h]
  exact BookKeeps.refl B

/-- What a reading keeps of the book (OnBytes/Iop/OpenLaws.lean) is more than is asked here. -/
theorem BookKeeps.of_kept {B B' : TreeBook} (h : Blk.BookKept B B') : BookKeeps B B' :=
  ⟨fun o p hp => by rw [h.place]; exact hp, fun t T hT => by
    obtain ⟨T', k, e1, e2, e3, _, _⟩ := h.trees t T hT
    exact ⟨T', k, e1, e2, e3⟩⟩

/-- What a reading leaves beside what `Blk.Frame` names: what is public of the book, the number
of roots received, and the number of answers to a sample. -/
structure ReadKeeps (c c' : Ctx) : Prop where
  /-- what is public of the book -/
  book : BookKeeps c.book c'.book
  /-- the number of roots received -/
  roots : c'.ch.roots = c.ch.roots
  /-- the number of answers to a sample -/
  samples : c'.ch.samples = c.ch.samples

/-- A context keeps what is its own. -/
theorem ReadKeeps.refl (c : Ctx) : ReadKeeps c c := ⟨BookKeeps.refl _, rfl, rfl⟩

/-- The relation goes through a context between. -/
theorem ReadKeeps.trans {a b c : Ctx} (h1 : ReadKeeps a b) (h2 : ReadKeeps b c) : ReadKeeps a c :=
  ⟨h1.book.trans h2.book, h2.roots.trans h1.roots, h2.samples.trans h1.samples⟩

/-- An equal context keeps all. -/
theorem ReadKeeps.of_eq {c c' : Ctx} (h : c' = c) : ReadKeeps c c' := by
  rw [h]
  exact ReadKeeps.refl c

/-- A reading of opened columns keeps what is public of the book, the number of roots and the
number of answers to a sample. -/
theorem readOpened_keeps (ids : Array Nat) (pos : Positions) (out : Array (Array Column))
    (c c' : Ctx) (hd : c.ch.dry = false) (h : (Blk.readOpened ids pos).Yields c out c') :
    ReadKeeps c c' := by
  obtain ⟨_, _, _, _, _, _, _, hfr, hbk⟩ := Blk.readOpened_inv ids pos out c c' hd h
  exact ⟨BookKeeps.of_kept hbk, hfr.roots, hfr.samples⟩

/-! ## Where oracle messages sit -/

/-- The statement S' has each oracle message of S, with its shape. -/
def ShapesKeep (S S' : Statement) : Prop :=
  ∀ (o : Nat) (x : Oracle), S.oracles[o]? = some x →
    ∃ x', S'.oracles[o]? = some x' ∧ x'.shape = x.shape

/-- A statement has its own oracle messages. -/
theorem ShapesKeep.refl (S : Statement) : ShapesKeep S S := fun _ x h => ⟨x, h, rfl⟩

/-- The relation goes through a statement between. -/
theorem ShapesKeep.trans {A B C : Statement} (h1 : ShapesKeep A B) (h2 : ShapesKeep B C) :
    ShapesKeep A C := fun o x h => by
  obtain ⟨x1, k1, e1⟩ := h1 o x h
  obtain ⟨x2, k2, e2⟩ := h2 o x1 k1
  exact ⟨x2, k2, e2.trans e1⟩

/-- The oracle messages ids are the parts of one tree, in this order: the tree with the number n
in its session, of 2^logN leaves. shapes: their shapes. All that is said is public: it follows from
what was announced when the tree was sent (OnBytes/Slice/BlkSentSeat.lean: `seat_of_sent`, under its
hypotheses). -/
structure Seat (c : Ctx) (ids : List Nat) (n logN : Nat) (shapes : List OracleShape) : Prop where
  /-- one shape for each oracle message -/
  len : shapes.length = ids.length
  /-- the tree: its number, its length, the widths of its parts in a column, and that oracle
  message number w of the list is its part w -/
  tree : ∃ (t : Nat) (tree : Tree), c.book.trees[t]? = some tree ∧ tree.number = n ∧
    tree.shape.logN = logN ∧
    tree.shape.mainSymbols = (shapes.map fun s => s.mainRows * s.mainDeg).toArray ∧
    tree.shape.maskSymbols = (shapes.map fun s => s.maskRows * 3).toArray ∧
    ∀ w, w < ids.length → c.book.place[ids.getD w 0]? = some (t, w)
  /-- the statement has each oracle message, with its shape -/
  shape : ∀ w, w < ids.length →
    ∃ x, c.st.oracles[ids.getD w 0]? = some x ∧ x.shape = shapes.getD w default

/-- A seat stays a seat as long as the book and the statement keep what is public. -/
theorem Seat.keeps {c c' : Ctx} {ids : List Nat} {n logN : Nat} {shapes : List OracleShape}
    (h : Seat c ids n logN shapes) (hb : BookKeeps c.book c'.book) (hs : ShapesKeep c.st c'.st) :
    Seat c' ids n logN shapes := by
  obtain ⟨t, tree, h1, h2, h3, h4, h5, h6⟩ := h.tree
  obtain ⟨T', k1, e1, e2, _⟩ := hb.tree t tree h1
  refine ⟨h.len, ⟨t, T', k1, e2.trans h2, ?_, ?_, ?_, fun w hw => hb.place _ _ (h6 w hw)⟩,
    fun w hw => ?_⟩
  · rw [e1]
    exact h3
  · rw [e1]
    exact h4
  · rw [e1]
    exact h5
  · obtain ⟨x, hx, ex⟩ := h.shape w hw
    obtain ⟨x', hx', ex'⟩ := hs _ x hx
    exact ⟨x', hx', ex'.trans ex⟩

end OnBytes.Slice

#print axioms OnBytes.Slice.BookKeeps.refl
#print axioms OnBytes.Slice.BookKeeps.trans
#print axioms OnBytes.Slice.BookKeeps.of_eq
#print axioms OnBytes.Slice.BookKeeps.of_kept
#print axioms OnBytes.Slice.ReadKeeps.refl
#print axioms OnBytes.Slice.ReadKeeps.trans
#print axioms OnBytes.Slice.ReadKeeps.of_eq
#print axioms OnBytes.Slice.ShapesKeep.refl
#print axioms OnBytes.Slice.ShapesKeep.trans
#print axioms OnBytes.Slice.Seat.keeps
#print axioms OnBytes.Slice.mem_viewColumns
#print axioms OnBytes.Slice.readOpened_shows
#print axioms OnBytes.Slice.readOpened_keeps
