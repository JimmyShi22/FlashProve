-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/BookKit.lean: in a dry run every opening that is noted is the opening of a tree
of the book of trees, and the book's trees keep shape, number and source: the property, the calls of
OnBytes/Iop/Ground.lean, and the four routines that read or write the book.

Definitions, statements and proofs. In a dry run an opening is noted by Blk.takeColumns, with the
shape, the number and the source of the tree that it is given. The one routine that calls it takes
the tree from a book that Blk.theBook has returned. The book is written by Blk.setBook, in three
routines, each time with a book that is made from one that Blk.theBook has returned. So Blk.setBook
and Blk.takeColumns do not have the property by themselves; the four routines around them have it,
and are shown here by hand. The rules and tactics of OnBytes/Tie/Pv/Keeps/KeepsLift.lean and the
commands of OnBytes/Tie/Pv/Keeps/KeepsWalk.lean are stated for any property of a monad's routines
that pure has and bind carries (the class HasKeeps). Inside the namespace of this file the blocks
get such a property of their own: `BookB`. So KeepsM x reads here, and here alone, as `BookB` says.
A file that wants another reading of KeepsM does not open this namespace.
Main names:
  `key t`: a tree's shape, number and source. `noteOf t`: what Blk.takeColumns notes of it.
  `Grows B B'`: each place of the book B holds in B' a tree with the same key.
  `Notes c`: every opening that is noted in c is `noteOf` of a tree of c's book.
  `BookB b`: wherever b succeeds in a dry run: the run stays dry, the book grows, and `Notes` goes
    along.
  `hasBook`: the class HasKeeps for blocks at `BookB`, inside this namespace alone.
  `b_fail` and those that follow: the calls of Ground.lean but Blk.setBook and Blk.takeColumns.
  `b_countOpening`, `b_readOpened`, `b_receiveOracles`, `b_adoptOracles`: the four by hand.
Tactics of this file.
  book_prim d: proves KeepsM, in the reading of this namespace, of a call d that is written as a
    function of the context and writes neither the book nor a noted round's openings.
Limits: one direction: from a success. Nothing on a run on a view.
-/
import OnBytes.Iop.GroundLaws
import OnBytes.Model.Trees
import OnBytes.Tie.Pv.Keeps.KeepsWalk
import OnBytes.Tie.Pv.Keeps.NotesKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Keeps.Book

open OnBytes OnBytes.Model OnBytes.L5

/-- A tree's shape, number and source. -/
def key (t : Tree) : TreeShape × Nat × Fmt.Src := (t.shape, t.number, t.src)

/-- What Blk.takeColumns notes of a tree in a dry run. -/
def noteOf (t : Tree) : Fmt.Shape × Fmt.Src :=
  ({ a := t.shape.logN, W := t.shape.mainWidth + t.shape.maskWidth, stored := false,
     tree := t.number }, t.src)

theorem noteOf_key {t t' : Tree} (h : key t' = key t) : noteOf t' = noteOf t := by
  obtain ⟨h1, h2, h3⟩ : t'.shape = t.shape ∧ t'.number = t.number ∧ t'.src = t.src := by
    unfold key at h
    exact ⟨congrArg (·.1) h, congrArg (·.2.1) h, congrArg (·.2.2) h⟩
  unfold noteOf
  rw [h1, h2, h3]

/-- Each place of B holds in B' a tree with the same key. -/
def GrowsT (A A' : Array Tree) : Prop :=
  ∀ (i : Nat) (t : Tree), A[i]? = some t → ∃ t', A'[i]? = some t' ∧ key t' = key t

theorem GrowsT.refl (A : Array Tree) : GrowsT A A := fun _ t h => ⟨t, h, rfl⟩

theorem GrowsT.trans {A B C : Array Tree} (h1 : GrowsT A B) (h2 : GrowsT B C) : GrowsT A C :=
  fun i t h => by
    obtain ⟨t1, a1, k1⟩ := h1 i t h
    obtain ⟨t2, a2, k2⟩ := h2 i t1 a1
    exact ⟨t2, a2, k2.trans k1⟩

theorem GrowsT.push (A : Array Tree) (x : Tree) : GrowsT A (A.push x) := fun i t h => by
  obtain ⟨hi, _⟩ := Array.getElem?_eq_some_iff.1 h
  refine ⟨t, ?_, rfl⟩
  rw [Array.getElem?_push]
  split
  · omega
  · exact h

theorem GrowsT.modify (A : Array Tree) (j : Nat) (f : Tree → Tree) (hf : ∀ t, key (f t) = key t) :
    GrowsT A (A.modify j f) := fun i t h => by
  rw [Array.getElem?_modify]
  split
  · exact ⟨f t, by rw [h]; rfl, hf t⟩
  · exact ⟨t, h, rfl⟩

/-- The same of two books. -/
def Grows (B B' : TreeBook) : Prop := GrowsT B.trees B'.trees

/-- Every noted opening is the opening of a tree of the trees A. -/
def NotesIn (noted : Array RoundNote) (A : Array Tree) : Prop :=
  ∀ n ∈ noted.toList, ∀ o ∈ n.opens, ∃ t ∈ A.toList, noteOf t = o

/-- Every opening that is noted in c is the opening of a tree of c's book. -/
def Notes (c : Ctx) : Prop := NotesIn c.ch.noted c.book.trees

theorem NotesIn.grows {noted : Array RoundNote} {A A' : Array Tree} (h : NotesIn noted A)
    (g : GrowsT A A') : NotesIn noted A' := fun n hn o ho => by
  obtain ⟨t, ht, e⟩ := h n hn o ho
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ht
  have hi' : i < A.size := by simpa using hi
  obtain ⟨t', a, k⟩ := g i A[i] (Array.getElem?_eq_getElem hi')
  refine ⟨t', Array.mem_toList_iff.2 (Array.mem_of_getElem? a), ?_⟩
  rw [noteOf_key k]
  simpa using e

/-- In a dry run: the run stays dry, the book grows, and Notes goes along. -/
def BookB {α : Type} (b : Blk α) : Prop :=
  ∀ c x c', b c = .ok (x, c') → c.ch.dry = true →
    c'.ch.dry = true ∧ Grows c.book c'.book ∧ (Notes c → Notes c')

/-- For a block, inside this namespace: BookB. -/
scoped instance (priority := high) hasBook : HasKeeps Blk where
  K := fun b => BookB b
  K_pure := fun a c x c' h hd => by cases h; exact ⟨hd, GrowsT.refl _, id⟩
  K_bind := fun b f hb hf c y c2 h hd => by
    obtain ⟨x, c1, h1, h2⟩ := (Blk.yields_bind b f c c2 y).1 ((Blk.yields_iff _ _ _ _).2 h)
    obtain ⟨d1, g1, n1⟩ := hb _ _ _ ((Blk.yields_iff _ _ _ _).1 h1) hd
    obtain ⟨d2, g2, n2⟩ := hf x _ _ _ ((Blk.yields_iff _ _ _ _).1 h2) d1
    exact ⟨d2, g1.trans g2, fun k => n2 (n1 k)⟩

/-- For a call that is written as a function of the context and writes neither the book nor a noted
round's openings. -/
macro "book_prim " d:ident : tactic =>
  `(tactic| (
      refine ⟨fun c x c' h hd => ?_⟩
      unfold $d at h
      try dsimp only at h
      repeat' (split at h)
      all_goals first
        | (cases h; done)
        | (cases h; exact ⟨hd, GrowsT.refl _, id⟩)))

/-! ## The calls of Ground.lean that are functions of the context -/

instance b_fail {α : Type} (n : String) : KeepsM (Blk.fail n : Blk α) := by book_prim Blk.fail
instance b_must (b : Bool) (n : String) : KeepsM (Blk.must b n) := by book_prim Blk.must
instance b_test (b : Bool) (n : String) : KeepsM (Blk.test b n) := by book_prim Blk.test
instance b_check (n : String) (b : Bool) : KeepsM (Blk.check n b) := by book_prim Blk.check
instance b_onView {α : Type} (d : α) (f : Unit → α) :
    KeepsM (Blk.onView d f) := by book_prim Blk.onView
instance b_getOnView {α : Type} (d : α) (f : Unit → Option α) (n : String) :
    KeepsM (Blk.getOnView d f n) := by book_prim Blk.getOnView
instance b_testOnView (f : Unit → Bool) (n : String) :
    KeepsM (Blk.testOnView f n) := by book_prim Blk.testOnView
instance b_checkOnView (n : String) (f : Unit → Bool) :
    KeepsM (Blk.checkOnView n f) := by book_prim Blk.checkOnView
instance b_get {α : Type} (x : Option α) (n : String) : KeepsM (Blk.get x n) := by book_prim Blk.get
instance b_isDry : KeepsM Blk.isDry := by book_prim Blk.isDry
instance b_samples : KeepsM Blk.samples := by book_prim Blk.samples
instance b_firstTree : KeepsM Blk.firstTree := by book_prim Blk.firstTree
instance b_lastEntry : KeepsM Blk.lastEntry := by book_prim Blk.lastEntry
instance b_note (w : String) (v : E) : KeepsM (Blk.note w v) := by book_prim Blk.note
instance b_noteBy (w : String) (v : Unit → E) : KeepsM (Blk.noteBy w v) := by book_prim Blk.noteBy
instance b_statement : KeepsM Blk.statement := by book_prim Blk.statement
instance b_setStatement (S : Statement) :
    KeepsM (Blk.setStatement S) := by book_prim Blk.setStatement
instance b_recvRoot : KeepsM Blk.recvRoot := by book_prim Blk.recvRoot
instance b_requireRows (r : Nat) : KeepsM (Blk.requireRows r) := by book_prim Blk.requireRows
instance b_handOver : KeepsM Blk.handOver := by book_prim Blk.handOver
instance b_onOracle (o : Nat) (f : Oracle → Oracle) :
    KeepsM (Blk.onOracle o f) := by book_prim Blk.onOracle
instance b_onGroup (g : Nat) (f : Group → Group) :
    KeepsM (Blk.onGroup g f) := by book_prim Blk.onGroup
instance b_theBook : KeepsM Blk.theBook := by book_prim Blk.theBook

instance b_item (i : Fmt.Item) (d : Fmt.ItemValue) : KeepsM (Blk.item i d) :=
  ⟨fun c x c' h hd => by
    unfold Blk.item at h
    simp only [hd, if_true] at h
    cases h
    exact ⟨rfl, GrowsT.refl _, id⟩⟩

instance b_close (n : String) (k : Fmt.Kind) (nz : Nat) : KeepsM (Blk.close n k nz) :=
  ⟨fun c x c' h hd => by
    unfold Blk.close at h
    cases he : c.ch.entries with
    | nil => simp [he] at h
    | cons e es =>
      simp only [he] at h
      split at h
      · cases h
      · simp only [hd] at h
        cases h
        refine ⟨rfl, GrowsT.refl _, fun q m hm o ho => ?_⟩
        have hm' : m ∈ (c.ch.noted.push
            { entry := e, kind := k, items := c.ch.items.reverse }).toList := hm
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm'
        rcases hm' with h1 | rfl
        · exact q m h1 o ho
        · cases ho⟩

instance b_readStored (t : Fmt.Stored) (p : Positions) : KeepsM (Blk.readStored t p) :=
  ⟨fun c x c' h hd => by
    unfold Blk.readStored at h
    simp only [hd, if_true] at h
    split at h
    · cases h
    · cases h
      exact ⟨rfl, GrowsT.refl _, fun q => Notes.all_modify
        (f := fun n => { n with stored := n.stored ++ [t] })
        (fun n => ∀ o ∈ n.opens, ∃ t ∈ c.book.trees.toList, noteOf t = o) (fun _ hn => hn) _ _ q⟩⟩

instance b_named {α : Type} (n : String) (b : Blk α) [hb : KeepsM b] : KeepsM (Blk.named n b) :=
  ⟨fun c x c' h hd => by
    unfold Blk.named at h
    split at h
    · cases h
    · cases h; exact hb.out _ _ _ (by assumption) hd⟩

instance b_inPlace {α : Type} (n : String) (b : Blk α) [hb : KeepsM b] :
    KeepsM (Blk.inPlace n b) :=
  ⟨fun c x c' h hd => by
    unfold Blk.inPlace at h
    split at h
    · cases h
    · cases h; exact hb.out _ _ _ (by assumption) hd⟩

/-- What has no context, lifted into a block. -/
instance b_except {α : Type} {n : Type → Type} [MonadLiftT n (Except Failure)] (x : n α) :
    KeepsM (monadLift x : Blk α) :=
  ⟨fun c y c' h hd => by
    have h' : ((monadLift x : Except Failure α) >>= fun a => pure (a, c)) = .ok (y, c') := h
    cases e : (monadLift x : Except Failure α) with
    | error f => rw [e] at h'; cases h'
    | ok a => rw [e] at h'; cases h'; exact ⟨hd, GrowsT.refl _, id⟩⟩

instance b_getThe : KeepsM (getThe Ctx : Blk Ctx) :=
  ⟨fun c x c' h hd => by cases h; exact ⟨hd, GrowsT.refl _, id⟩⟩

instance b_change (f : Fork → Option Fork) : KeepsM (SubM.change f) :=
  ⟨fun F c y c' h hd => by
    unfold SubM.change at h
    cases e : f F with
    | none => rw [e] at h; cases h
    | some a => rw [e] at h; cases h; exact ⟨hd, GrowsT.refl _, id⟩⟩

instance b_take {α : Type} (f : Fork → Option (α × Fork)) : KeepsM (SubM.take f) :=
  ⟨fun F c y c' h hd => by
    unfold SubM.take at h
    cases e : f F with
    | none => rw [e] at h; cases h
    | some a => rw [e] at h; cases h; exact ⟨hd, GrowsT.refl _, id⟩⟩

instance b_ask {α : Type} (f : Fork → Option α) : KeepsM (SubM.ask f) :=
  ⟨fun F c y c' h hd => by
    unfold SubM.ask at h
    cases e : f F with
    | none => rw [e] at h; cases h
    | some a => rw [e] at h; cases h; exact ⟨hd, GrowsT.refl _, id⟩⟩

/-! ## The four routines that read or write the book -/

/-- Blk.takeColumns of a tree whose key a tree of the book has. -/
theorem takeColumns_book {t : Tree} {xs : Array Nat} {c : Ctx} {x : Array (Array F)} {c' : Ctx}
    (h : Blk.takeColumns t xs c = .ok (x, c')) (hd : c.ch.dry = true)
    (ht : ∃ t' ∈ c.book.trees.toList, key t' = key t) :
    c'.ch.dry = true ∧ c'.book = c.book ∧ (Notes c → Notes c') := by
  unfold Blk.takeColumns at h
  simp only [hd, if_true] at h
  split at h
  · cases h
  · cases h
    refine ⟨rfl, rfl, fun q => Notes.all_modify
      (fun n => ∀ o ∈ n.opens, ∃ t ∈ c.book.trees.toList, noteOf t = o)
      (fun n hn o ho => ?_) _ _ q⟩
    rcases List.mem_append.1 ho with h1 | h1
    · exact hn o h1
    · obtain ⟨t', m, e⟩ := ht
      refine ⟨t', m, ?_⟩
      rw [List.mem_singleton.1 h1, noteOf_key e]
      rfl

/-- A context with another book that has grown. -/
theorem setBook_book (c : Ctx) (B : TreeBook) (hd : c.ch.dry = true)
    (g : GrowsT c.book.trees B.trees) :
    ({ c with book := B } : Ctx).ch.dry = true ∧ Grows c.book ({ c with book := B } : Ctx).book ∧
      (Notes c → Notes { c with book := B }) := ⟨hd, g, fun q => NotesIn.grows q g⟩

instance b_countOpening (t : Nat) : KeepsM (Blk.countOpening t) :=
  ⟨fun c x c' h0 hd => by
    have h := (Blk.yields_iff _ _ _ _).2 h0
    unfold Blk.countOpening at h
    obtain ⟨S, c1, h1, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨rfl, eh1⟩ := (Blk.yields_statement _ _ _).1 h1
    obtain rfl := eh1.symm
    obtain ⟨B, c2, h2, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨rfl, eh2⟩ := (Blk.yields_theBook _ _ _).1 h2
    obtain rfl := eh2.symm
    obtain ⟨tree, c3, h3, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨_, eh3⟩ := (Blk.yields_get _ _ _ _).1 h3
    obtain rfl := eh3.symm
    dsimp only at h
    obtain ⟨_, c4, h4, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨_, eh4⟩ := (Blk.yields_must _ _ _).1 h4
    obtain rfl := eh4.symm
    obtain ⟨_, c5, h5, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨_, eh5⟩ := (Blk.yields_must _ _ _).1 h5
    obtain rfl := eh5.symm
    rw [Blk.yields_setBook] at h
    subst h
    exact setBook_book _ _ hd (GrowsT.modify _ _ _ fun _ => rfl)⟩

/-- The loop of openTrees, from a context whose book has grown out of B. -/
theorem openTreesInto_book (B : TreeBook) (pos : Positions) :
    ∀ (ts : List Nat) (acc : Array (Nat × Array Nat × Array (Array F)))
      (all : List (Nat × Array Nat × Array (Array F))) (c c' : Ctx),
    (Blk.openTreesInto B pos ts acc).Yields c all c' → c.ch.dry = true →
    GrowsT B.trees c.book.trees →
      c'.ch.dry = true ∧ Grows c.book c'.book ∧ (Notes c → Notes c')
  | [], acc, all, c, c', h, hd, _ => by
    unfold Blk.openTreesInto at h
    obtain ⟨_, rfl⟩ := (Blk.yields_pure _ _ _ _).1 h
    exact ⟨hd, GrowsT.refl _, id⟩
  | t :: ts, acc, all, c, c', h, hd, hB => by
    unfold Blk.openTreesInto at h
    obtain ⟨_, c1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨d1, g1, n1⟩ := (b_countOpening t).out c _ c1 ((Blk.yields_iff _ _ _ _).1 h1) hd
    obtain ⟨tree, c2, h2, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 k1
    obtain ⟨ht, e2⟩ := (Blk.yields_get _ _ _ _).1 h2
    obtain rfl := e2.symm
    obtain ⟨_, c3, h3, k3⟩ := (Blk.yields_bind _ _ _ _ _).1 k2
    obtain ⟨_, e3⟩ := (Blk.yields_must _ _ _).1 h3
    obtain rfl := e3.symm
    obtain ⟨cols, c4, h4, k4⟩ := (Blk.yields_bind _ _ _ _ _).1 k3
    obtain ⟨t', a', q'⟩ := (hB.trans g1) t tree ht
    obtain ⟨d4, e4, n4⟩ := takeColumns_book ((Blk.yields_iff _ _ _ _).1 h4) d1
      ⟨t', Array.mem_toList_iff.2 (Array.mem_of_getElem? a'), q'⟩
    obtain ⟨d5, g5, n5⟩ := openTreesInto_book B pos ts _ all c4 c' k4 d4
      (by rw [e4]; exact hB.trans g1)
    refine ⟨d5, ?_, fun q => n5 (n4 (n1 q))⟩
    have g5' : GrowsT c1.book.trees c'.book.trees := by
      have := g5
      unfold Grows at this
      rw [e4] at this
      exact this
    exact GrowsT.trans g1 g5'

instance b_readOpened (ids : Array Nat) (pos : Positions) : KeepsM (Blk.readOpened ids pos) :=
  ⟨fun c x c' h0 hd => by
    have h := (Blk.yields_iff _ _ _ _).2 h0
    unfold Blk.readOpened at h
    obtain ⟨S, c1, h1, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨rfl, eh1⟩ := (Blk.yields_statement _ _ _).1 h1
    obtain rfl := eh1.symm
    obtain ⟨B, c2, h2, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨rfl, eh2⟩ := (Blk.yields_theBook _ _ _).1 h2
    obtain rfl := eh2.symm
    obtain ⟨places, c3, h3, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨_, eh3⟩ := (Blk.yields_get _ _ _ _).1 h3
    obtain rfl := eh3.symm
    dsimp only at h
    obtain ⟨_, c4, h4, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨_, eh4⟩ := (Blk.yields_must _ _ _).1 h4
    obtain rfl := eh4.symm
    obtain ⟨cols, c5, h5, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨_, eh⟩ := (Blk.yields_get _ _ _ _).1 h
    obtain rfl := eh
    unfold Blk.openTrees at h5
    exact openTreesInto_book _ pos _ _ _ _ _ h5 hd (GrowsT.refl _)⟩

/-- A loop whose body never breaks off carries what its body carries. -/
theorem loop_inv {α β : Type} (I : β → Ctx → Prop) (f : α → β → Blk (ForInStep β))
    (hf : ∀ a b c r c1, (f a b).Yields c r c1 → I b c → ∃ b1, r = .yield b1 ∧ I b1 c1) :
    ∀ (l : List α) (b : β) (c : Ctx) (b' : β) (c' : Ctx),
      (forIn l b f).Yields c b' c' → I b c → I b' c'
  | [], b, c, b', c', h, hI => by
    rw [List.forIn_nil] at h
    obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).1 h
    exact hI
  | a :: l, b, c, b', c', h, hI => by
    rw [List.forIn_cons] at h
    obtain ⟨r, c1, h1, h2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨b1, rfl, hs⟩ := hf a b c r c1 h1 hI
    exact loop_inv I f hf l b1 c1 b' c' h2 hs

/-- What the loops of receiveOracles and adoptOracles carry: the trees have grown out of A; the run
is dry; book and noted rounds are those of c0. -/
def LoopI (A : Array Tree) (c0 : Ctx) (trees : Array Tree) (c : Ctx) : Prop :=
  GrowsT A trees ∧ c.ch.dry = true ∧ c.book = c0.book ∧ c.ch.noted = c0.ch.noted

instance b_receiveOracles (sent : Array OracleNotice) : KeepsM (Blk.receiveOracles sent) :=
  ⟨fun c x c' h0 hd => by
    have h := (Blk.yields_iff _ _ _ _).2 h0
    unfold Blk.receiveOracles at h
    obtain ⟨S, c1, h1, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨rfl, eh1⟩ := (Blk.yields_statement _ _ _).1 h1
    obtain rfl := eh1.symm
    obtain ⟨B, c2, h2, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨rfl, eh2⟩ := (Blk.yields_theBook _ _ _).1 h2
    obtain rfl := eh2.symm
    obtain ⟨first, c3, h3, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    have e3 : c3 = c := by
      have h3' := (Blk.yields_iff _ _ _ _).1 h3
      unfold Blk.firstTree at h3'
      cases h3'
      rfl
    obtain rfl := e3.symm
    obtain ⟨_, c4, h4, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨_, eh4⟩ := (Blk.yields_must _ _ _).1 h4
    obtain rfl := eh4.symm
    obtain ⟨_, c5, h5, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨_, eh5⟩ := (Blk.yields_must _ _ _).1 h5
    obtain rfl := eh5.symm
    obtain ⟨lay, c6, h6, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨_, eh6⟩ := (Blk.yields_get _ _ _ _).1 h6
    obtain rfl := eh6.symm
    obtain ⟨t1, c7, h7, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨t2, c8, h8, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨_, c9, h9, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨_, c10, h10, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨_, eh⟩ := (Blk.yields_pure _ _ _ _).1 h
    obtain rfl := eh
    have e10 := (Blk.yields_setBook _ _ _).1 h10
    have e9 : c9.ch = c8.ch ∧ c9.book = c8.book := by
      have h9' := (Blk.yields_iff _ _ _ _).1 h9
      unfold Blk.setStatement at h9'
      cases h9'
      exact ⟨rfl, rfl⟩
    rw [← Array.forIn_toList] at h7
    have k7 : LoopI c.book.trees c t1 c7 := by
      refine loop_inv (LoopI c.book.trees c) _ ?_ _ _ _ _ _ h7
        ⟨GrowsT.refl _, hd, rfl, rfl⟩
      intro s r d y d1 hy hI
      obtain ⟨n, d2, y1, y2⟩ := (Blk.yields_bind _ _ _ _ _).1 hy
      obtain ⟨_, d3, y3, y4⟩ := (Blk.yields_bind _ _ _ _ _).1 y2
      obtain ⟨_, rfl⟩ := (Blk.yields_pure _ _ _ _).1 y3
      obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).1 y4
      refine ⟨_, rfl, hI.1.trans (GrowsT.push _ _), ?_⟩
      have y1' := (Blk.yields_iff _ _ _ _).1 y1
      unfold Blk.recvRoot at y1'
      simp only [hI.2.1, if_true] at y1'
      cases y1'
      exact ⟨rfl, hI.2.2.1, hI.2.2.2⟩
    have k8 : LoopI c.book.trees c t2 c8 := by
      refine loop_inv (LoopI c.book.trees c) _ ?_ _ _ _ _ _ h8 k7
      intro i r d y d1 hy hI
      obtain ⟨_, d3, y3, y4⟩ := (Blk.yields_bind _ _ _ _ _).1 hy
      obtain ⟨_, rfl⟩ := (Blk.yields_pure _ _ _ _).1 y3
      obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).1 y4
      exact ⟨_, rfl, hI.1.trans (GrowsT.modify _ _ _ fun _ => rfl), hI.2⟩
    obtain ⟨g, d8, b8, n8⟩ := k8
    rw [e10]
    refine ⟨by show c9.ch.dry = true; rw [e9.1]; exact d8, g, fun q => ?_⟩
    have q' : NotesIn c9.ch.noted c.book.trees := by rw [e9.1, n8]; exact q
    exact NotesIn.grows q' g⟩

instance b_adoptOracles (sent : Array OracleNotice) (given : Array (Nat × Fmt.Src)) :
    KeepsM (Blk.adoptOracles sent given) :=
  ⟨fun c x c' h0 hd => by
    have h := (Blk.yields_iff _ _ _ _).2 h0
    unfold Blk.adoptOracles at h
    obtain ⟨S, c1, h1, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨rfl, eh1⟩ := (Blk.yields_statement _ _ _).1 h1
    obtain rfl := eh1.symm
    obtain ⟨B, c2, h2, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨rfl, eh2⟩ := (Blk.yields_theBook _ _ _).1 h2
    obtain rfl := eh2.symm
    obtain ⟨_, c4, h4, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨_, eh4⟩ := (Blk.yields_must _ _ _).1 h4
    obtain rfl := eh4.symm
    obtain ⟨_, c5, h5, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨_, eh5⟩ := (Blk.yields_must _ _ _).1 h5
    obtain rfl := eh5.symm
    obtain ⟨lay, c6, h6, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨_, eh6⟩ := (Blk.yields_get _ _ _ _).1 h6
    obtain rfl := eh6.symm
    obtain ⟨_, c6', h6', h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨_, eh6p⟩ := (Blk.yields_must _ _ _).1 h6'
    obtain rfl := eh6p.symm
    obtain ⟨t1, c7, h7, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨t2, c8, h8, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨_, c9, h9, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨_, c10, h10, h⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨_, eh⟩ := (Blk.yields_pure _ _ _ _).1 h
    obtain rfl := eh
    have e10 := (Blk.yields_setBook _ _ _).1 h10
    have e9 : c9.ch = c8.ch ∧ c9.book = c8.book := by
      have h9' := (Blk.yields_iff _ _ _ _).1 h9
      unfold Blk.setStatement at h9'
      cases h9'
      exact ⟨rfl, rfl⟩
    have k7 : LoopI c.book.trees c t1 c7 := by
      refine loop_inv (LoopI c.book.trees c) _ ?_ _ _ _ _ _ h7
        ⟨GrowsT.refl _, hd, rfl, rfl⟩
      intro i r d y d1 hy hI
      obtain ⟨_, d3, y3, y4⟩ := (Blk.yields_bind _ _ _ _ _).1 hy
      obtain ⟨_, rfl⟩ := (Blk.yields_pure _ _ _ _).1 y3
      obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).1 y4
      exact ⟨_, rfl, hI.1.trans (GrowsT.push _ _), hI.2⟩
    have k8 : LoopI c.book.trees c t2 c8 := by
      refine loop_inv (LoopI c.book.trees c) _ ?_ _ _ _ _ _ h8 k7
      intro i r d y d1 hy hI
      obtain ⟨_, d3, y3, y4⟩ := (Blk.yields_bind _ _ _ _ _).1 hy
      obtain ⟨_, rfl⟩ := (Blk.yields_pure _ _ _ _).1 y3
      obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).1 y4
      exact ⟨_, rfl, hI.1.trans (GrowsT.modify _ _ _ fun _ => rfl), hI.2⟩
    obtain ⟨g, d8, b8, n8⟩ := k8
    rw [e10]
    refine ⟨by show c9.ch.dry = true; rw [e9.1]; exact d8, g, fun q => ?_⟩
    have q' : NotesIn c9.ch.noted c.book.trees := by rw [e9.1, n8]; exact q
    exact NotesIn.grows q' g⟩

end OnBytes.Tie.Pv.Keeps.Book

#print axioms OnBytes.Tie.Pv.Keeps.Book.b_countOpening
#print axioms OnBytes.Tie.Pv.Keeps.Book.b_readOpened
#print axioms OnBytes.Tie.Pv.Keeps.Book.b_receiveOracles
#print axioms OnBytes.Tie.Pv.Keeps.Book.b_adoptOracles
