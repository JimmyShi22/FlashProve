-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Laws/LawGround.lean: each of the 60 calls of OnBytes/Iop/Ground.lean whose type ends in
`Blk` carries the relation `Alike G d` (OnBytes/TypedOracleCompiler/Laws/LawAlike.lean), for every G and d. So each
serves both laws.

Why. They are the ground of the walk: a routine that is written over these calls with pure, bind,
if, match and loops is then walked by a tactic.

How the 60 fall.
  52 are one text with equal values (class `Same`): 21 by the tactic `same_prim` (the call is a
  function of the context and touches none of the fields in which two contexts that are alike may
  differ); `item` and `readStored` by hand; `named` and `inPlace` in OnBytes/TypedOracleCompiler/Laws/LawKit.lean;
  24 by "unfold; walk"; `receiveOracles`, `countOpening` and `readOpened` by hand, over the book.
  8 are not: the value or an argument is in a relation that is not equality:
    `carries_close`         what is returned as drawn is equal but for the digest (`DrawnAlike`);
    `carries_theBook`, `carries_handOver`   the book that is returned is alike tree by tree
                            (`BookAlike G`);
    `carries_setBook`, `carries_takeColumns`, `carries_openTreesInto`, `carries_openTrees`,
    `carries_adoptOracles`  an argument (a book, a tree, the list of trees taken over) is alike.

Other names. `alike_open`, `alike_done`: tactics that take two contexts that are alike apart, and
put two together. `carries_get`: a value that is there on both sides or on neither. `same_of_close`:
a text that closes a round and goes on without the digest is one text with equal values. `walk`: the
kit's tactic with that step. `symbolsOf_alike`: the symbols are cut out of the columns by the tree's
shape alone.

Not claimed. Nothing on a block that fails but that the other fails under the same name. Nothing on
what a call tests. Two texts that differ in an argument that holds a value:
OnBytes/TypedOracleCompiler/Laws/LawDry.lean.

-/
import OnBytes.TypedOracleCompiler.Laws.LawAlike

namespace OnBytes.TwoLaws

open OnBytes

variable {G : ByteArray → ByteArray → ByteArray → ByteArray → Prop} {d : Bool}

-- alike_open takes two contexts that are alike apart, field by field, and makes the equal fields
-- one. Its names (dry, lf, lf', cu, cu', no, no', bk, bk', hlf, hcu, hno, hbk, hd) can be used
-- after it.
set_option hygiene false in
macro "alike_open" : tactic =>
  `(tactic| (
    intro c c' h
    obtain ⟨⟨dry, ft, sm, en, lf, cu, op, ro, la, ak, it, no⟩, st, bk, nt, kn, fl⟩ := c
    obtain ⟨⟨dry', ft', sm', en', lf', cu', op', ro', la', ak', it', no'⟩, st', bk', nt', kn',
      fl'⟩ := c'
    obtain ⟨h1, h2, h3, h4, hlf, hcu, h7, h8, h9, h10, h11, hno, h13, hbk, h15, h16, h17, hd⟩ := h
    dsimp only at h1 h2 h3 h4 hlf hcu h7 h8 h9 h10 h11 hno h13 hbk h15 h16 h17 hd
    subst h1 h2 h3 h4 h7 h8 h9 h10 h11 h13 h15 h16 h17))

/-- Two contexts are alike: each field by rfl or by a hypothesis at hand. -/
macro "alike_done" : tactic => `(tactic| (constructor <;> first | rfl | assumption))

/-- For a call that is written as a function of the context and touches none of the fields in which
two contexts that are alike may differ. -/
macro "same_prim " d:ident : tactic =>
  `(tactic| (
      refine ⟨?_⟩
      alike_open
      unfold $d
      try dsimp only
      repeat' split
      all_goals first
        | exact Out.err _
        | exact Out.ok rfl (by alike_done)
        | contradiction
        | (simp_all; done)))

/-! ## The calls of Ground.lean that are functions of the context: one text, equal values -/

instance same_fail {α : Type} (n : String) : Same (Alike G d) (Blk.fail n : Blk α) := by
  same_prim Blk.fail
instance same_must (b : Bool) (n : String) : Same (Alike G d) (Blk.must b n) := by
  same_prim Blk.must
instance same_test (b : Bool) (n : String) : Same (Alike G d) (Blk.test b n) := by
  same_prim Blk.test
instance same_check (n : String) (b : Bool) : Same (Alike G d) (Blk.check n b) := by
  same_prim Blk.check
instance same_onView {α : Type} (x : α) (f : Unit → α) : Same (Alike G d) (Blk.onView x f) := by
  same_prim Blk.onView
instance same_getOnView {α : Type} (x : α) (f : Unit → Option α) (n : String) :
    Same (Alike G d) (Blk.getOnView x f n) := by
  same_prim Blk.getOnView
instance same_testOnView (f : Unit → Bool) (n : String) :
    Same (Alike G d) (Blk.testOnView f n) := by
  same_prim Blk.testOnView
instance same_checkOnView (n : String) (f : Unit → Bool) :
    Same (Alike G d) (Blk.checkOnView n f) := by
  same_prim Blk.checkOnView
instance same_get {α : Type} (x : Option α) (n : String) : Same (Alike G d) (Blk.get x n) := by
  same_prim Blk.get
instance same_isDry : Same (Alike G d) Blk.isDry := by same_prim Blk.isDry
instance same_samples : Same (Alike G d) Blk.samples := by same_prim Blk.samples
instance same_firstTree : Same (Alike G d) Blk.firstTree := by same_prim Blk.firstTree
instance same_lastEntry : Same (Alike G d) Blk.lastEntry := by same_prim Blk.lastEntry
instance same_note (w : String) (v : E) : Same (Alike G d) (Blk.note w v) := by
  same_prim Blk.note
instance same_noteBy (w : String) (v : Unit → E) : Same (Alike G d) (Blk.noteBy w v) := by
  same_prim Blk.noteBy
instance same_statement : Same (Alike G d) Blk.statement := by same_prim Blk.statement
instance same_setStatement (S : Statement) : Same (Alike G d) (Blk.setStatement S) := by
  same_prim Blk.setStatement
instance same_recvRoot : Same (Alike G d) Blk.recvRoot := by same_prim Blk.recvRoot
instance same_requireRows (r : Nat) : Same (Alike G d) (Blk.requireRows r) := by
  same_prim Blk.requireRows
instance same_onOracle (o : Nat) (f : Oracle → Oracle) : Same (Alike G d) (Blk.onOracle o f) := by
  same_prim Blk.onOracle
instance same_onGroup (g : Nat) (f : Group → Group) : Same (Alike G d) (Blk.onGroup g f) := by
  same_prim Blk.onGroup

/-! ## The calls in which the two sides may differ: in an argument, or in the value -/

/-- A value that is there on both sides or on neither. -/
theorem carries_get {α : Type} {P : α → α → Prop} {x y : Option α} (h : OptAlike P x y)
    (n : String) : Carries (Alike G d) P (Blk.get x n) (Blk.get y n) := by
  intro c c' hc
  cases h with
  | none => exact Out.err _
  | some k => exact Out.ok k hc

theorem carries_theBook : Carries (Alike G d) (BookAlike G) Blk.theBook Blk.theBook := by
  alike_open
  exact Out.ok hbk (by alike_done)

theorem carries_setBook {B B' : TreeBook} (hB : BookAlike G B B') :
    Carries (Alike G d) Eq (Blk.setBook B) (Blk.setBook B') := by
  alike_open
  exact Out.ok rfl (by alike_done)

theorem carries_handOver :
    Carries (Alike G d) (fun p q => p.1 = q.1 ∧ BookAlike G p.2 q.2) Blk.handOver Blk.handOver := by
  alike_open
  exact Out.ok ⟨rfl, hbk⟩ (by alike_done)

/-- An item of the open message: the digest is no item. -/
instance same_item (i : Fmt.Item) (x : Fmt.ItemValue) : Same (Alike G d) (Blk.item i x) := by
  refine ⟨?_⟩
  alike_open
  unfold Blk.item
  cases dry with
  | true => exact Out.ok rfl (by alike_done)
  | false =>
    cases hcu with
    | some hr =>
      rename_i r r'
      obtain ⟨v, dr⟩ := r
      obtain ⟨v', dr'⟩ := r'
      obtain ⟨hv, hdr⟩ := hr
      dsimp only at hv hdr
      subst hv
      cases v with
      | nil => exact Out.err _
      | cons g gs =>
        exact Out.ok rfl (by constructor <;> first | rfl | assumption | exact .some ⟨rfl, hdr⟩)
    | none =>
      cases hlf with
      | nil => exact Out.err _
      | cons hr ht =>
        rename_i r r' t t'
        obtain ⟨v, dr⟩ := r
        obtain ⟨v', dr'⟩ := r'
        obtain ⟨hv, hdr⟩ := hr
        dsimp only at hv hdr
        subst hv
        cases v with
        | nil => exact Out.err _
        | cons g gs =>
          exact Out.ok rfl (by constructor <;> first | rfl | assumption | exact .some ⟨rfl, hdr⟩)

/-- Closing a round: what is returned as drawn is equal but for the digest. -/
theorem carries_close (n : String) (k : Fmt.Kind) (nz : Nat) :
    Carries (Alike G d) DrawnAlike (Blk.close n k nz) (Blk.close n k nz) := by
  alike_open
  unfold Blk.close
  cases en with
  | nil => exact Out.err _
  | cons e es =>
    dsimp only
    generalize hs : Chan.settled _ = s
    generalize hs' : Chan.settled _ = s'
    have es' : s = s' := by rw [← hs, ← hs']; rfl
    subst es'
    split
    · exact Out.err _
    · cases dry with
      | true =>
        exact Out.ok (DrawnAlike.refl _) (by
          constructor <;> first | rfl | assumption | exact hno.push ⟨rfl, rfl, rfl, .nil, rfl⟩)
      | false =>
        cases hcu with
        | some hr =>
          rename_i r r'
          obtain ⟨v, ⟨el, po, tr, dg⟩⟩ := r
          obtain ⟨v', ⟨el', po', tr', dg'⟩⟩ := r'
          obtain ⟨hv, ⟨e1, e2, e3⟩⟩ := hr
          dsimp only at hv e1 e2 e3
          subst hv e1 e2 e3
          simp only [Bool.false_eq_true, ↓reduceIte]
          split
          · exact Out.ok ⟨rfl, rfl, rfl⟩ (by
              constructor <;> first | rfl | assumption | exact .none)
          · exact Out.err _
        | none =>
          cases hlf with
          | nil => exact Out.err _
          | cons hr ht =>
            rename_i r r' t t'
            obtain ⟨v, ⟨el, po, tr, dg⟩⟩ := r
            obtain ⟨v', ⟨el', po', tr', dg'⟩⟩ := r'
            obtain ⟨hv, ⟨e1, e2, e3⟩⟩ := hr
            dsimp only at hv e1 e2 e3
            subst hv e1 e2 e3
            simp only [Bool.false_eq_true, ↓reduceIte]
            split
            · exact Out.ok ⟨rfl, rfl, rfl⟩ (by
                constructor <;> first | rfl | assumption | exact .none)
            · exact Out.err _

/-- A text that closes a round and goes on without the digest is one text with equal values. -/
theorem same_of_close {β : Type} (n : String) (k : Fmt.Kind) (nz : Nat) {f : Fmt.Drawn → Blk β}
    (hf : ∀ e p t g g', Carries (Alike G d) Eq (f ⟨e, p, t, g⟩) (f ⟨e, p, t, g'⟩)) :
    Same (Alike G d) (Blk.close n k nz >>= f) :=
  ⟨Carries.bind (carries_close n k nz) fun x x' h => by
    obtain ⟨e, p, t, g⟩ := x
    obtain ⟨e', p', t', g'⟩ := x'
    obtain ⟨h1, h2, h3⟩ := h
    dsimp only at h1 h2 h3
    subst h1 h2 h3
    exact hf _ _ _ _ _⟩

/-- The columns of a tree: on a view the tree's source is not read; a dry run notes it. -/
theorem carries_takeColumns {t t' : Tree} (ht : TreeAlike G t t') (xs : Array Nat) :
    Carries (Alike G d) Eq (Blk.takeColumns t xs) (Blk.takeColumns t' xs) := by
  obtain ⟨sh, nu, sr, pa, ol, li⟩ := t
  obtain ⟨sh', nu', sr', pa', ol', li'⟩ := t'
  obtain ⟨e1, e2, hs, e4, e5, e6⟩ := ht
  dsimp only at e1 e2 hs e4 e5 e6
  subst e1 e2 e4 e5 e6
  alike_open
  unfold Blk.takeColumns
  have hz := hno.size_eq
  cases dry with
  | true =>
    simp only [↓reduceIte, Array.isEmpty_iff_size_eq_zero, hz]
    split
    · exact Out.err _
    · exact Out.ok rfl (by
        constructor <;> first
          | rfl
          | assumption
          | exact hno.modify _ fun a b hab => ⟨hab.entry, hab.kind, hab.items,
              hab.opens.append (.cons ⟨rfl, hs⟩ .nil), hab.stored⟩)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · exact Out.ok rfl (by alike_done)
    · exact Out.err _

instance same_readStored (t : Fmt.Stored) (p : Positions) :
    Same (Alike G d) (Blk.readStored t p) := by
  refine ⟨?_⟩
  alike_open
  unfold Blk.readStored
  have hz := hno.size_eq
  cases dry with
  | true =>
    simp only [↓reduceIte, Array.isEmpty_iff_size_eq_zero, hz]
    split
    · exact Out.err _
    · exact Out.ok rfl (by
        constructor <;> first
          | rfl
          | assumption
          | exact hno.modify _ fun a b hab => ⟨hab.entry, hab.kind, hab.items, hab.opens,
              by show a.stored ++ [t] = b.stored ++ [t]; rw [hab.stored]⟩)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · exact Out.ok rfl (by alike_done)
    · exact Out.err _

/-! ## The tactic for one text, with the closing of a round -/

/-- The kit's tactic same, and before a bind: a closing of a round whose digest is not read. If the
text behind the closing reads the digest, the two sides differ and the step fails. -/
macro "walk" : tactic =>
  `(tactic| repeat' first
      | infer_instance
      | intro _
      | (with_reducible refine same_of_close _ _ _ (fun _ _ _ _ _ => ?_); try dsimp only
         refine Carries.of_same ?_)
      | with_reducible apply Same.bind
      | split
      | dsimp only)

/-! ## The calls of Ground.lean that are written over these: one text, equal values -/

instance same_recvE : Same (Alike G d) Blk.recvE := by unfold Blk.recvE; walk
instance same_recvAnswer : Same (Alike G d) Blk.recvAnswer := by unfold Blk.recvAnswer; walk
instance same_recvEsInto (n : Nat) (acc : Array E) : Same (Alike G d) (Blk.recvEsInto n acc) := by
  induction n generalizing acc with
  | zero => unfold Blk.recvEsInto; walk
  | succ n ih => unfold Blk.recvEsInto; walk
instance same_recvEs (n : Nat) : Same (Alike G d) (Blk.recvEs n) := by unfold Blk.recvEs; walk
instance same_closeEmpty (n : String) : Same (Alike G d) (Blk.closeEmpty n) := by
  unfold Blk.closeEmpty; walk
instance same_closeElems (n : String) (nz : Nat) : Same (Alike G d) (Blk.closeElems n nz) := by
  unfold Blk.closeElems; walk
instance same_closeOne (n : String) (k : Fmt.Kind) (nz : Nat) :
    Same (Alike G d) (Blk.closeOne n k nz) := by
  unfold Blk.closeOne; walk
instance same_closePositions (n : String) (l : Nat) :
    Same (Alike G d) (Blk.closePositions n l) := by
  unfold Blk.closePositions; walk
instance same_oracle (o : Nat) : Same (Alike G d) (Blk.oracle o) := by unfold Blk.oracle; walk
instance same_group (g : Nat) : Same (Alike G d) (Blk.group g) := by unfold Blk.group; walk
instance same_newGroup (c m : Nat) : Same (Alike G d) (Blk.newGroup c m) := by
  unfold Blk.newGroup; walk
instance same_spendAsMask (o : Nat) : Same (Alike G d) (Blk.spendAsMask o) := by
  unfold Blk.spendAsMask; walk
instance same_join (g o : Nat) (k : Bool) : Same (Alike G d) (Blk.join g o k) := by
  unfold Blk.join; walk
instance same_takeMask (o : Nat) : Same (Alike G d) (Blk.takeMask o) := by
  unfold Blk.takeMask; walk
instance same_takeMasksInto (o n : Nat) (acc : Array Nat) :
    Same (Alike G d) (Blk.takeMasksInto o n acc) := by
  induction n generalizing acc with
  | zero => unfold Blk.takeMasksInto; walk
  | succ n ih => unfold Blk.takeMasksInto; walk
instance same_takeMasks (o n : Nat) : Same (Alike G d) (Blk.takeMasks o n) := by
  unfold Blk.takeMasks; walk
instance same_closeLedger (o : Nat) : Same (Alike G d) (Blk.closeLedger o) := by
  unfold Blk.closeLedger; walk
instance same_addRow (g : Nat) (r : Row) : Same (Alike G d) (Blk.addRow g r) := by
  unfold Blk.addRow; walk
instance same_addRowsOnView (g : Nat) (r : Unit → Option (List Row)) :
    Same (Alike G d) (Blk.addRowsOnView g r) := by
  unfold Blk.addRowsOnView; walk
instance same_layout (g : Nat) : Same (Alike G d) (Blk.layout g) := by unfold Blk.layout; walk
instance same_beginRun (g : Nat) : Same (Alike G d) (Blk.beginRun g) := by
  unfold Blk.beginRun; walk
instance same_requireSampled (r : Row) : Same (Alike G d) (Blk.requireSampled r) := by
  unfold Blk.requireSampled; walk
instance same_requireAllTested : Same (Alike G d) Blk.requireAllTested := by
  unfold Blk.requireAllTested; walk
instance same_sampledElsewhere (m : Nat) (o : Statement) (t : Nat) :
    Same (Alike G d) (Blk.sampledElsewhere m o t) := by
  unfold Blk.sampledElsewhere; walk

/-! ## The calls of Ground.lean that read or write the book of trees -/

theorem ArrAlike.getD {α : Type} {P : α → α → Prop} {a b : Array α} (h : ArrAlike P a b) (i : Nat)
    {x y : α} (hx : P x y) : P (a.getD i x) (b.getD i y) := by
  have h1 := h i
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  generalize a[i]? = u at h1
  generalize b[i]? = v at h1
  cases h1 with
  | none => exact hx
  | some k => exact k

instance same_receiveOracles (s : Array OracleNotice) :
    Same (Alike G d) (Blk.receiveOracles s) := by
  refine ⟨?_⟩
  unfold Blk.receiveOracles
  refine Carries.bind_same fun S => ?_
  refine Carries.bind carries_theBook fun B B' hB => ?_
  rw [hB.place, hB.trees.size_eq]
  refine Carries.bind_same fun first => ?_
  refine Carries.bind_same fun _ => ?_
  refine Carries.bind_same fun _ => ?_
  refine Carries.bind_same fun lay => ?_
  dsimp only
  refine Carries.bind (Carries.forIn_array _ hB.trees fun a x x' hx => ?_) fun t t' ht => ?_
  · refine Carries.bind_same fun n => ?_
    refine Carries.bind_same fun _ => ?_
    exact Carries.pure (.yield (hx.push ⟨rfl, rfl, .own n, rfl, rfl, rfl⟩))
  · refine Carries.bind (Carries.forIn_list _ ht fun i x x' hx => ?_) fun u u' hu => ?_
    · refine Carries.bind_same fun _ => ?_
      exact Carries.pure (.yield (hx.modify _ fun a b h => ⟨h.shape, h.number, h.src,
        by dsimp only; rw [h.parts], by dsimp only; rw [h.oneList], h.lists⟩))
    · refine Carries.bind_same fun _ => ?_
      refine Carries.bind (carries_setBook ⟨hu, rfl⟩) fun _ _ _ => ?_
      exact Carries.pure rfl

instance same_countOpening (t : Nat) : Same (Alike G d) (Blk.countOpening t) := by
  refine ⟨?_⟩
  unfold Blk.countOpening
  refine Carries.bind_same fun S => ?_
  refine Carries.bind carries_theBook fun B B' hB => ?_
  refine Carries.bind (carries_get (hB.trees t) _) fun tr tr' ht => ?_
  dsimp only
  rw [ht.parts, ht.oneList, ht.lists]
  refine Carries.bind_same fun _ => ?_
  refine Carries.bind_same fun _ => ?_
  exact carries_setBook ⟨hB.trees.modify _ fun a b h => ⟨h.shape, h.number, h.src, h.parts,
    h.oneList, by show a.lists + 1 = b.lists + 1; rw [h.lists]⟩, hB.place⟩

theorem carries_openTreesInto {B B' : TreeBook} (hB : BookAlike G B B') (pos : Positions)
    (ts : List Nat) (acc : Array (Nat × Array Nat × Array (Array F))) :
    Carries (Alike G d) Eq (Blk.openTreesInto B pos ts acc) (Blk.openTreesInto B' pos ts acc) := by
  induction ts generalizing acc with
  | nil => unfold Blk.openTreesInto; exact Carries.pure rfl
  | cons t ts ih =>
    unfold Blk.openTreesInto
    refine Carries.bind_same fun _ => ?_
    refine Carries.bind (carries_get (hB.trees t) _) fun tr tr' ht => ?_
    have e : Blk.ownList tr pos = Blk.ownList tr' pos := by unfold Blk.ownList; rw [ht.shape]
    dsimp only
    rw [ht.shape, e]
    refine Carries.bind_same fun _ => ?_
    refine Carries.bind (carries_takeColumns ht _) fun c _ hc => ?_
    subst hc
    exact ih _

theorem carries_openTrees {B B' : TreeBook} (hB : BookAlike G B B') (pos : Positions)
    (ts : List Nat) :
    Carries (Alike G d) Eq (Blk.openTrees B pos ts) (Blk.openTrees B' pos ts) :=
  carries_openTreesInto hB pos ts #[]

/-- The symbols of an oracle message are cut out of the columns by the tree's shape alone. -/
theorem symbolsOf_alike {B B' : TreeBook} (hB : BookAlike G B B') (S : Statement)
    (pos : Positions) (cols : List (Nat × Array Nat × Array (Array F))) (o : Nat) (p : Nat × Nat) :
    Blk.symbolsOf S B pos cols o p = Blk.symbolsOf S B' pos cols o p := by
  unfold Blk.symbolsOf
  have h := hB.trees p.1
  generalize B.trees[p.1]? = x at h ⊢
  generalize B'.trees[p.1]? = y at h ⊢
  cases h with
  | none => rfl
  | some k => simp [k.shape]

instance same_readOpened (ids : Array Nat) (p : Positions) :
    Same (Alike G d) (Blk.readOpened ids p) := by
  refine ⟨?_⟩
  unfold Blk.readOpened
  refine Carries.bind_same fun S => ?_
  refine Carries.bind carries_theBook fun B B' hB => ?_
  have e1 : ∀ t, (B.trees[t]?).map (fun x : Tree => x.parts) =
      (B'.trees[t]?).map (fun x : Tree => x.parts) :=
    fun t => hB.trees.map_eq _ (fun _ _ h => h.parts) t
  simp only [hB.place, e1, symbolsOf_alike hB]
  refine Carries.bind_same fun places => ?_
  refine Carries.bind_same fun _ => ?_
  refine Carries.bind (carries_openTrees hB _ _) fun c _ hc => ?_
  subst hc
  exact Carries.of_same inferInstance

/-- Trees that are taken over: their numbers are equal, their sources go together. -/
theorem carries_adoptOracles (s : Array OracleNotice) {g g' : Array (Nat × Fmt.Src)}
    (hg : ArrAlike (fun x y => x.1 = y.1 ∧ SrcAlike G x.2 y.2) g g') :
    Carries (Alike G d) Eq (Blk.adoptOracles s g) (Blk.adoptOracles s g') := by
  unfold Blk.adoptOracles
  refine Carries.bind_same fun S => ?_
  refine Carries.bind carries_theBook fun B B' hB => ?_
  rw [hB.place, hB.trees.size_eq, hg.size_eq]
  refine Carries.bind_same fun _ => ?_
  refine Carries.bind_same fun _ => ?_
  refine Carries.bind_same fun lay => ?_
  refine Carries.bind_same fun _ => ?_
  dsimp only
  refine Carries.bind (Carries.forIn_list _ hB.trees fun a x x' hx => ?_) fun t t' ht => ?_
  · refine Carries.bind_same fun _ => ?_
    have h0 := hg.getD a (x := (0, Fmt.Src.own 0)) (y := (0, Fmt.Src.own 0)) ⟨rfl, .own 0⟩
    exact Carries.pure (.yield (hx.push ⟨rfl, h0.1, h0.2, rfl, rfl, rfl⟩))
  · refine Carries.bind (Carries.forIn_list _ ht fun i x x' hx => ?_) fun u u' hu => ?_
    · refine Carries.bind_same fun _ => ?_
      exact Carries.pure (.yield (hx.modify _ fun a b h => ⟨h.shape, h.number, h.src,
        by dsimp only; rw [h.parts], h.oneList, h.lists⟩))
    · refine Carries.bind_same fun _ => ?_
      refine Carries.bind (carries_setBook ⟨hu, rfl⟩) fun _ _ _ => ?_
      exact Carries.pure rfl

end OnBytes.TwoLaws
