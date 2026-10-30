-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/KeepsKit.lean: of the rule of OnBytes/Iop/Ground.lean, "only this file writes
the channel or the field failed", four parts as theorems. No walked block changes the channel's flag
dry. None wipes a mark that stood in the field failed when the block began. In a run on a view the
plan's unused entries and the view's rounds that are not yet closed are used up together, from the
front, and what a round has drawn is not changed. And the view's rounds that are not yet begun
behind a block are the last of those before it. One class for all four, Keeps.

What the class does not say. It compares the context before a block with the context after it, where
the block succeeds. Of the channel it speaks of dry, entries, cur and left alone, and of a round
that is not yet closed only of what it has drawn. The name of a mark may change. And it
holds of a block that catches a failure and so drops a mark that was made inside it: as a function
of the context such a block is a block without that test, and no property of the function can tell
the two apart (KeepsGuard.lean [not in this library], keeps_catches). That no walked routine catches
a failure is a reading of their texts, and the kit has no rule for a catch; it is no theorem.

The two properties KeepsViewB and KeepsMark follow from the class (Keeps.viewB, Keeps.mark).

 1. the two definitions, to the letter of a note of this project that is not in this library; Kept;
    Keeps; KeepsDry and KeepsFailed, to the letter of a second such text; KeepsRounds; Keeps is the
    conjunction of the three (keeps_iff).
 2. closure rules: pure, bind, map, if, loops over lists and arrays.
 3. the tactic keeps: instances first, then bind, match and if by cases.
 4. each call of Ground.lean.

Tactics of this file.
  keeps: proves Keeps of a block: it takes an instance where one reaches, and else goes one step
    into the block's text (a binder, a bind, a match or an if, a let) and goes on.
  keeps_prim d: proves Keeps of a call d that is written as a function of the context: it unfolds d,
    goes through its cases, and closes each case: a failure, or a context with the same flag dry,
    the same or a new mark, and the same entries, cur and left.
  keeps_flags d: for the two calls that write entries, cur or left (Blk.item, Blk.close): the flag
    dry and the mark alone; the rest is by OnBytes/Iop/GroundLaws.lean (item_inv, close_inv) and by
    cases.
-/
import OnBytes.Iop.GroundLaws

namespace OnBytes.L5

open OnBytes

/-- A run on a view stays a run on a view. In the letters of a note of this project
that is not in this library. -/
def KeepsViewB {α : Type} (b : Blk α) : Prop :=
  ∀ c x c', c.ch.dry = false → b.Yields c x c' → c'.ch.dry = false

/-- In a run on a view a mark is not cleared. In the letters of the same note. -/
def KeepsMark {α : Type} (b : Blk α) : Prop :=
  ∀ c x c', c.ch.dry = false → b.Yields c x c' → c'.failed = none → c.failed = none

/-- c' has the flag dry of c, and has a mark if c has one. In a run on a view, c' has the plan's
unused entries of c but for the first k, and its rounds that are not yet closed are those of c but
for the first k, as far as what they have drawn goes. The view's rounds that are not yet begun in c'
are the last of those of c. -/
structure Kept (c c' : Ctx) : Prop where
  dry : c'.ch.dry = c.ch.dry
  mark : c'.failed = none → c.failed = none
  tail : c.ch.dry = false → ∃ k, c'.ch.entries = c.ch.entries.drop k ∧
    c'.ch.pending.map (·.drawn) = (c.ch.pending.drop k).map (·.drawn)
  left : c'.ch.left <:+ c.ch.left

theorem Kept.refl (c : Ctx) : Kept c c := ⟨rfl, id, fun _ => ⟨0, rfl, rfl⟩, List.suffix_refl _⟩

theorem Kept.trans {a b c : Ctx} (h1 : Kept a b) (h2 : Kept b c) : Kept a c :=
  ⟨h2.dry.trans h1.dry, fun h => h1.mark (h2.mark h), fun hd => by
    obtain ⟨k1, e1, p1⟩ := h1.tail hd
    obtain ⟨k2, e2, p2⟩ := h2.tail (h1.dry.trans hd)
    refine ⟨k1 + k2, by rw [e2, e1, List.drop_drop], ?_⟩
    rw [p2, List.map_drop, p1, ← List.map_drop, List.drop_drop], h2.left.trans h1.left⟩

/-- A context with the same flag dry, the same unused entries and the same rounds not yet closed. -/
theorem Kept.same {c c' : Ctx} (hd : c'.ch.dry = c.ch.dry)
    (hm : c'.failed = none → c.failed = none) (he : c'.ch.entries = c.ch.entries)
    (hp : c'.ch.pending = c.ch.pending) (hl : c'.ch.left = c.ch.left) : Kept c c' :=
  ⟨hd, hm, fun _ => ⟨0, he, by rw [hp]; rfl⟩, by rw [hl]; exact List.suffix_refl _⟩

/-- Wherever the block succeeds, the context that it leaves is Kept. In both readings. -/
class Keeps {α : Type} (b : Blk α) : Prop where
  out : ∀ c x c', b c = .ok (x, c') → Kept c c'

theorem Keeps.viewB {α : Type} (b : Blk α) [h : Keeps b] : KeepsViewB b :=
  fun c x c' hd hy => ((h.out c x c' ((Blk.yields_iff b c x c').1 hy)).dry).trans hd

theorem Keeps.mark {α : Type} (b : Blk α) [h : Keeps b] : KeepsMark b :=
  fun c x c' _ hy => (h.out c x c' ((Blk.yields_iff b c x c').1 hy)).mark

/-- The definition of a text of this project that is not in this library, to the letter. -/
def KeepsDry {α : Type} (b : Blk α) : Prop := ∀ c x c', b.Yields c x c' → c'.ch.dry = c.ch.dry

/-- The definition of the same text, to the letter. -/
def KeepsFailed {α : Type} (b : Blk α) : Prop :=
  ∀ c x c', b.Yields c x c' → c'.failed = none → c.failed = none

/-- In a run on a view the unused entries and the rounds not yet closed go together, from the
front; and of the view's rounds that are not yet begun the last are left. -/
def KeepsRounds {α : Type} (b : Blk α) : Prop :=
  ∀ c x c', b.Yields c x c' →
    (c.ch.dry = false → ∃ k, c'.ch.entries = c.ch.entries.drop k ∧
      c'.ch.pending.map (·.drawn) = (c.ch.pending.drop k).map (·.drawn)) ∧
    c'.ch.left <:+ c.ch.left

/-- Keeps is the three together. -/
theorem keeps_iff {α : Type} (b : Blk α) :
    Keeps b ↔ KeepsDry b ∧ KeepsFailed b ∧ KeepsRounds b :=
  ⟨fun h => ⟨fun c x c' hy => (h.out c x c' ((Blk.yields_iff b c x c').1 hy)).dry,
      fun c x c' hy => (h.out c x c' ((Blk.yields_iff b c x c').1 hy)).mark,
      fun c x c' hy => ⟨(h.out c x c' ((Blk.yields_iff b c x c').1 hy)).tail,
        (h.out c x c' ((Blk.yields_iff b c x c').1 hy)).left⟩⟩,
    fun h => ⟨fun c x c' e => ⟨h.1 c x c' ((Blk.yields_iff b c x c').2 e),
      h.2.1 c x c' ((Blk.yields_iff b c x c').2 e),
      (h.2.2 c x c' ((Blk.yields_iff b c x c').2 e)).1,
      (h.2.2 c x c' ((Blk.yields_iff b c x c').2 e)).2⟩⟩⟩

/-! ## Closure rules -/

instance keeps_pure {α : Type} (a : α) : Keeps (pure a : Blk α) :=
  ⟨fun c x c' h => by cases h; exact Kept.refl _⟩

theorem Keeps.bind {α β : Type} {b : Blk α} {f : α → Blk β} (hb : Keeps b)
    (hf : ∀ x, Keeps (f x)) : Keeps (b >>= f) :=
  ⟨fun c y c2 h => by
    obtain ⟨x, c1, h1, h2⟩ := (Blk.yields_bind b f c c2 y).1 ((Blk.yields_iff _ _ _ _).2 h)
    exact (hb.out _ _ _ ((Blk.yields_iff _ _ _ _).1 h1)).trans
      ((hf x).out _ _ _ ((Blk.yields_iff _ _ _ _).1 h2))⟩

instance keeps_bind {α β : Type} (b : Blk α) (f : α → Blk β) [hb : Keeps b]
    [hf : ∀ x, Keeps (f x)] : Keeps (b >>= f) := Keeps.bind hb hf

instance keeps_map {α β : Type} (g : α → β) (b : Blk α) [hb : Keeps b] : Keeps (g <$> b) := by
  have e : g <$> b = b >>= fun x => pure (g x) := (bind_pure_comp g b).symm
  rw [e]; infer_instance

instance keeps_ite {α : Type} (p : Prop) [Decidable p] (a b : Blk α) [ha : Keeps a]
    [hb : Keeps b] : Keeps (if p then a else b) := by
  split <;> assumption

instance keeps_dite {α : Type} (p : Prop) [Decidable p] (a : p → Blk α) (b : ¬p → Blk α)
    [ha : ∀ h, Keeps (a h)] [hb : ∀ h, Keeps (b h)] : Keeps (dite p a b) := by
  split
  · exact ha _
  · exact hb _

instance keeps_forIn_list {α β : Type} (l : List α) (init : β)
    (f : α → β → Blk (ForInStep β)) [hf : ∀ a b, Keeps (f a b)] : Keeps (forIn l init f) := by
  induction l generalizing init with
  | nil => rw [List.forIn_nil]; infer_instance
  | cons a l ih =>
    rw [List.forIn_cons]
    refine Keeps.bind (hf a init) fun r => ?_
    cases r with
    | done b => exact keeps_pure b
    | yield b => exact ih b

instance keeps_forIn_array {α β : Type} (l : Array α) (init : β)
    (f : α → β → Blk (ForInStep β)) [hf : ∀ a b, Keeps (f a b)] : Keeps (forIn l init f) := by
  rw [← Array.forIn_toList]; infer_instance

instance keeps_foldlM_list {α β : Type} (l : List α) (init : β) (f : β → α → Blk β)
    [hf : ∀ b a, Keeps (f b a)] : Keeps (l.foldlM f init) := by
  induction l generalizing init with
  | nil => rw [List.foldlM_nil]; infer_instance
  | cons a l ih =>
    rw [List.foldlM_cons]
    exact Keeps.bind (hf init a) fun r => ih r

instance keeps_foldlM_array {α β : Type} (l : Array α) (init : β) (f : β → α → Blk β)
    [hf : ∀ b a, Keeps (f b a)] : Keeps (l.foldlM f init) := by
  rw [← Array.foldlM_toList]; infer_instance

instance keeps_forM_list {α : Type} (l : List α) (f : α → Blk PUnit) [hf : ∀ a, Keeps (f a)] :
    Keeps (l.forM f) := by
  induction l with
  | nil => exact keeps_pure _
  | cons a l ih => exact Keeps.bind (hf a) fun _ => ih

instance keeps_forM_array {α : Type} (l : Array α) (f : α → Blk PUnit) [hf : ∀ a, Keeps (f a)] :
    Keeps (l.forM f) := by
  unfold Array.forM; infer_instance

/-! ## The tactic -/

/-- Instances where they reach; else one step: a binder, a bind, a let, a match or an if. -/
macro "keeps" : tactic =>
  `(tactic| repeat' first
      | infer_instance
      | intro _
      | apply Keeps.bind
      | split
      | dsimp only)

/-- For a call that is written as a function of the context. -/
macro "keeps_prim " d:ident : tactic =>
  `(tactic| (
      refine ⟨fun c x c' h => ?_⟩
      unfold $d at h
      try dsimp only at h
      repeat' (split at h)
      all_goals first
        | (cases h; done)
        | (cases h; exact Kept.same rfl id rfl rfl rfl)
        | (cases h; exact Kept.same rfl (fun e => nomatch e) rfl rfl rfl)))

/-- For the two calls that write the unused entries or the rounds not yet closed: the flag dry and
the mark alone. -/
macro "keeps_flags " d:ident : tactic =>
  `(tactic| (
      intro c x c' h
      unfold $d at h
      try dsimp only at h
      repeat' (split at h)
      all_goals first
        | (cases h; done)
        | (cases h; exact ⟨rfl, id⟩)
        | (cases h; exact ⟨rfl, fun e => nomatch e⟩)))

/-! ## The calls of Ground.lean that are functions of the context -/

instance keeps_fail {α : Type} (n : String) : Keeps (Blk.fail n : Blk α) := by keeps_prim Blk.fail
instance keeps_must (b : Bool) (n : String) : Keeps (Blk.must b n) := by keeps_prim Blk.must
instance keeps_test (b : Bool) (n : String) : Keeps (Blk.test b n) := by keeps_prim Blk.test
instance keeps_check (n : String) (b : Bool) : Keeps (Blk.check n b) := by keeps_prim Blk.check
instance keeps_onView {α : Type} (d : α) (f : Unit → α) :
    Keeps (Blk.onView d f) := by
  keeps_prim Blk.onView
instance keeps_getOnView {α : Type} (d : α) (f : Unit → Option α) (n : String) :
    Keeps (Blk.getOnView d f n) := by
  keeps_prim Blk.getOnView
instance keeps_testOnView (f : Unit → Bool) (n : String) : Keeps (Blk.testOnView f n) := by
  keeps_prim Blk.testOnView
instance keeps_checkOnView (n : String) (f : Unit → Bool) : Keeps (Blk.checkOnView n f) := by
  keeps_prim Blk.checkOnView
instance keeps_get {α : Type} (x : Option α) (n : String) :
    Keeps (Blk.get x n) := by
  keeps_prim Blk.get
instance keeps_isDry : Keeps Blk.isDry := by keeps_prim Blk.isDry
instance keeps_samples : Keeps Blk.samples := by keeps_prim Blk.samples
instance keeps_firstTree : Keeps Blk.firstTree := by keeps_prim Blk.firstTree
instance keeps_lastEntry : Keeps Blk.lastEntry := by keeps_prim Blk.lastEntry
instance keeps_note (w : String) (v : E) : Keeps (Blk.note w v) := by keeps_prim Blk.note
instance keeps_noteBy (w : String) (v : Unit → E) :
    Keeps (Blk.noteBy w v) := by
  keeps_prim Blk.noteBy
instance keeps_statement : Keeps Blk.statement := by keeps_prim Blk.statement
instance keeps_setStatement (S : Statement) :
    Keeps (Blk.setStatement S) := by
  keeps_prim Blk.setStatement
theorem item_flags (i : Fmt.Item) (d : Fmt.ItemValue) : ∀ c x c', Blk.item i d c = .ok (x, c') →
    c'.ch.dry = c.ch.dry ∧ (c'.failed = none → c.failed = none) := by keeps_flags Blk.item
theorem item_left (i : Fmt.Item) (d : Fmt.ItemValue) : ∀ c x c', Blk.item i d c = .ok (x, c') →
    c'.ch.left <:+ c.ch.left := by
  intro c x c' h
  unfold Blk.item at h
  split at h
  · cases h
    exact ⟨[], rfl⟩
  · cases hc : c.ch.cur with
    | some r =>
      simp only [hc] at h
      cases hv : r.vals with
      | nil => simp [hv] at h
      | cons g gs =>
        simp only [hv, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact ⟨[], rfl⟩
    | none =>
      simp only [hc] at h
      cases hl : c.ch.left with
      | nil => simp [hl] at h
      | cons r t =>
        simp only [hl] at h
        cases hv : r.vals with
        | nil => simp [hv] at h
        | cons g gs =>
          simp only [hv, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact ⟨[r], rfl⟩
/-- An item is taken off the first round that is not yet closed: what that round has drawn stays. -/
instance keeps_item (i : Fmt.Item) (d : Fmt.ItemValue) : Keeps (Blk.item i d) :=
  ⟨fun c x c' h => ⟨(item_flags i d c x c' h).1, (item_flags i d c x c' h).2, fun hd => by
    obtain ⟨r, rest, vs, e1, _, e3, e4⟩ :=
      Blk.item_inv i d x c c' hd ((Blk.yields_iff _ _ _ _).2 h)
    exact ⟨0, e4.entries, by rw [e3, e1]; rfl⟩, item_left i d c x c' h⟩⟩
instance keeps_recvRoot : Keeps Blk.recvRoot := by keeps_prim Blk.recvRoot
theorem close_flags (n : String) (k : Fmt.Kind) (nz : Nat) : ∀ c x c',
    Blk.close n k nz c = .ok (x, c') →
      c'.ch.dry = c.ch.dry ∧ (c'.failed = none → c.failed = none) := by keeps_flags Blk.close
theorem close_left (n : String) (k : Fmt.Kind) (nz : Nat) : ∀ c x c',
    Blk.close n k nz c = .ok (x, c') → c'.ch.left <:+ c.ch.left := by
  intro c x c' h
  unfold Blk.close at h
  cases he : c.ch.entries with
  | nil => simp [he] at h
  | cons e es =>
    simp only [he] at h
    split at h
    · cases h
    · split at h
      · cases h
        exact ⟨[], rfl⟩
      · cases hc : c.ch.cur with
        | some r =>
          simp only [hc] at h
          split at h
          · cases h
            exact ⟨[], rfl⟩
          · cases h
        | none =>
          simp only [hc] at h
          cases hl : c.ch.left with
          | nil => simp [hl] at h
          | cons r t =>
            simp only [hl] at h
            split at h
            · cases h
              exact ⟨[r], rfl⟩
            · cases h
/-- The first unused entry and the first round that is not yet closed go together. -/
instance keeps_close (n : String) (k : Fmt.Kind) (nz : Nat) : Keeps (Blk.close n k nz) :=
  ⟨fun c x c' h => ⟨(close_flags n k nz c x c' h).1, (close_flags n k nz c x c' h).2, fun hd => by
    obtain ⟨e, es, r, rest, a1, _, _, a4, _, _, _, _, _, a10, a11, _⟩ :=
      Blk.close_inv n k nz x c c' hd ((Blk.yields_iff _ _ _ _).2 h)
    exact ⟨1, by rw [a11, a1]; rfl, by rw [a10, a4]; rfl⟩, close_left n k nz c x c' h⟩⟩
instance keeps_requireRows (r : Nat) : Keeps (Blk.requireRows r) := by keeps_prim Blk.requireRows
instance keeps_handOver : Keeps Blk.handOver := by keeps_prim Blk.handOver
instance keeps_onOracle (o : Nat) (f : Oracle → Oracle) :
    Keeps (Blk.onOracle o f) := by
  keeps_prim Blk.onOracle
instance keeps_onGroup (g : Nat) (f : Group → Group) :
    Keeps (Blk.onGroup g f) := by
  keeps_prim Blk.onGroup
instance keeps_theBook : Keeps Blk.theBook := by keeps_prim Blk.theBook
instance keeps_setBook (B : TreeBook) : Keeps (Blk.setBook B) := by keeps_prim Blk.setBook
instance keeps_takeColumns (t : Tree) (xs : Array Nat) : Keeps (Blk.takeColumns t xs) := by
  keeps_prim Blk.takeColumns
instance keeps_readStored (t : Fmt.Stored) (p : Positions) : Keeps (Blk.readStored t p) := by
  keeps_prim Blk.readStored

instance keeps_named {α : Type} (n : String) (b : Blk α) [hb : Keeps b] : Keeps (Blk.named n b) :=
  ⟨fun c x c' h => by
    unfold Blk.named at h
    split at h
    · cases h
    · cases h; exact hb.out _ _ _ (by assumption)⟩

instance keeps_inPlace {α : Type} (n : String) (b : Blk α) [hb : Keeps b] :
    Keeps (Blk.inPlace n b) :=
  ⟨fun c x c' h => by
    unfold Blk.inPlace at h
    split at h
    · cases h
    · cases h; exact hb.out _ _ _ (by assumption)⟩

/-! ## The calls of Ground.lean that are written over these -/

instance keeps_recvE : Keeps Blk.recvE := by unfold Blk.recvE; keeps
instance keeps_recvAnswer : Keeps Blk.recvAnswer := by unfold Blk.recvAnswer; keeps
instance keeps_recvEsInto (n : Nat) (acc : Array E) : Keeps (Blk.recvEsInto n acc) := by
  induction n generalizing acc with
  | zero => unfold Blk.recvEsInto; keeps
  | succ n ih => unfold Blk.recvEsInto; keeps
instance keeps_recvEs (n : Nat) : Keeps (Blk.recvEs n) := by unfold Blk.recvEs; keeps
instance keeps_closeEmpty (n : String) : Keeps (Blk.closeEmpty n) := by unfold Blk.closeEmpty; keeps
instance keeps_closeElems (n : String) (nz : Nat) :
    Keeps (Blk.closeElems n nz) := by
  unfold Blk.closeElems; keeps
instance keeps_closeOne (n : String) (k : Fmt.Kind) (nz : Nat) : Keeps (Blk.closeOne n k nz) := by
  unfold Blk.closeOne; keeps
instance keeps_closePositions (n : String) (l : Nat) : Keeps (Blk.closePositions n l) := by
  unfold Blk.closePositions; keeps
instance keeps_oracle (o : Nat) : Keeps (Blk.oracle o) := by unfold Blk.oracle; keeps
instance keeps_group (g : Nat) : Keeps (Blk.group g) := by unfold Blk.group; keeps
instance keeps_newGroup (c m : Nat) : Keeps (Blk.newGroup c m) := by unfold Blk.newGroup; keeps
instance keeps_spendAsMask (o : Nat) : Keeps (Blk.spendAsMask o) := by unfold Blk.spendAsMask; keeps
instance keeps_join (g o : Nat) (k : Bool) : Keeps (Blk.join g o k) := by unfold Blk.join; keeps
instance keeps_takeMask (o : Nat) : Keeps (Blk.takeMask o) := by unfold Blk.takeMask; keeps
instance keeps_takeMasksInto (o n : Nat) (acc : Array Nat) : Keeps (Blk.takeMasksInto o n acc) := by
  induction n generalizing acc with
  | zero => unfold Blk.takeMasksInto; keeps
  | succ n ih => unfold Blk.takeMasksInto; keeps
instance keeps_takeMasks (o n : Nat) : Keeps (Blk.takeMasks o n) := by unfold Blk.takeMasks; keeps
instance keeps_closeLedger (o : Nat) : Keeps (Blk.closeLedger o) := by unfold Blk.closeLedger; keeps
instance keeps_addRow (g : Nat) (r : Row) : Keeps (Blk.addRow g r) := by unfold Blk.addRow; keeps
instance keeps_addRowsOnView (g : Nat) (r : Unit → Option (List Row)) :
    Keeps (Blk.addRowsOnView g r) := by
  unfold Blk.addRowsOnView; keeps
instance keeps_layout (g : Nat) : Keeps (Blk.layout g) := by unfold Blk.layout; keeps
instance keeps_beginRun (g : Nat) : Keeps (Blk.beginRun g) := by unfold Blk.beginRun; keeps
instance keeps_requireSampled (r : Row) :
    Keeps (Blk.requireSampled r) := by
  unfold Blk.requireSampled; keeps
instance keeps_requireAllTested : Keeps Blk.requireAllTested := by
  unfold Blk.requireAllTested; keeps
instance keeps_receiveOracles (s : Array OracleNotice) : Keeps (Blk.receiveOracles s) := by
  unfold Blk.receiveOracles; keeps
instance keeps_countOpening (t : Nat) :
    Keeps (Blk.countOpening t) := by
  unfold Blk.countOpening; keeps
instance keeps_openTreesInto (B : TreeBook) (p : Positions) (ts : List Nat)
    (acc : Array (Nat × Array Nat × Array (Array F))) : Keeps (Blk.openTreesInto B p ts acc) := by
  induction ts generalizing acc with
  | nil => unfold Blk.openTreesInto; keeps
  | cons t ts ih => unfold Blk.openTreesInto; keeps
instance keeps_openTrees (B : TreeBook) (p : Positions) (ts : List Nat) :
    Keeps (Blk.openTrees B p ts) := by
  unfold Blk.openTrees; keeps
instance keeps_readOpened (ids : Array Nat) (p : Positions) : Keeps (Blk.readOpened ids p) := by
  unfold Blk.readOpened; keeps
instance keeps_sampledElsewhere (m : Nat) (o : Statement) (t : Nat) :
    Keeps (Blk.sampledElsewhere m o t) := by
  unfold Blk.sampledElsewhere; keeps
instance keeps_adoptOracles (s : Array OracleNotice) (g : Array (Nat × Fmt.Src)) :
    Keeps (Blk.adoptOracles s g) := by
  unfold Blk.adoptOracles; keeps

#print axioms Kept.refl
#print axioms Kept.trans
#print axioms Keeps.viewB
#print axioms Keeps.mark
#print axioms Kept.same
#print axioms keeps_iff
#print axioms keeps_pure
#print axioms Keeps.bind
#print axioms keeps_bind
#print axioms keeps_map
#print axioms keeps_ite
#print axioms keeps_dite
#print axioms keeps_forIn_list
#print axioms keeps_forIn_array
#print axioms keeps_foldlM_list
#print axioms keeps_foldlM_array
#print axioms keeps_forM_list
#print axioms keeps_forM_array
#print axioms keeps_fail
#print axioms keeps_must
#print axioms keeps_test
#print axioms keeps_check
#print axioms keeps_onView
#print axioms keeps_getOnView
#print axioms keeps_testOnView
#print axioms keeps_checkOnView
#print axioms keeps_get
#print axioms keeps_isDry
#print axioms keeps_samples
#print axioms keeps_firstTree
#print axioms keeps_lastEntry
#print axioms keeps_note
#print axioms keeps_noteBy
#print axioms keeps_statement
#print axioms keeps_setStatement
#print axioms keeps_item
#print axioms keeps_recvRoot
#print axioms keeps_close
#print axioms keeps_requireRows
#print axioms keeps_handOver
#print axioms keeps_onOracle
#print axioms keeps_onGroup
#print axioms keeps_theBook
#print axioms keeps_setBook
#print axioms keeps_takeColumns
#print axioms keeps_readStored
#print axioms keeps_named
#print axioms keeps_inPlace
#print axioms keeps_recvE
#print axioms keeps_recvAnswer
#print axioms keeps_recvEsInto
#print axioms keeps_recvEs
#print axioms keeps_closeEmpty
#print axioms keeps_closeElems
#print axioms keeps_closeOne
#print axioms keeps_closePositions
#print axioms keeps_oracle
#print axioms keeps_group
#print axioms keeps_newGroup
#print axioms keeps_spendAsMask
#print axioms keeps_join
#print axioms keeps_takeMask
#print axioms keeps_takeMasksInto
#print axioms keeps_takeMasks
#print axioms keeps_closeLedger
#print axioms keeps_addRow
#print axioms keeps_addRowsOnView
#print axioms keeps_layout
#print axioms keeps_beginRun
#print axioms keeps_requireSampled
#print axioms keeps_requireAllTested
#print axioms keeps_receiveOracles
#print axioms keeps_countOpening
#print axioms keeps_openTreesInto
#print axioms keeps_openTrees
#print axioms keeps_readOpened
#print axioms keeps_sampledElsewhere
#print axioms keeps_adoptOracles

end OnBytes.L5
