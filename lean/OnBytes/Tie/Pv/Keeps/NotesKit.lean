-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/NotesKit.lean: a property of every round that a dry run has noted, carried
along the verifier's routines: two such properties: "not of the kind sealed" and "its list of stored
tables is empty" (the field stored of a noted round).

Definitions, statements and proofs. A dry run (OnBytes/Iop/Ground.lean) lists a chain's rounds: each
closing notes a round with its kind; two calls add to the round that was noted last. The rules and
tactics of OnBytes/Tie/Pv/Keeps/KeepsLift.lean and the commands of
OnBytes/Tie/Pv/Keeps/KeepsWalk.lean are stated for any property of a monad's routines that pure has
and bind carries (the class HasKeeps). Inside each of the two namespaces Unsealed and Unstored of
this file the blocks get such a property of their own. So KeepsM x reads there, and there alone: in
a dry run, if every noted round is P before x, so is every noted round behind it. A file that wants
another reading of KeepsM opens neither namespace: it takes the statements in plain words
(`NotesB`).
Main names (namespace OnBytes.Tie.Pv.Keeps.Notes):
  `All P c`: every round that is noted in c is P.
  `NotesB P b`: wherever the block b succeeds from a context in a dry run in which `All P` holds, it
    leaves a context in a dry run in which `All P` holds.
  `nb_fail` and those that follow: the calls of Ground.lean that are written as functions of the
    context, for every P; `nb_close`, `nb_takeColumns`, `nb_readStored`: under a premise on P.
  `dryRun_all`: the rounds that a dry run returns come from noted rounds that are P.
  `Unsealed.P`, `Unsealed.hasK`, `Unsealed.NotSealed k`: the first property, its class, and the
    class of the six kinds that are not "sealed", under which a closing has the property.
  `Unstored.P`, `Unstored.hasK`: the second. Blk.readStored does not have it.
Tactics of this file.
  notes_prim d: proves `NotesB P` of a call d that is written as a function of the context and does
    not write the noted rounds: it unfolds d, goes through its cases, and closes each case.
Limits: one direction: from a success. Nothing on a run on a view.
-/
import OnBytes.Tie.Pv.Keeps.KeepsWalk
import OnBytes.Model.Trees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Keeps.Notes

open OnBytes OnBytes.Model OnBytes.L5

/-- Every noted round is P. -/
def All (P : RoundNote → Prop) (c : Ctx) : Prop := ∀ n ∈ c.ch.noted.toList, P n

/-- In a dry run the block carries "every noted round is P". -/
def NotesB (P : RoundNote → Prop) {α : Type} (b : Blk α) : Prop :=
  ∀ c x c', b c = .ok (x, c') → c.ch.dry = true → All P c → c'.ch.dry = true ∧ All P c'

variable (P : RoundNote → Prop)

theorem NotesB.pure {α : Type} (a : α) : NotesB P (Pure.pure a : Blk α) :=
  fun c x c' h hd hP => by cases h; exact ⟨hd, hP⟩

theorem NotesB.bind {α β : Type} (b : Blk α) (f : α → Blk β) (hb : NotesB P b)
    (hf : ∀ a, NotesB P (f a)) : NotesB P (b >>= f) := fun c y c2 h hd hP => by
  obtain ⟨x, c1, h1, h2⟩ := (Blk.yields_bind b f c c2 y).1 ((Blk.yields_iff _ _ _ _).2 h)
  obtain ⟨d1, p1⟩ := hb _ _ _ ((Blk.yields_iff _ _ _ _).1 h1) hd hP
  exact hf x _ _ _ ((Blk.yields_iff _ _ _ _).1 h2) d1 p1

/-- For a call that is written as a function of the context and does not write the noted rounds. -/
macro "notes_prim " d:ident : tactic =>
  `(tactic| (
      intro c x c' h hd hP
      unfold $d at h
      try dsimp only at h
      repeat' (split at h)
      all_goals first
        | (cases h; done)
        | (cases h; exact ⟨hd, hP⟩)))

/-! ## The calls of Ground.lean that are functions of the context -/

theorem nb_fail {α : Type} (n : String) : NotesB P (Blk.fail n : Blk α) := by notes_prim Blk.fail
theorem nb_must (b : Bool) (n : String) : NotesB P (Blk.must b n) := by notes_prim Blk.must
theorem nb_test (b : Bool) (n : String) : NotesB P (Blk.test b n) := by notes_prim Blk.test
theorem nb_check (n : String) (b : Bool) : NotesB P (Blk.check n b) := by notes_prim Blk.check
theorem nb_onView {α : Type} (d : α) (f : Unit → α) :
    NotesB P (Blk.onView d f) := by notes_prim Blk.onView
theorem nb_getOnView {α : Type} (d : α) (f : Unit → Option α) (n : String) :
    NotesB P (Blk.getOnView d f n) := by notes_prim Blk.getOnView
theorem nb_testOnView (f : Unit → Bool) (n : String) :
    NotesB P (Blk.testOnView f n) := by notes_prim Blk.testOnView
theorem nb_checkOnView (n : String) (f : Unit → Bool) :
    NotesB P (Blk.checkOnView n f) := by notes_prim Blk.checkOnView
theorem nb_get {α : Type} (x : Option α) (n : String) :
    NotesB P (Blk.get x n) := by notes_prim Blk.get
theorem nb_isDry : NotesB P Blk.isDry := by notes_prim Blk.isDry
theorem nb_samples : NotesB P Blk.samples := by notes_prim Blk.samples
theorem nb_firstTree : NotesB P Blk.firstTree := by notes_prim Blk.firstTree
theorem nb_lastEntry : NotesB P Blk.lastEntry := by notes_prim Blk.lastEntry
theorem nb_note (w : String) (v : E) : NotesB P (Blk.note w v) := by notes_prim Blk.note
theorem nb_noteBy (w : String) (v : Unit → E) :
    NotesB P (Blk.noteBy w v) := by notes_prim Blk.noteBy
theorem nb_statement : NotesB P Blk.statement := by notes_prim Blk.statement
theorem nb_setStatement (S : Statement) :
    NotesB P (Blk.setStatement S) := by notes_prim Blk.setStatement
theorem nb_recvRoot : NotesB P Blk.recvRoot := by notes_prim Blk.recvRoot
theorem nb_requireRows (r : Nat) : NotesB P (Blk.requireRows r) := by notes_prim Blk.requireRows
theorem nb_handOver : NotesB P Blk.handOver := by notes_prim Blk.handOver
theorem nb_onOracle (o : Nat) (f : Oracle → Oracle) :
    NotesB P (Blk.onOracle o f) := by notes_prim Blk.onOracle
theorem nb_onGroup (g : Nat) (f : Group → Group) :
    NotesB P (Blk.onGroup g f) := by notes_prim Blk.onGroup
theorem nb_theBook : NotesB P Blk.theBook := by notes_prim Blk.theBook
theorem nb_setBook (B : TreeBook) : NotesB P (Blk.setBook B) := by notes_prim Blk.setBook

theorem nb_item (i : Fmt.Item) (d : Fmt.ItemValue) : NotesB P (Blk.item i d) :=
  fun c x c' h hd hP => by
    unfold Blk.item at h
    simp only [hd, if_true] at h
    cases h
    exact ⟨rfl, hP⟩

/-- A closing notes one round more. -/
theorem nb_close (n : String) (k : Fmt.Kind) (nz : Nat)
    (hk : ∀ e items, P { entry := e, kind := k, items := items }) : NotesB P (Blk.close n k nz) :=
  fun c x c' h hd hP => by
    unfold Blk.close at h
    cases he : c.ch.entries with
    | nil => simp [he] at h
    | cons e es =>
      simp only [he] at h
      split at h
      · cases h
      · simp only [hd] at h
        cases h
        refine ⟨rfl, fun m hm => ?_⟩
        have hm' : m ∈ (c.ch.noted.push
            { entry := e, kind := k, items := c.ch.items.reverse }).toList := hm
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm'
        rcases hm' with h1 | rfl
        · exact hP m h1
        · exact hk _ _

theorem all_modify {f : RoundNote → RoundNote} (hf : ∀ n, P n → P (f n)) (a : Array RoundNote)
    (i : Nat) (h : ∀ n ∈ a.toList, P n) : ∀ n ∈ (a.modify i f).toList, P n := by
  intro n hn
  rw [Array.toList_modify] at hn
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hn
  rw [List.getElem_modify]
  have hj' : j < a.toList.length := by simpa using hj
  split
  · exact hf _ (h _ (List.getElem_mem hj'))
  · exact h _ (List.getElem_mem hj')

theorem nb_takeColumns (t : Tree) (xs : Array Nat)
    (hf : ∀ n o, P n → P { n with opens := o }) : NotesB P (Blk.takeColumns t xs) :=
  fun c x c' h hd hP => by
    unfold Blk.takeColumns at h
    simp only [hd, if_true] at h
    split at h
    · cases h
    · cases h
      exact ⟨rfl, all_modify P (fun n hn => hf n _ hn) _ _ hP⟩

theorem nb_readStored (t : Fmt.Stored) (p : Positions)
    (hf : ∀ n s, P n → P { n with stored := s }) : NotesB P (Blk.readStored t p) :=
  fun c x c' h hd hP => by
    unfold Blk.readStored at h
    simp only [hd, if_true] at h
    split at h
    · cases h
    · cases h
      exact ⟨rfl, all_modify P (fun n hn => hf n _ hn) _ _ hP⟩

theorem nb_named {α : Type} (n : String) (b : Blk α) (hb : NotesB P b) :
    NotesB P (Blk.named n b) := fun c x c' h hd hP => by
  unfold Blk.named at h
  split at h
  · cases h
  · cases h; exact hb _ _ _ (by assumption) hd hP

theorem nb_inPlace {α : Type} (n : String) (b : Blk α) (hb : NotesB P b) :
    NotesB P (Blk.inPlace n b) := fun c x c' h hd hP => by
  unfold Blk.inPlace at h
  split at h
  · cases h
  · cases h; exact hb _ _ _ (by assumption) hd hP

theorem nb_except {α : Type} {n : Type → Type} [MonadLiftT n (Except Failure)] (x : n α) :
    NotesB P (monadLift x : Blk α) := fun c y c' h hd hP => by
  have h' : ((monadLift x : Except Failure α) >>= fun a => Pure.pure (a, c)) = .ok (y, c') := h
  cases e : (monadLift x : Except Failure α) with
  | error f => rw [e] at h'; cases h'
  | ok a => rw [e] at h'; cases h'; exact ⟨hd, hP⟩

theorem nb_getThe : NotesB P (getThe Ctx : Blk Ctx) :=
  fun c x c' h hd hP => by cases h; exact ⟨hd, hP⟩

theorem nb_change (f : Fork → Option Fork) (F : Fork) : NotesB P (SubM.change f F) :=
  fun c y c' h hd hP => by
    unfold SubM.change at h
    cases e : f F with
    | none => rw [e] at h; cases h
    | some a => rw [e] at h; cases h; exact ⟨hd, hP⟩

theorem nb_take {α : Type} (f : Fork → Option (α × Fork)) (F : Fork) :
    NotesB P (SubM.take f F) := fun c y c' h hd hP => by
  unfold SubM.take at h
  cases e : f F with
  | none => rw [e] at h; cases h
  | some a => rw [e] at h; cases h; exact ⟨hd, hP⟩

theorem nb_ask {α : Type} (f : Fork → Option α) (F : Fork) : NotesB P (SubM.ask f F) :=
  fun c y c' h hd hP => by
    unfold SubM.ask at h
    cases e : f F with
    | none => rw [e] at h; cases h
    | some a => rw [e] at h; cases h; exact ⟨hd, hP⟩

/-- The context from which a dry run starts, and the context at its end. -/
theorem dryRun_ctx {α : Type} {b : Blk α} {s : Start} {rs : List (Fmt.Round × List Fmt.Stored)}
    {a : α} (h : b.dryRun s = some (rs, a)) :
    ∃ c0 c, b c0 = .ok (a, c) ∧ c0.ch.dry = true ∧ c0.ch.noted = #[] ∧
      rs = c.ch.noted.toList.map fun n => (⟨n.entry, n.kind, n.items, n.opens⟩, n.stored) := by
  unfold Blk.dryRun Blk.dryRunNamed at h
  split at h
  · cases h
  · rename_i a' c hr
    split at h
    · have e : (c.ch.noted.toList.map fun n =>
          ((⟨n.entry, n.kind, n.items, n.opens⟩ : Fmt.Round), n.stored), a') = (rs, a) :=
        Option.some.inj h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      unfold Blk.runNamed at hr
      split at hr
      · exact ⟨_, c, hr, rfl, rfl, rfl⟩
      · cases hr
    · cases h

/-- The rounds that a dry run returns come from noted rounds that are P. -/
theorem dryRun_all {α : Type} {b : Blk α} (k : NotesB P b) {s : Start}
    {rs : List (Fmt.Round × List Fmt.Stored)} {a : α} (h : b.dryRun s = some (rs, a)) :
    ∀ r ∈ rs, ∃ n, P n ∧ r = (⟨n.entry, n.kind, n.items, n.opens⟩, n.stored) := by
  obtain ⟨c0, c, hr, hd, hn, rfl⟩ := dryRun_ctx h
  have hA := (k c0 a c hr hd (fun n hm => by rw [hn] at hm; cases hm)).2
  intro r hr'
  obtain ⟨n, hn', rfl⟩ := List.mem_map.1 hr'
  exact ⟨n, hA n hn', rfl⟩

end OnBytes.Tie.Pv.Keeps.Notes

/-! ## Not of the kind "sealed" -/

namespace OnBytes.Tie.Pv.Keeps.Notes.Unsealed

open OnBytes OnBytes.Model OnBytes.L5

/-- The noted round is not of the kind "sealed". -/
def P (n : RoundNote) : Prop := n.kind ≠ .sealed

/-- For a block, inside this namespace. -/
scoped instance (priority := high) hasK : HasKeeps Blk where
  K := fun b => NotesB P b
  K_pure := fun a => NotesB.pure P a
  K_bind := fun b f hb hf => NotesB.bind P b f hb hf

/-- A kind other than "sealed". -/
class NotSealed (k : Fmt.Kind) : Prop where
  out : k ≠ .sealed

instance : NotSealed .elems := ⟨by decide⟩
instance : NotSealed .join := ⟨by decide⟩
instance : NotSealed .seeds := ⟨by decide⟩
instance : NotSealed .positions := ⟨by decide⟩
instance : NotSealed .entries := ⟨by decide⟩
instance : NotSealed .nothing := ⟨by decide⟩

instance (c : Prop) [Decidable c] (a b : Fmt.Kind) [ha : NotSealed a] [hb : NotSealed b] :
    NotSealed (if c then a else b) := ⟨by split; exact ha.out; exact hb.out⟩

instance u_fail {α : Type} (n : String) : KeepsM (Blk.fail n : Blk α) := ⟨nb_fail P n⟩
instance u_must (b : Bool) (n : String) : KeepsM (Blk.must b n) := ⟨nb_must P b n⟩
instance u_test (b : Bool) (n : String) : KeepsM (Blk.test b n) := ⟨nb_test P b n⟩
instance u_check (n : String) (b : Bool) : KeepsM (Blk.check n b) := ⟨nb_check P n b⟩
instance u_onView {α : Type} (d : α) (f : Unit → α) : KeepsM (Blk.onView d f) := ⟨nb_onView P d f⟩
instance u_getOnView {α : Type} (d : α) (f : Unit → Option α) (n : String) :
    KeepsM (Blk.getOnView d f n) := ⟨nb_getOnView P d f n⟩
instance u_testOnView (f : Unit → Bool) (n : String) :
    KeepsM (Blk.testOnView f n) := ⟨nb_testOnView P f n⟩
instance u_checkOnView (n : String) (f : Unit → Bool) :
    KeepsM (Blk.checkOnView n f) := ⟨nb_checkOnView P n f⟩
instance u_get {α : Type} (x : Option α) (n : String) : KeepsM (Blk.get x n) := ⟨nb_get P x n⟩
instance u_isDry : KeepsM Blk.isDry := ⟨nb_isDry P⟩
instance u_samples : KeepsM Blk.samples := ⟨nb_samples P⟩
instance u_firstTree : KeepsM Blk.firstTree := ⟨nb_firstTree P⟩
instance u_lastEntry : KeepsM Blk.lastEntry := ⟨nb_lastEntry P⟩
instance u_note (w : String) (v : E) : KeepsM (Blk.note w v) := ⟨nb_note P w v⟩
instance u_noteBy (w : String) (v : Unit → E) : KeepsM (Blk.noteBy w v) := ⟨nb_noteBy P w v⟩
instance u_statement : KeepsM Blk.statement := ⟨nb_statement P⟩
instance u_setStatement (S : Statement) : KeepsM (Blk.setStatement S) := ⟨nb_setStatement P S⟩
instance u_recvRoot : KeepsM Blk.recvRoot := ⟨nb_recvRoot P⟩
instance u_requireRows (r : Nat) : KeepsM (Blk.requireRows r) := ⟨nb_requireRows P r⟩
instance u_handOver : KeepsM Blk.handOver := ⟨nb_handOver P⟩
instance u_onOracle (o : Nat) (f : Oracle → Oracle) :
    KeepsM (Blk.onOracle o f) := ⟨nb_onOracle P o f⟩
instance u_onGroup (g : Nat) (f : Group → Group) : KeepsM (Blk.onGroup g f) := ⟨nb_onGroup P g f⟩
instance u_theBook : KeepsM Blk.theBook := ⟨nb_theBook P⟩
instance u_setBook (B : TreeBook) : KeepsM (Blk.setBook B) := ⟨nb_setBook P B⟩

instance u_item (i : Fmt.Item) (d : Fmt.ItemValue) : KeepsM (Blk.item i d) := ⟨nb_item P i d⟩

instance u_named {α : Type} (n : String) (b : Blk α) [hb : KeepsM b] :
    KeepsM (Blk.named n b) := ⟨nb_named P n b hb.out⟩

instance u_inPlace {α : Type} (n : String) (b : Blk α) [hb : KeepsM b] :
    KeepsM (Blk.inPlace n b) := ⟨nb_inPlace P n b hb.out⟩

instance u_except {α : Type} {n : Type → Type} [MonadLiftT n (Except Failure)] (x : n α) :
    KeepsM (monadLift x : Blk α) := ⟨nb_except P x⟩

instance u_getThe : KeepsM (getThe Ctx : Blk Ctx) := ⟨nb_getThe P⟩

instance u_change (f : Fork → Option Fork) : KeepsM (SubM.change f) :=
  ⟨fun F => nb_change P f F⟩

instance u_take {α : Type} (f : Fork → Option (α × Fork)) : KeepsM (SubM.take f) :=
  ⟨fun F => nb_take P f F⟩

instance u_ask {α : Type} (f : Fork → Option α) : KeepsM (SubM.ask f) :=
  ⟨fun F => nb_ask P f F⟩

instance u_close (n : String) (k : Fmt.Kind) [hk : NotSealed k] (nz : Nat) :
    KeepsM (Blk.close n k nz) := ⟨nb_close P n k nz fun _ _ => hk.out⟩

instance u_takeColumns (t : Tree) (xs : Array Nat) : KeepsM (Blk.takeColumns t xs) :=
  ⟨nb_takeColumns P t xs fun _ _ h => h⟩

instance u_readStored (t : Fmt.Stored) (p : Positions) : KeepsM (Blk.readStored t p) :=
  ⟨nb_readStored P t p fun _ _ h => h⟩

instance u_closeOne (n : String) (k : Fmt.Kind) [NotSealed k] (nz : Nat) :
    KeepsM (Blk.closeOne n k nz) := by
  unfold Blk.closeOne; keepsM

end OnBytes.Tie.Pv.Keeps.Notes.Unsealed

/-! ## The list of stored tables is empty -/

namespace OnBytes.Tie.Pv.Keeps.Notes.Unstored

open OnBytes OnBytes.Model OnBytes.L5

/-- The noted round's list of stored tables is empty. This is not the mark "stored" of an opening's
shape, of which nothing is said. -/
def P (n : RoundNote) : Prop := n.stored = []

/-- For a block, inside this namespace. -/
scoped instance (priority := high) hasK : HasKeeps Blk where
  K := fun b => NotesB P b
  K_pure := fun a => NotesB.pure P a
  K_bind := fun b f hb hf => NotesB.bind P b f hb hf

instance s_fail {α : Type} (n : String) : KeepsM (Blk.fail n : Blk α) := ⟨nb_fail P n⟩
instance s_must (b : Bool) (n : String) : KeepsM (Blk.must b n) := ⟨nb_must P b n⟩
instance s_test (b : Bool) (n : String) : KeepsM (Blk.test b n) := ⟨nb_test P b n⟩
instance s_check (n : String) (b : Bool) : KeepsM (Blk.check n b) := ⟨nb_check P n b⟩
instance s_onView {α : Type} (d : α) (f : Unit → α) : KeepsM (Blk.onView d f) := ⟨nb_onView P d f⟩
instance s_getOnView {α : Type} (d : α) (f : Unit → Option α) (n : String) :
    KeepsM (Blk.getOnView d f n) := ⟨nb_getOnView P d f n⟩
instance s_testOnView (f : Unit → Bool) (n : String) :
    KeepsM (Blk.testOnView f n) := ⟨nb_testOnView P f n⟩
instance s_checkOnView (n : String) (f : Unit → Bool) :
    KeepsM (Blk.checkOnView n f) := ⟨nb_checkOnView P n f⟩
instance s_get {α : Type} (x : Option α) (n : String) : KeepsM (Blk.get x n) := ⟨nb_get P x n⟩
instance s_isDry : KeepsM Blk.isDry := ⟨nb_isDry P⟩
instance s_samples : KeepsM Blk.samples := ⟨nb_samples P⟩
instance s_firstTree : KeepsM Blk.firstTree := ⟨nb_firstTree P⟩
instance s_lastEntry : KeepsM Blk.lastEntry := ⟨nb_lastEntry P⟩
instance s_note (w : String) (v : E) : KeepsM (Blk.note w v) := ⟨nb_note P w v⟩
instance s_noteBy (w : String) (v : Unit → E) : KeepsM (Blk.noteBy w v) := ⟨nb_noteBy P w v⟩
instance s_statement : KeepsM Blk.statement := ⟨nb_statement P⟩
instance s_setStatement (S : Statement) : KeepsM (Blk.setStatement S) := ⟨nb_setStatement P S⟩
instance s_recvRoot : KeepsM Blk.recvRoot := ⟨nb_recvRoot P⟩
instance s_requireRows (r : Nat) : KeepsM (Blk.requireRows r) := ⟨nb_requireRows P r⟩
instance s_handOver : KeepsM Blk.handOver := ⟨nb_handOver P⟩
instance s_onOracle (o : Nat) (f : Oracle → Oracle) :
    KeepsM (Blk.onOracle o f) := ⟨nb_onOracle P o f⟩
instance s_onGroup (g : Nat) (f : Group → Group) : KeepsM (Blk.onGroup g f) := ⟨nb_onGroup P g f⟩
instance s_theBook : KeepsM Blk.theBook := ⟨nb_theBook P⟩
instance s_setBook (B : TreeBook) : KeepsM (Blk.setBook B) := ⟨nb_setBook P B⟩

instance s_item (i : Fmt.Item) (d : Fmt.ItemValue) : KeepsM (Blk.item i d) := ⟨nb_item P i d⟩

instance s_named {α : Type} (n : String) (b : Blk α) [hb : KeepsM b] :
    KeepsM (Blk.named n b) := ⟨nb_named P n b hb.out⟩

instance s_inPlace {α : Type} (n : String) (b : Blk α) [hb : KeepsM b] :
    KeepsM (Blk.inPlace n b) := ⟨nb_inPlace P n b hb.out⟩

instance s_except {α : Type} {n : Type → Type} [MonadLiftT n (Except Failure)] (x : n α) :
    KeepsM (monadLift x : Blk α) := ⟨nb_except P x⟩

instance s_getThe : KeepsM (getThe Ctx : Blk Ctx) := ⟨nb_getThe P⟩

instance s_change (f : Fork → Option Fork) : KeepsM (SubM.change f) :=
  ⟨fun F => nb_change P f F⟩

instance s_take {α : Type} (f : Fork → Option (α × Fork)) : KeepsM (SubM.take f) :=
  ⟨fun F => nb_take P f F⟩

instance s_ask {α : Type} (f : Fork → Option α) : KeepsM (SubM.ask f) :=
  ⟨fun F => nb_ask P f F⟩

instance s_close (n : String) (k : Fmt.Kind) (nz : Nat) : KeepsM (Blk.close n k nz) :=
  ⟨nb_close P n k nz fun _ _ => rfl⟩

instance s_takeColumns (t : Tree) (xs : Array Nat) : KeepsM (Blk.takeColumns t xs) :=
  ⟨nb_takeColumns P t xs fun _ _ h => h⟩

end OnBytes.Tie.Pv.Keeps.Notes.Unstored

#print axioms OnBytes.Tie.Pv.Keeps.Notes.nb_close
#print axioms OnBytes.Tie.Pv.Keeps.Notes.nb_readStored
#print axioms OnBytes.Tie.Pv.Keeps.Notes.dryRun_all
#print axioms OnBytes.Tie.Pv.Keeps.Notes.Unsealed.u_closeOne
