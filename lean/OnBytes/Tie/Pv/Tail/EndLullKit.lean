-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndLullKit.lean: the routines that close no round: wherever such a routine
succeeds, the plan's entries that are still to come are as they were.

Definitions, statements and proofs. The text is that of StillKit.lean,
with the property replaced, by a program: there «the round whose message is
being received and the rounds that are not yet begun are as they were», here «the entries are as
they were». As there, the rules and tactics of OnBytes/Tie/Pv/Keeps/KeepsLift.lean and the commands
of OnBytes/Tie/Pv/Keeps/KeepsWalk.lean are used at another property of a monad's routines than the
library's own (the class HasKeeps): inside the namespace of this file, and there alone, KeepsM x
reads: x closes no round. Of the calls of OnBytes/Iop/Ground.lean that are written as functions of
the context all have the property but one: Blk.close.

Main names:
  `Same c c'`: c' has the entries of c's channel.
  `LullB b`: wherever the block b succeeds, the context that it leaves is `Same`.
  `hasLull`: the class HasKeeps for blocks at `LullB`; it holds inside this namespace alone.
  `lull_fail` and those that follow: the calls of Ground.lean; `lull_item`: taking an item off a
    round.
  `same_blk`, `same_sub`, `same_link`: what KeepsM says here of a success of a block, of a routine
    of a sub-proof and of a routine of a link.
Tactics of this file. lull_prim d: proves KeepsM, in the reading of this namespace, of a call d
that is written as a function of the context.

Limits: one direction: from a success. In both readings of a block (a dry run and a run on a view).


-/
import OnBytes.Tie.Pv.Keeps.KeepsWalk
import OnBytes.Model.Trees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Lull

open OnBytes OnBytes.Model OnBytes.L5

/-- c' has the entries of c's channel. -/
structure Same (c c' : Ctx) : Prop where
  entries : c'.ch.entries = c.ch.entries

/-- A context has its own entries. -/
theorem Same.refl (c : Ctx) : Same c c := ⟨rfl⟩

/-- One stretch behind another. -/
theorem Same.trans {a b c : Ctx} (h1 : Same a b) (h2 : Same b c) : Same a c :=
  ⟨h2.entries.trans h1.entries⟩

/-- Wherever the block succeeds, it has closed no round. -/
def LullB {α : Type} (b : Blk α) : Prop := ∀ c x c', b c = .ok (x, c') → Same c c'

/-- For a block, inside this namespace: LullB. -/
scoped instance (priority := high) hasLull : HasKeeps Blk where
  K := fun b => LullB b
  K_pure := fun a c x c' h => by cases h; exact Same.refl _
  K_bind := fun b f hb hf c y c2 h => by
    obtain ⟨x, c1, h1, h2⟩ := (Blk.yields_bind b f c c2 y).1 ((Blk.yields_iff _ _ _ _).2 h)
    exact (hb _ _ _ ((Blk.yields_iff _ _ _ _).1 h1)).trans
      (hf x _ _ _ ((Blk.yields_iff _ _ _ _).1 h2))

/-- For a call that is written as a function of the context. -/
macro "lull_prim " d:ident : tactic =>
  `(tactic| (
      refine ⟨fun c x c' h => ?_⟩
      unfold $d at h
      try dsimp only at h
      repeat' (split at h)
      all_goals first
        | (cases h; done)
        | (cases h; exact ⟨rfl⟩)))

/-! ## The calls of Ground.lean that are functions of the context -/

instance lull_fail {α : Type} (n : String) : KeepsM (Blk.fail n : Blk α) := by lull_prim Blk.fail
/-- `Blk.must` closes no round. -/
instance lull_must (b : Bool) (n : String) : KeepsM (Blk.must b n) := by lull_prim Blk.must
/-- `Blk.test` closes no round. -/
instance lull_test (b : Bool) (n : String) : KeepsM (Blk.test b n) := by lull_prim Blk.test
/-- `Blk.check` closes no round. -/
instance lull_check (n : String) (b : Bool) : KeepsM (Blk.check n b) := by lull_prim Blk.check
/-- `Blk.onView` closes no round. -/
instance lull_onView {α : Type} (d : α) (f : Unit → α) : KeepsM (Blk.onView d f) := by
  lull_prim Blk.onView
/-- `Blk.getOnView` closes no round. -/
instance lull_getOnView {α : Type} (d : α) (f : Unit → Option α) (n : String) :
    KeepsM (Blk.getOnView d f n) := by
  lull_prim Blk.getOnView
/-- `Blk.testOnView` closes no round. -/
instance lull_testOnView (f : Unit → Bool) (n : String) : KeepsM (Blk.testOnView f n) := by
  lull_prim Blk.testOnView
/-- `Blk.checkOnView` closes no round. -/
instance lull_checkOnView (n : String) (f : Unit → Bool) : KeepsM (Blk.checkOnView n f) := by
  lull_prim Blk.checkOnView
/-- `Blk.get` closes no round. -/
instance lull_get {α : Type} (x : Option α) (n : String) : KeepsM (Blk.get x n) := by
  lull_prim Blk.get
/-- `Blk.isDry` closes no round. -/
instance lull_isDry : KeepsM Blk.isDry := by lull_prim Blk.isDry
/-- `Blk.samples` closes no round. -/
instance lull_samples : KeepsM Blk.samples := by lull_prim Blk.samples
/-- `Blk.firstTree` closes no round. -/
instance lull_firstTree : KeepsM Blk.firstTree := by lull_prim Blk.firstTree
/-- `Blk.lastEntry` closes no round. -/
instance lull_lastEntry : KeepsM Blk.lastEntry := by lull_prim Blk.lastEntry
/-- `Blk.note` closes no round. -/
instance lull_note (w : String) (v : E) : KeepsM (Blk.note w v) := by lull_prim Blk.note
/-- `Blk.noteBy` closes no round. -/
instance lull_noteBy (w : String) (v : Unit → E) : KeepsM (Blk.noteBy w v) := by
  lull_prim Blk.noteBy
/-- `Blk.statement` closes no round. -/
instance lull_statement : KeepsM Blk.statement := by lull_prim Blk.statement
/-- `Blk.setStatement` closes no round. -/
instance lull_setStatement (S : Statement) : KeepsM (Blk.setStatement S) := by
  lull_prim Blk.setStatement
/-- `Blk.recvRoot` closes no round. -/
instance lull_recvRoot : KeepsM Blk.recvRoot := by lull_prim Blk.recvRoot
/-- `Blk.requireRows` closes no round. -/
instance lull_requireRows (r : Nat) : KeepsM (Blk.requireRows r) := by lull_prim Blk.requireRows
/-- `Blk.handOver` closes no round. -/
instance lull_handOver : KeepsM Blk.handOver := by lull_prim Blk.handOver
/-- `Blk.onOracle` closes no round. -/
instance lull_onOracle (o : Nat) (f : Oracle → Oracle) : KeepsM (Blk.onOracle o f) := by
  lull_prim Blk.onOracle
/-- `Blk.onGroup` closes no round. -/
instance lull_onGroup (g : Nat) (f : Group → Group) : KeepsM (Blk.onGroup g f) := by
  lull_prim Blk.onGroup
/-- `Blk.theBook` closes no round. -/
instance lull_theBook : KeepsM Blk.theBook := by lull_prim Blk.theBook
/-- `Blk.setBook` closes no round. -/
instance lull_setBook (B : TreeBook) : KeepsM (Blk.setBook B) := by lull_prim Blk.setBook
/-- `Blk.takeColumns` closes no round. -/
instance lull_takeColumns (t : Tree) (xs : Array Nat) : KeepsM (Blk.takeColumns t xs) := by
  lull_prim Blk.takeColumns
/-- `Blk.readStored` closes no round. -/
instance lull_readStored (t : Fmt.Stored) (p : Positions) : KeepsM (Blk.readStored t p) := by
  lull_prim Blk.readStored

/-- `Blk.named` closes no round. -/
instance lull_named {α : Type} (n : String) (b : Blk α) [hb : KeepsM b] :
    KeepsM (Blk.named n b) :=
  ⟨fun c x c' h => by
    unfold Blk.named at h
    split at h
    · cases h
    · cases h; exact hb.out _ _ _ (by assumption)⟩

/-- `Blk.inPlace` closes no round. -/
instance lull_inPlace {α : Type} (n : String) (b : Blk α) [hb : KeepsM b] :
    KeepsM (Blk.inPlace n b) :=
  ⟨fun c x c' h => by
    unfold Blk.inPlace at h
    split at h
    · cases h
    · cases h; exact hb.out _ _ _ (by assumption)⟩

/-- What has no context, lifted into a block. -/
instance lull_except {α : Type} {n : Type → Type} [MonadLiftT n (Except Failure)] (x : n α) :
    KeepsM (monadLift x : Blk α) :=
  ⟨fun c y c' h => by
    have h' : ((monadLift x : Except Failure α) >>= fun a => pure (a, c)) = .ok (y, c') := h
    cases e : (monadLift x : Except Failure α) with
    | error f => rw [e] at h'; cases h'
    | ok a => rw [e] at h'; cases h'; exact Same.refl _⟩

/-- `getThe` closes no round. -/
instance lull_getThe : KeepsM (getThe Ctx : Blk Ctx) :=
  ⟨fun c x c' h => by cases h; exact Same.refl _⟩

/-! ## The three calls of OnBytes/Model/Hide.lean that are functions of both states -/

instance lull_change (f : Fork → Option Fork) : KeepsM (SubM.change f) :=
  ⟨fun F c y c' h => by
    unfold SubM.change at h
    cases e : f F with
    | none => rw [e] at h; cases h
    | some a => rw [e] at h; cases h; exact Same.refl _⟩

/-- `SubM.take` closes no round. -/
instance lull_take {α : Type} (f : Fork → Option (α × Fork)) : KeepsM (SubM.take f) :=
  ⟨fun F c y c' h => by
    unfold SubM.take at h
    cases e : f F with
    | none => rw [e] at h; cases h
    | some a => rw [e] at h; cases h; exact Same.refl _⟩

/-- `SubM.ask` closes no round. -/
instance lull_ask {α : Type} (f : Fork → Option α) : KeepsM (SubM.ask f) :=
  ⟨fun F c y c' h => by
    unfold SubM.ask at h
    cases e : f F with
    | none => rw [e] at h; cases h
    | some a => rw [e] at h; cases h; exact Same.refl _⟩

/-! ## Taking an item off a round -/

instance lull_item (i : Fmt.Item) (dflt : Fmt.ItemValue) : KeepsM (Blk.item i dflt) := by
  lull_prim Blk.item

/-! ## What KeepsM says here of a success -/

theorem same_blk {α : Type} {b : Blk α} (k : KeepsM b) {c : Ctx} {x : α} {c' : Ctx}
    (h : b c = .ok (x, c')) : Same c c' := k.out c x c' h

/-- What KeepsM says here of a success of a routine of a sub-proof. -/
theorem same_sub {α : Type} {x : SubM α} (k : KeepsM x) {F : Fork} {c : Ctx} {a : α} {G : Fork}
    {c' : Ctx} (h : x F c = .ok ((a, G), c')) : Same c c' := k.out F c (a, G) c' h

/-- What KeepsM says here of a success of a routine of a link. -/
theorem same_link {α : Type} {x : LinkM α} (k : KeepsM x) {L : LinkCtx} {F : Fork} {c : Ctx}
    {a : α} {L' : LinkCtx} {G : Fork} {c' : Ctx} (h : x L F c = .ok (((a, L'), G), c')) :
    Same c c' := k.out L F c ((a, L'), G) c' h

end OnBytes.Tie.Pv.Tail.Lull

#print axioms OnBytes.Tie.Pv.Tail.Lull.hasLull
#print axioms OnBytes.Tie.Pv.Tail.Lull.lull_takeColumns
#print axioms OnBytes.Tie.Pv.Tail.Lull.same_link
