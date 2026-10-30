-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Keeps/StillKit.lean: the routines that begin and close no round of the view: wherever
such a routine succeeds, the round whose message is being received and the rounds that are not yet
begun are as they were.

Definitions, statements and proofs. The rules and tactics of OnBytes/Tie/Pv/Keeps/KeepsLift.lean and
the commands of OnBytes/Tie/Pv/Keeps/KeepsWalk.lean are stated for any property of a monad's
routines that pure has and bind carries (the class HasKeeps). Inside the namespace of this file the
blocks get another such property than Keeps of OnBytes/Tie/Pv/Keeps/KeepsKit.lean: `StillB`. So
KeepsM x reads here, and here alone: x begins and closes no round. A file that wants both readings
does not open this namespace: it takes the statements in plain words (`Same`) that
OnBytes/Tie/Pv/Keeps/StillRan.lean draws from the class. Of the calls of OnBytes/Iop/Ground.lean
that are written as functions of the context all have the property but two: Blk.item, which takes
an item off a round, and Blk.close.
Main names:
  `Same c c'`: c' has the fields cur and left of c's channel.
  `StillB b`: wherever the block b succeeds, the context that it leaves is `Same`.
  `hasStill`: the class HasKeeps for blocks at `StillB`; it holds inside this namespace alone,
    before the library's own.
  `still_fail` and the 25 that follow: the calls of Ground.lean.
  `still_named`, `still_inPlace`, `still_except`, `still_getThe`; `still_change`, `still_take`,
    `still_ask`: further calls that are written as functions of a state.
  `same_blk`, `same_sub`, `same_link`: what KeepsM says here of a success of a block, of a routine
    of a sub-proof and of a routine of a link.
Tactics of this file.
  still_prim d: proves KeepsM, in the reading of this namespace, of a call d that is written as a
    function of the context: it unfolds d, goes through its cases, and closes each case: a failure,
    or a context with the same cur and left.
Limits: one direction: from a success. In both readings of a block (a dry run and a run on a view).
-/
import OnBytes.Tie.Pv.Keeps.KeepsWalk
import OnBytes.Model.Trees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Keeps.Still

open OnBytes OnBytes.Model OnBytes.L5

/-- c' has the fields cur and left of c's channel. -/
structure Same (c c' : Ctx) : Prop where
  cur : c'.ch.cur = c.ch.cur
  left : c'.ch.left = c.ch.left

theorem Same.refl (c : Ctx) : Same c c := ⟨rfl, rfl⟩

theorem Same.trans {a b c : Ctx} (h1 : Same a b) (h2 : Same b c) : Same a c :=
  ⟨h2.cur.trans h1.cur, h2.left.trans h1.left⟩

/-- Wherever the block succeeds, it has begun and closed no round. -/
def StillB {α : Type} (b : Blk α) : Prop := ∀ c x c', b c = .ok (x, c') → Same c c'

/-- For a block, inside this namespace: StillB. -/
scoped instance (priority := high) hasStill : HasKeeps Blk where
  K := fun b => StillB b
  K_pure := fun a c x c' h => by cases h; exact Same.refl _
  K_bind := fun b f hb hf c y c2 h => by
    obtain ⟨x, c1, h1, h2⟩ := (Blk.yields_bind b f c c2 y).1 ((Blk.yields_iff _ _ _ _).2 h)
    exact (hb _ _ _ ((Blk.yields_iff _ _ _ _).1 h1)).trans
      (hf x _ _ _ ((Blk.yields_iff _ _ _ _).1 h2))

/-- For a call that is written as a function of the context. -/
macro "still_prim " d:ident : tactic =>
  `(tactic| (
      refine ⟨fun c x c' h => ?_⟩
      unfold $d at h
      try dsimp only at h
      repeat' (split at h)
      all_goals first
        | (cases h; done)
        | (cases h; exact ⟨rfl, rfl⟩)))

/-! ## The calls of Ground.lean that are functions of the context -/

instance still_fail {α : Type} (n : String) : KeepsM (Blk.fail n : Blk α) := by still_prim Blk.fail
instance still_must (b : Bool) (n : String) : KeepsM (Blk.must b n) := by still_prim Blk.must
instance still_test (b : Bool) (n : String) : KeepsM (Blk.test b n) := by still_prim Blk.test
instance still_check (n : String) (b : Bool) : KeepsM (Blk.check n b) := by still_prim Blk.check
instance still_onView {α : Type} (d : α) (f : Unit → α) : KeepsM (Blk.onView d f) := by
  still_prim Blk.onView
instance still_getOnView {α : Type} (d : α) (f : Unit → Option α) (n : String) :
    KeepsM (Blk.getOnView d f n) := by
  still_prim Blk.getOnView
instance still_testOnView (f : Unit → Bool) (n : String) : KeepsM (Blk.testOnView f n) := by
  still_prim Blk.testOnView
instance still_checkOnView (n : String) (f : Unit → Bool) : KeepsM (Blk.checkOnView n f) := by
  still_prim Blk.checkOnView
instance still_get {α : Type} (x : Option α) (n : String) : KeepsM (Blk.get x n) := by
  still_prim Blk.get
instance still_isDry : KeepsM Blk.isDry := by still_prim Blk.isDry
instance still_samples : KeepsM Blk.samples := by still_prim Blk.samples
instance still_firstTree : KeepsM Blk.firstTree := by still_prim Blk.firstTree
instance still_lastEntry : KeepsM Blk.lastEntry := by still_prim Blk.lastEntry
instance still_note (w : String) (v : E) : KeepsM (Blk.note w v) := by still_prim Blk.note
instance still_noteBy (w : String) (v : Unit → E) : KeepsM (Blk.noteBy w v) := by
  still_prim Blk.noteBy
instance still_statement : KeepsM Blk.statement := by still_prim Blk.statement
instance still_setStatement (S : Statement) : KeepsM (Blk.setStatement S) := by
  still_prim Blk.setStatement
instance still_recvRoot : KeepsM Blk.recvRoot := by still_prim Blk.recvRoot
instance still_requireRows (r : Nat) : KeepsM (Blk.requireRows r) := by still_prim Blk.requireRows
instance still_handOver : KeepsM Blk.handOver := by still_prim Blk.handOver
instance still_onOracle (o : Nat) (f : Oracle → Oracle) : KeepsM (Blk.onOracle o f) := by
  still_prim Blk.onOracle
instance still_onGroup (g : Nat) (f : Group → Group) : KeepsM (Blk.onGroup g f) := by
  still_prim Blk.onGroup
instance still_theBook : KeepsM Blk.theBook := by still_prim Blk.theBook
instance still_setBook (B : TreeBook) : KeepsM (Blk.setBook B) := by still_prim Blk.setBook
instance still_takeColumns (t : Tree) (xs : Array Nat) : KeepsM (Blk.takeColumns t xs) := by
  still_prim Blk.takeColumns
instance still_readStored (t : Fmt.Stored) (p : Positions) : KeepsM (Blk.readStored t p) := by
  still_prim Blk.readStored

instance still_named {α : Type} (n : String) (b : Blk α) [hb : KeepsM b] :
    KeepsM (Blk.named n b) :=
  ⟨fun c x c' h => by
    unfold Blk.named at h
    split at h
    · cases h
    · cases h; exact hb.out _ _ _ (by assumption)⟩

instance still_inPlace {α : Type} (n : String) (b : Blk α) [hb : KeepsM b] :
    KeepsM (Blk.inPlace n b) :=
  ⟨fun c x c' h => by
    unfold Blk.inPlace at h
    split at h
    · cases h
    · cases h; exact hb.out _ _ _ (by assumption)⟩

/-- What has no context, lifted into a block. -/
instance still_except {α : Type} {n : Type → Type} [MonadLiftT n (Except Failure)] (x : n α) :
    KeepsM (monadLift x : Blk α) :=
  ⟨fun c y c' h => by
    have h' : ((monadLift x : Except Failure α) >>= fun a => pure (a, c)) = .ok (y, c') := h
    cases e : (monadLift x : Except Failure α) with
    | error f => rw [e] at h'; cases h'
    | ok a => rw [e] at h'; cases h'; exact Same.refl _⟩

instance still_getThe : KeepsM (getThe Ctx : Blk Ctx) :=
  ⟨fun c x c' h => by cases h; exact Same.refl _⟩

/-! ## The three calls of OnBytes/Model/Hide.lean that are functions of both states -/

instance still_change (f : Fork → Option Fork) : KeepsM (SubM.change f) :=
  ⟨fun F c y c' h => by
    unfold SubM.change at h
    cases e : f F with
    | none => rw [e] at h; cases h
    | some a => rw [e] at h; cases h; exact Same.refl _⟩

instance still_take {α : Type} (f : Fork → Option (α × Fork)) : KeepsM (SubM.take f) :=
  ⟨fun F c y c' h => by
    unfold SubM.take at h
    cases e : f F with
    | none => rw [e] at h; cases h
    | some a => rw [e] at h; cases h; exact Same.refl _⟩

instance still_ask {α : Type} (f : Fork → Option α) : KeepsM (SubM.ask f) :=
  ⟨fun F c y c' h => by
    unfold SubM.ask at h
    cases e : f F with
    | none => rw [e] at h; cases h
    | some a => rw [e] at h; cases h; exact Same.refl _⟩

/-! ## What KeepsM says here of a success -/

theorem same_blk {α : Type} {b : Blk α} (k : KeepsM b) {c : Ctx} {x : α} {c' : Ctx}
    (h : b c = .ok (x, c')) : Same c c' := k.out c x c' h

theorem same_sub {α : Type} {x : SubM α} (k : KeepsM x) {F : Fork} {c : Ctx} {a : α} {G : Fork}
    {c' : Ctx} (h : x F c = .ok ((a, G), c')) : Same c c' := k.out F c (a, G) c' h

theorem same_link {α : Type} {x : LinkM α} (k : KeepsM x) {L : LinkCtx} {F : Fork} {c : Ctx}
    {a : α} {L' : LinkCtx} {G : Fork} {c' : Ctx} (h : x L F c = .ok (((a, L'), G), c')) :
    Same c c' := k.out L F c ((a, L'), G) c' h

end OnBytes.Tie.Pv.Keeps.Still

#print axioms OnBytes.Tie.Pv.Keeps.Still.hasStill
#print axioms OnBytes.Tie.Pv.Keeps.Still.still_takeColumns
#print axioms OnBytes.Tie.Pv.Keeps.Still.same_link
