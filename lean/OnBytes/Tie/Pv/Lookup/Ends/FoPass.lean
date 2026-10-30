-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPass.lean.
From one state of a run to a later one; lines that turn nothing.

`Passes F G`: every property of a sub-proof's state that the steps keep (`Prim`,
OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean) and
that F has, G has. `Passes.of`, `Passes.ofL`: it holds between the two ends of a run of a routine
that keeps every such property. `Passes.later`, `Passes.ls`: so G is a later state than F with the
slots' arrays at their sizes, and has a coefficient for each slot, if F has.
A property with `Prim` is kept by every change of the books alone, so `Passes` carries nothing on
the number of claims, the batching element, the owed claims or the door's mark.
`IdleB b`, `IdleS x`, `IdleL x`: if the block, the sub-proof's routine or the link's routine
returns, the context (and the sub-proof's state) are as they were.
`linkBind_ok'`, `linkLift_ok'`, `linkBlk_ok`: when a link's routine returns that is put together by
bind, lifted from a sub-proof's routine, or lifted from a block.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvCoef
import OnBytes.Tie.Pv.Lookup.Ends.FoInvInst
import OnBytes.Model.Head

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- Every property that the steps keep passes from F to G. -/
def Passes (F G : Fork) : Prop := ∀ (I : Fork → Prop) [Prim I], I F → I G

theorem Passes.refl (F : Fork) : Passes F F := fun _ _ h => h

theorem Passes.trans {F G H : Fork} (a : Passes F G) (b : Passes G H) : Passes F H :=
  fun I _ h => b I (a I h)

theorem Passes.later {F G : Fork} (h : Passes F G) (hS : Sized F) : Later F G ∧ Sized G :=
  h (fun X => Later F X ∧ Sized X) ⟨Later.refl F, hS⟩

theorem Passes.ls {F G : Fork} (h : Passes F G) (hS : Sized F) (hl : F.LS.size = F.ns) :
    G.LS.size = G.ns :=
  (h (fun X => Sized X ∧ X.LS.size = X.ns) ⟨hS, hl⟩).2

section
variable {α β : Type}

theorem Passes.of {x : SubM α} {F G : Fork} {c c' : Ctx} {a : α}
    (h : x F c = .ok ((a, G), c')) (hk : ∀ (I : Fork → Prop) [Prim I], Inv I x) : Passes F G :=
  fun I _ hI => hk I _ _ _ _ _ h hI

theorem Passes.ofL {x : LinkM α} {L L' : LinkCtx} {F G : Fork} {c c' : Ctx} {a : α}
    (h : x L F c = .ok (((a, L'), G), c')) (hk : ∀ (I : Fork → Prop) [Prim I], InvL I x) :
    Passes F G :=
  fun I _ hI => hk I L _ _ _ _ _ h hI

theorem linkBind_ok' (x : LinkM α) (f : α → LinkM β) (Lc : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((β × LinkCtx) × Fork) × Ctx) :
    (x >>= f) Lc F c = .ok r ↔
      ∃ a Lc1 F1 c1, x Lc F c = .ok (((a, Lc1), F1), c1) ∧ f a Lc1 F1 c1 = .ok r := by
  show (x Lc >>= fun p => f p.1 p.2) F c = .ok r ↔ _
  rw [bind_ok]
  constructor
  · rintro ⟨⟨a, Lc1⟩, F1, c1, h1, h2⟩
    exact ⟨a, Lc1, F1, c1, h1, h2⟩
  · rintro ⟨a, Lc1, F1, c1, h1, h2⟩
    exact ⟨(a, Lc1), F1, c1, h1, h2⟩

theorem linkPure_ok (a : α) (L : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((α × LinkCtx) × Fork) × Ctx) :
    (Pure.pure a : LinkM α) L F c = .ok r ↔ r = (((a, L), F), c) := pure_ok (a, L) F c r

theorem linkLift_ok' (x : SubM α) (Lc Lc1 : LinkCtx) (F G : Fork) (c c' : Ctx) (a : α) :
    (StateT.lift x : LinkM α) Lc F c = .ok (((a, Lc1), G), c') ↔
      x F c = .ok ((a, G), c') ∧ Lc1 = Lc := by
  show (x >>= fun b => (Pure.pure (b, Lc) : SubM (α × LinkCtx))) F c = _ ↔ _
  rw [bind_ok]
  constructor
  · rintro ⟨b, F1, c1, h1, h2⟩
    rw [pure_ok] at h2
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h2
    exact ⟨h1, rfl⟩
  · rintro ⟨h1, rfl⟩
    exact ⟨a, G, c', h1, rfl⟩

theorem linkBlk_ok (b : Blk α) (Lc Lc1 : LinkCtx) (F G : Fork) (c c' : Ctx) (a : α) :
    (StateT.lift (StateT.lift b : SubM α) : LinkM α) Lc F c = .ok (((a, Lc1), G), c') ↔
      b c = .ok (a, c') ∧ G = F ∧ Lc1 = Lc := by
  rw [linkLift_ok', lift_ok]
  constructor
  · rintro ⟨⟨a', c1, h1, e⟩, rfl⟩
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e
    exact ⟨h1, rfl, rfl⟩
  · rintro ⟨h1, rfl, rfl⟩
    exact ⟨⟨a, c', h1, rfl⟩, rfl⟩

/-- Whatever the sub-proof's routine returns has the property. -/
def Yields (x : SubM α) (p : α → Prop) : Prop :=
  ∀ (F : Fork) (c : Ctx) (a : α) (G : Fork) (c' : Ctx), x F c = .ok ((a, G), c') → p a

theorem Yields.pure {p : α → Prop} {a : α} (h : p a) : Yields (Pure.pure a : SubM α) p := by
  intro F c b G c' hr
  rw [pure_ok] at hr
  obtain ⟨⟨rfl, -⟩, -⟩ := by simpa [Prod.ext_iff] using hr
  exact h

theorem Yields.bind {x : SubM α} {f : α → SubM β} {p : β → Prop}
    (hf : ∀ a, Yields (f a) p) : Yields (x >>= f) p := by
  intro F c b G c' hr
  rw [bind_ok] at hr
  obtain ⟨a, F1, c1, -, h2⟩ := hr
  exact hf a _ _ _ _ _ h2

/-- Whatever the link's routine returns has the property. -/
def YieldsL (x : LinkM α) (p : α → Prop) : Prop :=
  ∀ (L : LinkCtx) (F : Fork) (c : Ctx) (a : α) (L' : LinkCtx) (G : Fork) (c' : Ctx),
    x L F c = .ok (((a, L'), G), c') → p a

theorem YieldsL.pure {p : α → Prop} {a : α} (h : p a) : YieldsL (Pure.pure a : LinkM α) p := by
  intro L F c b L' G c' hr
  have e : (((a, L), F), c) = (((b, L'), G), c') := Except.ok.inj hr
  obtain ⟨⟨⟨rfl, -⟩, -⟩, -⟩ := by simpa [Prod.ext_iff] using e
  exact h

theorem YieldsL.bind {x : LinkM α} {f : α → LinkM β} {p : β → Prop}
    (hf : ∀ a, YieldsL (f a) p) : YieldsL (x >>= f) p := by
  intro L F c b L' G c' hr
  rw [linkBind_ok'] at hr
  obtain ⟨a, L1, F1, c1, -, h2⟩ := hr
  exact hf a _ _ _ _ _ _ _ h2

/-- If the block returns, the context is as it was. -/
def IdleB (b : Blk α) : Prop := ∀ c r, b c = .ok r → r.2 = c

/-- If the sub-proof's routine returns, its state and the context are as they were. -/
def IdleS (x : SubM α) : Prop := ∀ F c r, x F c = .ok r → r.1.2 = F ∧ r.2 = c

/-- If the link's routine returns, the sub-proof's state and the context are as they were. -/
def IdleL (x : LinkM α) : Prop :=
  ∀ (L : LinkCtx) (F : Fork) (c : Ctx) (r : ((α × LinkCtx) × Fork) × Ctx),
    x L F c = .ok r → r.1.2 = F ∧ r.2 = c

theorem IdleB.pure (a : α) : IdleB (Pure.pure a : Blk α) := by
  intro c r h
  have e : (a, c) = r := Except.ok.inj h
  rw [← e]

theorem IdleB.refuse (name : String) : IdleB (refuse name : Blk α) := by
  intro c r h
  have e : (Except.error { name := name } : Except Failure (α × Ctx)) = .ok r := h
  cases e

theorem IdleB.mustAs (name : String) (b : Bool) : IdleB (mustAs name b) := by
  unfold OnBytes.Model.mustAs
  cases b
  · exact IdleB.refuse name
  · exact IdleB.pure ()

theorem IdleB.getAs (name : String) (x : Option α) : IdleB (Head.getAs name x) := by
  unfold Head.getAs
  cases x
  · exact IdleB.refuse name
  · exact IdleB.pure _

theorem IdleB.must (b : Bool) (name : String) : IdleB (Blk.must b name) := by
  intro c r h
  unfold Blk.must at h
  split at h
  · rw [← Except.ok.inj h]
  · cases h

theorem IdleB.getO (x : Option α) (name : String) : IdleB (Blk.get x name) := by
  intro c r h
  unfold Blk.get at h
  split at h
  · rw [← Except.ok.inj h]
  · cases h

theorem IdleB.testAs (name : String) (b : Bool) : IdleB (testAs name b) := by
  intro c r h
  unfold OnBytes.Model.testAs at h
  have h' : (if (b || c.ch.dry) = true then (Pure.pure () : Blk Unit)
      else OnBytes.Model.refuse name) c = .ok r := h
  split at h'
  · exact IdleB.pure () c r h'
  · exact IdleB.refuse name c r h'

theorem IdleS.pure (a : α) : IdleS (Pure.pure a : SubM α) := by
  intro F c r h
  rw [pure_ok] at h
  rw [h]
  exact ⟨rfl, rfl⟩

theorem IdleS.bind {x : SubM α} {f : α → SubM β} (hx : IdleS x) (hf : ∀ a, IdleS (f a)) :
    IdleS (x >>= f) := by
  intro F c r h
  rw [bind_ok] at h
  obtain ⟨a, F1, c1, h1, h2⟩ := h
  obtain ⟨e1, e2⟩ := hx F c _ h1
  obtain ⟨e3, e4⟩ := hf a F1 c1 r h2
  exact ⟨e3.trans e1, e4.trans e2⟩

theorem IdleS.lift {b : Blk α} (hb : IdleB b) : IdleS (StateT.lift b : SubM α) := by
  intro F c r h
  rw [lift_ok] at h
  obtain ⟨a, c1, h1, rfl⟩ := h
  exact ⟨rfl, hb c _ h1⟩

theorem IdleS.get : IdleS (MonadState.get : SubM Fork) := by
  intro F c r h
  have e : ((F, F), c) = r := Except.ok.inj h
  rw [← e]
  exact ⟨rfl, rfl⟩

theorem IdleS.ask (f : Fork → Option α) : IdleS (SubM.ask f) := by
  intro F c r h
  rw [ask_ok] at h
  obtain ⟨a, -, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem IdleL.lift {x : SubM α} (hx : IdleS x) : IdleL (StateT.lift x : LinkM α) := by
  rintro L F c ⟨⟨⟨a, L'⟩, G⟩, c'⟩ h
  exact hx F c _ ((linkLift_ok' _ _ _ _ _ _ _ _).1 h).1

theorem IdleL.sub {x : SubM α} (hx : IdleS x) : IdleL (LinkM.sub x) := IdleL.lift hx

theorem IdleL.blk {b : Blk α} (hb : IdleB b) :
    IdleL (StateT.lift (StateT.lift b : SubM α) : LinkM α) := IdleL.lift (IdleS.lift hb)

/-- An idle line of a link's routine, applied to a run. -/
theorem IdleL.of {x : LinkM α} (hx : IdleL x) {L L' : LinkCtx} {F G : Fork} {c c' : Ctx} {a : α}
    (h : x L F c = .ok (((a, L'), G), c')) : G = F ∧ c' = c := hx L F c _ h

/-- A line that is a lifted idle block. -/
theorem blkLine {b : Blk α} (hb : IdleB b) {L L' : LinkCtx} {F G : Fork} {c c' : Ctx} {a : α}
    (h : (StateT.lift (StateT.lift b : SubM α) : LinkM α) L F c = .ok (((a, L'), G), c')) :
    L' = L ∧ G = F ∧ c' = c ∧ b c = .ok (a, c) := by
  obtain ⟨h1, rfl, rfl⟩ := (linkBlk_ok _ _ _ _ _ _ _ _).1 h
  obtain rfl : c' = c := hb c _ h1
  exact ⟨rfl, rfl, rfl, h1⟩

/-- Two runs in a row are a run of the two routines in a row. -/
theorem seq_ok {x : SubM α} {y : SubM β} {F F1 : Fork} {c c1 : Ctx} {a : α}
    {r : (β × Fork) × Ctx} (h1 : x F c = .ok ((a, F1), c1)) (h2 : y F1 c1 = .ok r) :
    (x >>= fun _ => y) F c = .ok r := (bind_ok _ _ _ _ _).2 ⟨_, _, _, h1, h2⟩

theorem ite_true_ok {p : Prop} [Decidable p] (hp : p) {x y : SubM α} {F : Fork} {c : Ctx}
    {r : Except Failure ((α × Fork) × Ctx)} (h : x F c = r) : (if p then x else y) F c = r := by
  rw [if_pos hp]
  exact h

theorem ite_false_ok {p : Prop} [Decidable p] (hp : ¬ p) {x y : SubM α} {F : Fork} {c : Ctx}
    {r : Except Failure ((α × Fork) × Ctx)} (h : y F c = r) : (if p then x else y) F c = r := by
  rw [if_neg hp]
  exact h

theorem mustAs_true {name : String} {b : Bool} {c c' : Ctx} {a : Unit}
    (h : mustAs name b c = .ok (a, c')) : b = true := by
  cases b
  · cases h
  · rfl

/-- A line that is a lifted idle routine of the sub-proof. -/
theorem subLine {x : SubM α} (hx : IdleS x) {L L' : LinkCtx} {F G : Fork} {c c' : Ctx} {a : α}
    (h : (StateT.lift x : LinkM α) L F c = .ok (((a, L'), G), c')) :
    L' = L ∧ G = F ∧ c' = c := by
  obtain ⟨h1, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h
  obtain ⟨e1, e2⟩ := hx F c _ h1
  exact ⟨rfl, e1, e2⟩

/-- A line that unwraps a public value. -/
theorem formLine {x : Option α} {L L' : LinkCtx} {F G : Fork} {c c' : Ctx} {a : α}
    (h : LinkM.sub (SubM.get x) L F c = .ok (((a, L'), G), c')) :
    x = some a ∧ L' = L ∧ G = F ∧ c' = c := by
  obtain ⟨h1, rfl⟩ := (linkLift_ok' _ _ _ _ _ _ _ _).1 h
  obtain ⟨b, hb, e⟩ := (get_ok _ _ _ _).1 h1
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e
  exact ⟨hb, rfl, rfl, rfl⟩

/-- The line that reads the link's state. -/
theorem getLine {L L' a : LinkCtx} {F G : Fork} {c c' : Ctx}
    (h : (MonadState.get : LinkM LinkCtx) L F c = .ok (((a, L'), G), c')) :
    a = L ∧ L' = L ∧ G = F ∧ c' = c := by
  have e : (((L, L), F), c) = (((a, L'), G), c') := Except.ok.inj h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem IdleL.get : IdleL (MonadState.get : LinkM LinkCtx) := by
  rintro L F c r h
  have e : (((L, L), F), c) = r := Except.ok.inj h
  rw [← e]
  exact ⟨rfl, rfl⟩

end
end Fo
