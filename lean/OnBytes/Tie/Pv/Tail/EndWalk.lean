-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndWalk.lean: a way to show of a whole routine of a sub-proof's check that it
keeps something of the sub-proof's state, by a walk through the routine's text.

Definitions, theorems with their proofs, and one tactic. A routine (`SubM`, OnBytes/Model/Hide.lean;
`LinkM`, OnBytes/Model/Trees.lean) changes the sub-proof's state only by a few basic steps. If each
basic step stands in a relation R that is reflexive and transitive, so does every routine that is
made of them.

Main names:
  `Prim R`: R is reflexive and transitive, and holds wherever the arrays' shapes and the batching
    element are kept (`FrameKept`, OnBytes/Tie/Pv/Tail/EndKeep.lean). `PrimS R`: it holds already
    where the shapes are kept (`ShapesKept`). The two relations themselves are the examples.
  `Pres R x`, `PresL R x`: wherever the routine x returns, R holds from the state before to the
    state after: for short, «x keeps R». Both are classes, so that a law that is proved once is
    found again. Laws for a value, for «x, then f», for lifted calls, reads, tests, loops and folds;
    for each basic step of OnBytes/Model/Hide.lean; for `t2Lin`.
  `walk`: the tactic: one step after the other through a routine's text.

Limits: one direction: from a run that returns. Nothing on what a routine adds or reads.


-/
import OnBytes.Tie.Pv.Psc.PscRun
import OnBytes.Tie.Pv.Tail.EndRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Walk
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail OnBytes.Tie.Pv.Tail.Port

/-- R is reflexive and transitive, and holds wherever shapes and batching element are kept. -/
class Prim (R : Fork → Fork → Prop) : Prop where
  refl : ∀ F, R F F
  trans : ∀ {F G H}, R F G → R G H → R F H
  ofFrame : ∀ {F G}, FrameKept F G → R F G

/-- R holds already where the shapes are kept. -/
class PrimS (R : Fork → Fork → Prop) : Prop extends Prim R where
  ofShapes : ∀ {F G}, ShapesKept F G → R F G

/-- The first example. -/
instance : PrimS ShapesKept where
  refl := ShapesKept.refl
  trans := ShapesKept.trans
  ofFrame := fun h => h.shapes
  ofShapes := fun h => h

/-- The second example. -/
instance : Prim FrameKept where
  refl := FrameKept.refl
  trans := FrameKept.trans
  ofFrame := fun h => h

/-- Wherever the routine returns, R holds from the state before to the state after. -/
class Pres (R : Fork → Fork → Prop) {α : Type} (x : SubM α) : Prop where
  out : ∀ F c a G c', x F c = .ok ((a, G), c') → R F G

/-- The same for a routine that also calls the chain. -/
class PresL (R : Fork → Fork → Prop) {α : Type} (x : LinkM α) : Prop where
  out : ∀ L F c a L' G c', x L F c = .ok (((a, L'), G), c') → R F G

variable {R : Fork → Fork → Prop}

/-! ## A value; one after the other; lifted calls -/

instance pres_pure [Prim R] {α : Type} (a : α) : Pres R (pure a : SubM α) :=
  ⟨fun F _ _ _ _ h => by
    obtain ⟨_, rfl, _⟩ := (Port.pure_ok _ _ _ _ _ _).1 h
    exact Prim.refl _⟩

/-- «x, then f». -/
theorem pres_bind [Prim R] {α β : Type} {x : SubM α} {f : α → SubM β} (hx : Pres R x)
    (hf : ∀ a, Pres R (f a)) : Pres R (x >>= f) :=
  ⟨fun F c b G c' h => by
    obtain ⟨a, F1, c1, h1, h2⟩ := (Port.bind_ok _ _ _ _ _).1 h
    exact Prim.trans (hx.out F c a F1 c1 h1) ((hf a).out F1 c1 b G c' h2)⟩

/-- A lifted block leaves the sub-proof's state. -/
instance pres_liftS [Prim R] {α : Type} (b : Blk α) : Pres R (StateT.lift b : SubM α) :=
  ⟨fun F c a G c' h => by
    obtain ⟨x, c1, -, e⟩ := (OnBytes.PscRun.lift_ok b F c ((a, G), c')).1 h
    obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
    exact Prim.refl _⟩

/-- The same, as the routines' texts write it. -/
instance pres_liftM [Prim R] {α : Type} (b : Blk α) : Pres R (liftM b : SubM α) :=
  pres_liftS b

/-- The same, in the third spelling. -/
instance pres_monadLift [Prim R] {α : Type} (b : Blk α) : Pres R (monadLift b : SubM α) :=
  pres_liftS b

/-- Reading a value off the state. -/
instance pres_ask [Prim R] {α : Type} (f : Fork → Option α) : Pres R (SubM.ask f) :=
  ⟨fun F _ _ _ _ h => by
    obtain ⟨_, rfl, _⟩ := (Port.ask_ok _ _ _ _ _ _).1 h
    exact Prim.refl _⟩

/-- Unwrapping a value. -/
instance pres_get [Prim R] {α : Type} (x : Option α) : Pres R (SubM.get x) := pres_liftS _

/-- A public condition. -/
instance pres_must [Prim R] (b : Bool) : Pres R (SubM.must b) := pres_liftS _

/-- A condition on values. -/
instance pres_test [Prim R] (b : Bool) : Pres R (SubM.test b) := pres_liftS _

/-- Reading the whole state. -/
instance pres_getF [Prim R] : Pres R (get : SubM Fork) :=
  ⟨fun F c a G c' h => by
    have h' : (Except.ok ((F, F), c) : Except Failure ((Fork × Fork) × Ctx)) = .ok ((a, G), c') := h
    cases h'
    exact Prim.refl _⟩

/-! ## Loops and folds -/

theorem pres_loop [Prim R] {α β : Type} (f : α → β → SubM (ForInStep β))
    (hf : ∀ a b, Pres R (f a b)) : ∀ (l : List α) (b : β), Pres R (forIn l b f)
  | [], b => by
    rw [List.forIn_nil]
    exact pres_pure b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine pres_bind (hf a b) fun r => ?_
    cases r with
    | done b1 => exact pres_pure b1
    | yield b1 => exact pres_loop f hf l b1

/-- A loop over an array. -/
theorem pres_loopArr [Prim R] {α β : Type} (f : α → β → SubM (ForInStep β))
    (hf : ∀ a b, Pres R (f a b)) (as : Array α) (b : β) : Pres R (forIn as b f) := by
  rw [← Array.forIn_toList]
  exact pres_loop f hf as.toList b

/-- A fold over a list. -/
theorem pres_foldlM [Prim R] {α β : Type} (f : β → α → SubM β) (hf : ∀ b a, Pres R (f b a)) :
    ∀ (l : List α) (b : β), Pres R (l.foldlM f b)
  | [], b => by
    rw [List.foldlM_nil]
    exact pres_pure b
  | a :: l, b => by
    rw [List.foldlM_cons]
    exact pres_bind (hf b a) fun b1 => pres_foldlM f hf l b1

/-- A fold over an array. -/
theorem pres_foldlMArr [Prim R] {α β : Type} (f : β → α → SubM β) (hf : ∀ b a, Pres R (f b a))
    (as : Array α) (b : β) : Pres R (as.foldlM f b) := by
  rw [← Array.foldlM_toList]
  exact pres_foldlM f hf as.toList b

/-- A routine for each member of an array. -/
theorem pres_forMArr [Prim R] {α : Type} (f : α → SubM PUnit) (hf : ∀ a, Pres R (f a))
    (as : Array α) : Pres R (as.forM f) := by
  unfold Array.forM
  exact pres_foldlMArr _ (fun _ a => hf a) as _

/-- A routine for each member of a list. -/
theorem pres_forM [Prim R] {α : Type} (f : α → SubM PUnit) (hf : ∀ a, Pres R (f a)) :
    ∀ (l : List α), Pres R (l.forM f)
  | [] => by
    show Pres R (pure PUnit.unit : SubM PUnit)
    exact pres_pure _
  | a :: l => by
    show Pres R (f a >>= fun _ => l.forM f)
    exact pres_bind (hf a) fun _ => pres_forM f hf l

/-! ## The basic steps -/

theorem pres_change (f : Fork → Option Fork) (hf : ∀ F G, f F = some G → R F G) :
    Pres R (SubM.change f) :=
  ⟨fun F c a G c' h => by
    obtain ⟨H, hH, e⟩ := (OnBytes.PscRun.change_ok f F c ((a, G), c')).1 h
    obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
    exact hf F _ hH⟩

/-- A step on the state that returns a value. -/
theorem pres_take {α : Type} (f : Fork → Option (α × Fork))
    (hf : ∀ F a G, f F = some (a, G) → R F G) : Pres R (SubM.take f) :=
  ⟨fun F c a G c' h => by
    obtain ⟨⟨a1, G1⟩, hx, e⟩ := (OnBytes.PscRun.take_ok f F c ((a, G), c')).1 h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
    exact hf F _ _ hx⟩

/-- `SubM.takeSlots` keeps R. -/
instance pres_takeSlots [Prim R] (n : Nat) : Pres R (SubM.takeSlots n) :=
  pres_take _ fun F a G h => by
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Prim.ofFrame (took_frame F n)

/-- `SubM.hide` keeps R. -/
instance pres_hide [Prim R] (j : Nat) (y f : E) : Pres R (SubM.hide j y f) :=
  pres_change _ fun _ _ h => Prim.ofFrame (hide_frame h)

/-- Putting a run of values under slots. -/
instance pres_hideRun [Prim R] (j : Nat) (v : Array E) (f : E) :
    Pres R (SubM.change (·.hideRun j v f)) :=
  pres_change _ fun _ _ h => Prim.ofFrame (hideRun_frame h)

/-- `SubM.kap` keeps R. -/
instance pres_kap [Prim R] : Pres R SubM.kap :=
  pres_take _ fun _ _ _ h => Prim.ofFrame (kap_frame h)

/-- `SubM.push` keeps R. -/
instance pres_push [Prim R] (w : E) (a : Aff) : Pres R (SubM.push w a) :=
  pres_change _ fun _ _ h => Prim.ofFrame (push_frame h)

/-- `SubM.lin` keeps R. -/
instance pres_lin [Prim R] (f : Aff) : Pres R (SubM.lin f) :=
  pres_change _ fun _ _ h => Prim.ofFrame (lin_frame h)

/-- `SubM.owe` keeps R. -/
instance pres_owe [Prim R] (what : String) : Pres R (SubM.owe what) :=
  pres_take _ fun F a G h => by
    have e := Option.some.inj h
    have e2 : (F.owe what).2 = G := congrArg Prod.snd e
    rw [← e2]
    exact Prim.ofFrame (owe_frame F what)

/-- `SubM.paid` keeps R. -/
instance pres_paid [Prim R] (i : Nat) : Pres R (SubM.paid i) :=
  pres_change _ fun F _ h => by
    obtain rfl := Option.some.inj h
    exact Prim.ofFrame (paid_frame F i)

/-- `SubM.rootTaken` keeps R. -/
instance pres_rootTaken [Prim R] (t w : Nat) : Pres R (SubM.rootTaken t w) :=
  pres_change _ fun F _ h => by
    obtain rfl := Option.some.inj h
    exact Prim.ofFrame (rootTaken_frame F t w)

/-- `SubM.setPlanClaims` keeps R. -/
instance pres_setPlanClaims [Prim R] (n : Nat) : Pres R (SubM.setPlanClaims n) :=
  pres_change _ fun F _ h => by
    obtain rfl := Option.some.inj h
    exact Prim.ofFrame (FrameKept.of_same rfl rfl)

/-- `SubM.batchBy` keeps R, where R asks nothing of the batching element: the routine sets it. -/
instance pres_batchBy [PrimS R] (x : E) : Pres R (SubM.batchBy x) :=
  pres_change _ fun _ _ h => PrimS.ofShapes (batchBy_shapes h)

/-- `SubM.slots` keeps R. -/
instance pres_slots [PrimS R] (n : Nat) : Pres R (SubM.slots n) :=
  pres_change _ fun F _ h => by
    obtain rfl := Option.some.inj h
    exact PrimS.ofShapes (slots_shapes F n)

/-! ## The routines on the chain, and the reads of the state -/

instance pres_read [Prim R] (n : Nat) : Pres R (SubM.read n) := pres_liftS _

/-- `SubM.readSum` keeps R. -/
instance pres_readSum [Prim R] : Pres R SubM.readSum := pres_liftS _

/-- `SubM.answer` keeps R. -/
instance pres_answer [Prim R] (r : RoundName) : Pres R (SubM.answer r) := pres_liftS _

/-- `SubM.answerNotZero` keeps R. -/
instance pres_answerNotZero [Prim R] (r : RoundName) : Pres R (SubM.answerNotZero r) :=
  pres_liftS _

/-- `SubM.point` keeps R. -/
instance pres_point [Prim R] (r : RoundName) (n : Nat) : Pres R (SubM.point r n) := pres_liftS _

/-- `SubM.batch` keeps R. -/
instance pres_batch [Prim R] (rows : Nat) : Pres R (SubM.batch rows) := pres_liftS _

/-- `SubM.batchOpen` keeps R. -/
instance pres_batchOpen [Prim R] : Pres R SubM.batchOpen := pres_liftS _

/-- `SubM.batchRows` keeps R. -/
instance pres_batchRows [Prim R] (rows : Nat) : Pres R (SubM.batchRows rows) := pres_liftS _

/-- `SubM.empty` keeps R. -/
instance pres_empty [Prim R] (r : RoundName) : Pres R (SubM.empty r) := pres_liftS _

/-- `SubM.trits` keeps R. -/
instance pres_trits [Prim R] (a b : Nat) : Pres R (SubM.trits a b) := pres_liftS _

/-- `SubM.slot` keeps R. -/
instance pres_slot [Prim R] : Pres R SubM.slot := pres_ask _

/-- `SubM.shown` keeps R. -/
instance pres_shown [Prim R] (j : Nat) : Pres R (SubM.shown j) := pres_ask _

/-- `SubM.publicPart` keeps R. -/
instance pres_publicPart [Prim R] (a : Aff) : Pres R (SubM.publicPart a) := pres_ask _

/-- `SubM.claims` keeps R. -/
instance pres_claims [Prim R] : Pres R SubM.claims := pres_ask _

/-- `SubM.allTaken` keeps R. -/
instance pres_allTaken [Prim R] : Pres R SubM.allTaken := pres_ask _

/-- `SubM.settle` keeps R. -/
instance pres_settle [Prim R] (used : Nat) : Pres R (SubM.settle used) := pres_ask _

/-- One step of a walk through a routine's text. -/
macro "walk_step" : tactic => `(tactic| first
  | exact inferInstance
  | refine pres_bind ?_ ?_ | refine pres_loop _ ?_ _ _ | refine pres_loopArr _ ?_ _ _
  | refine pres_foldlM _ ?_ _ _ | refine pres_foldlMArr _ ?_ _ _ | refine pres_forMArr _ ?_ _
  | refine pres_forM _ ?_ _
  | intro _ | split | dsimp only)

/-- A walk through a routine's text. -/
macro "walk" : tactic => `(tactic| repeat' walk_step)

/-- `SubM.claimsIn` keeps R. -/
instance pres_claimsIn [Prim R] (n : Nat) : Pres R (SubM.claimsIn n) := by
  unfold SubM.claimsIn
  walk

end OnBytes.Tie.Pv.Tail.Walk

#print axioms OnBytes.Tie.Pv.Tail.Walk.pres_bind
#print axioms OnBytes.Tie.Pv.Tail.Walk.pres_loop
#print axioms OnBytes.Tie.Pv.Tail.Walk.pres_lin
#print axioms OnBytes.Tie.Pv.Tail.Walk.pres_claimsIn
