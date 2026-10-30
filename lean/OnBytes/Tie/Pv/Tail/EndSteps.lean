-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndSteps.lean: a way to show of a whole routine of a sub-proof's check that it
keeps a relation between the state before and the state after, for relations that are known step by
step only.

Definitions, theorems with their proofs, and two tactics. OnBytes/Tie/Pv/Tail/EndWalk.lean has the
same way for relations that hold wherever the arrays' shapes and the batching element are kept. A
relation that speaks of another field of the state (the coefficients of the slots, the plan's number
of claims) is none of these. Here the relation is asked to hold across each of seven basic steps.
The laws and their proofs are those of EndWalk.lean, EndWalkTail.lean and EndWalkHead.lean, with the
class replaced.

Main names:
  `Steps R`: R holds from every state to itself, along two steps in a row, and across: taking slots;
    filling a slot; filling a run of slots; adding a claim without runs; noting a debt; marking it
    paid; noting that an array's root was taken.
  `Stp R x`, `StpL R x`: wherever the routine x returns, R holds from the state before to the state
    after; the second for a routine that also calls the chain. Laws for a value, for «x, then f»,
    for lifted calls, reads, loops, folds and ranges.
  `stp`, `stpL`: the tactics.

Limits: one direction: from a run that returns. No law for a claim with runs (`t2Lin`), for setting
the number of slots, the plan's number of claims or the batching element: a routine that does one of
these is not walked here.


-/
import OnBytes.Tie.Pv.Psc.PscRun
import OnBytes.Tie.Pv.Tail.EndRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.StepsW
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail OnBytes.Tie.Pv.Tail.Port

/-- R holds across each basic step. -/
class Steps (R : Fork → Fork → Prop) : Prop where
  refl : ∀ F, R F F
  trans : ∀ {F G H}, R F G → R G H → R F H
  took : ∀ (F : Fork) (n : Nat), R F { F with next := F.next + n }
  hide : ∀ {F G : Fork} {j : Nat} {y f : E}, F.hide j y f = some G → R F G
  hideRun : ∀ {F G : Fork} {j : Nat} {v : Array E} {f : E}, F.hideRun j v f = some G → R F G
  lin : ∀ {F G : Fork} {f : Aff}, F.lin f = some G → R F G
  owe : ∀ (F : Fork) (what : String), R F (F.owe what).2
  paid : ∀ (F : Fork) (i : Nat), R F (F.paid i)
  rootTaken : ∀ (F : Fork) (t w : Nat), R F (F.rootTaken t w)

/-- Wherever the routine returns, R holds from the state before to the state after. -/
class Stp (R : Fork → Fork → Prop) {α : Type} (x : SubM α) : Prop where
  out : ∀ F c a G c', x F c = .ok ((a, G), c') → R F G

/-- The same for a routine that also calls the chain. -/
class StpL (R : Fork → Fork → Prop) {α : Type} (x : LinkM α) : Prop where
  out : ∀ L F c a L' G c', x L F c = .ok (((a, L'), G), c') → R F G

variable {R : Fork → Fork → Prop}

/-! ## A value; one after the other; lifted calls -/

instance stp_pure [Steps R] {α : Type} (a : α) : Stp R (pure a : SubM α) :=
  ⟨fun F _ _ _ _ h => by
    obtain ⟨_, rfl, _⟩ := (Port.pure_ok _ _ _ _ _ _).1 h
    exact Steps.refl _⟩

/-- «x, then f». -/
theorem stp_bind [Steps R] {α β : Type} {x : SubM α} {f : α → SubM β} (hx : Stp R x)
    (hf : ∀ a, Stp R (f a)) : Stp R (x >>= f) :=
  ⟨fun F c b G c' h => by
    obtain ⟨a, F1, c1, h1, h2⟩ := (Port.bind_ok _ _ _ _ _).1 h
    exact Steps.trans (hx.out F c a F1 c1 h1) ((hf a).out F1 c1 b G c' h2)⟩

/-- A lifted block leaves the sub-proof's state. -/
instance stp_liftS [Steps R] {α : Type} (b : Blk α) : Stp R (StateT.lift b : SubM α) :=
  ⟨fun F c a G c' h => by
    obtain ⟨x, c1, -, e⟩ := (OnBytes.PscRun.lift_ok b F c ((a, G), c')).1 h
    obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
    exact Steps.refl _⟩

/-- The same, as the routines' texts write it. -/
instance stp_liftM [Steps R] {α : Type} (b : Blk α) : Stp R (liftM b : SubM α) :=
  stp_liftS b

/-- The same, in the third spelling. -/
instance stp_monadLift [Steps R] {α : Type} (b : Blk α) : Stp R (monadLift b : SubM α) :=
  stp_liftS b

/-- Reading a value off the state. -/
instance stp_ask [Steps R] {α : Type} (f : Fork → Option α) : Stp R (SubM.ask f) :=
  ⟨fun F _ _ _ _ h => by
    obtain ⟨_, rfl, _⟩ := (Port.ask_ok _ _ _ _ _ _).1 h
    exact Steps.refl _⟩

/-- Unwrapping a value. -/
instance stp_get [Steps R] {α : Type} (x : Option α) : Stp R (SubM.get x) := stp_liftS _

/-- A public condition. -/
instance stp_must [Steps R] (b : Bool) : Stp R (SubM.must b) := stp_liftS _

/-- A condition on values. -/
instance stp_test [Steps R] (b : Bool) : Stp R (SubM.test b) := stp_liftS _

/-- Reading the whole state. -/
instance stp_getF [Steps R] : Stp R (get : SubM Fork) :=
  ⟨fun F c a G c' h => by
    have h' : (Except.ok ((F, F), c) : Except Failure ((Fork × Fork) × Ctx)) = .ok ((a, G), c') := h
    cases h'
    exact Steps.refl _⟩

/-! ## Loops and folds -/

theorem stp_loop [Steps R] {α β : Type} (f : α → β → SubM (ForInStep β))
    (hf : ∀ a b, Stp R (f a b)) : ∀ (l : List α) (b : β), Stp R (forIn l b f)
  | [], b => by
    rw [List.forIn_nil]
    exact stp_pure b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine stp_bind (hf a b) fun r => ?_
    cases r with
    | done b1 => exact stp_pure b1
    | yield b1 => exact stp_loop f hf l b1

/-- A loop over an array. -/
theorem stp_loopArr [Steps R] {α β : Type} (f : α → β → SubM (ForInStep β))
    (hf : ∀ a b, Stp R (f a b)) (as : Array α) (b : β) : Stp R (forIn as b f) := by
  rw [← Array.forIn_toList]
  exact stp_loop f hf as.toList b

/-- A fold over a list. -/
theorem stp_foldlM [Steps R] {α β : Type} (f : β → α → SubM β) (hf : ∀ b a, Stp R (f b a)) :
    ∀ (l : List α) (b : β), Stp R (l.foldlM f b)
  | [], b => by
    rw [List.foldlM_nil]
    exact stp_pure b
  | a :: l, b => by
    rw [List.foldlM_cons]
    exact stp_bind (hf b a) fun b1 => stp_foldlM f hf l b1

/-- A fold over an array. -/
theorem stp_foldlMArr [Steps R] {α β : Type} (f : β → α → SubM β) (hf : ∀ b a, Stp R (f b a))
    (as : Array α) (b : β) : Stp R (as.foldlM f b) := by
  rw [← Array.foldlM_toList]
  exact stp_foldlM f hf as.toList b

/-- A routine for each member of an array. -/
theorem stp_forMArr [Steps R] {α : Type} (f : α → SubM PUnit) (hf : ∀ a, Stp R (f a))
    (as : Array α) : Stp R (as.forM f) := by
  unfold Array.forM
  exact stp_foldlMArr _ (fun _ a => hf a) as _

/-- A routine for each member of a list. -/
theorem stp_forM [Steps R] {α : Type} (f : α → SubM PUnit) (hf : ∀ a, Stp R (f a)) :
    ∀ (l : List α), Stp R (l.forM f)
  | [] => by
    show Stp R (pure PUnit.unit : SubM PUnit)
    exact stp_pure _
  | a :: l => by
    show Stp R (f a >>= fun _ => l.forM f)
    exact stp_bind (hf a) fun _ => stp_forM f hf l

/-! ## The basic steps -/

theorem stp_change (f : Fork → Option Fork) (hf : ∀ F G, f F = some G → R F G) :
    Stp R (SubM.change f) :=
  ⟨fun F c a G c' h => by
    obtain ⟨H, hH, e⟩ := (OnBytes.PscRun.change_ok f F c ((a, G), c')).1 h
    obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
    exact hf F _ hH⟩

/-- A step on the state that returns a value. -/
theorem stp_take {α : Type} (f : Fork → Option (α × Fork))
    (hf : ∀ F a G, f F = some (a, G) → R F G) : Stp R (SubM.take f) :=
  ⟨fun F c a G c' h => by
    obtain ⟨⟨a1, G1⟩, hx, e⟩ := (OnBytes.PscRun.take_ok f F c ((a, G), c')).1 h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
    exact hf F _ _ hx⟩

/-- `SubM.takeSlots` keeps R. -/
instance stp_takeSlots [Steps R] (n : Nat) : Stp R (SubM.takeSlots n) :=
  stp_take _ fun F a G h => by
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Steps.took F n

/-- `SubM.hide` keeps R. -/
instance stp_hide [Steps R] (j : Nat) (y f : E) : Stp R (SubM.hide j y f) :=
  stp_change _ fun _ _ h => Steps.hide h

/-- Putting a run of values under slots. -/
instance stp_hideRun [Steps R] (j : Nat) (v : Array E) (f : E) :
    Stp R (SubM.change (·.hideRun j v f)) :=
  stp_change _ fun _ _ h => Steps.hideRun h

/-- `SubM.lin` keeps R. -/
instance stp_lin [Steps R] (f : Aff) : Stp R (SubM.lin f) :=
  stp_change _ fun _ _ h => Steps.lin h

/-- `SubM.owe` keeps R. -/
instance stp_owe [Steps R] (what : String) : Stp R (SubM.owe what) :=
  stp_take _ fun F a G h => by
    have e2 : (F.owe what).2 = G := congrArg Prod.snd (Option.some.inj h)
    rw [← e2]
    exact Steps.owe F what

/-- `SubM.paid` keeps R. -/
instance stp_paid [Steps R] (i : Nat) : Stp R (SubM.paid i) :=
  stp_change _ fun F _ h => by
    obtain rfl := Option.some.inj h
    exact Steps.paid F i

/-- `SubM.rootTaken` keeps R. -/
instance stp_rootTaken [Steps R] (t w : Nat) : Stp R (SubM.rootTaken t w) :=
  stp_change _ fun F _ h => by
    obtain rfl := Option.some.inj h
    exact Steps.rootTaken F t w

/-! ## The routines on the chain, and the reads of the state -/

instance stp_read [Steps R] (n : Nat) : Stp R (SubM.read n) := stp_liftS _

/-- `SubM.readSum` keeps R. -/
instance stp_readSum [Steps R] : Stp R SubM.readSum := stp_liftS _

/-- `SubM.answer` keeps R. -/
instance stp_answer [Steps R] (r : RoundName) : Stp R (SubM.answer r) := stp_liftS _

/-- `SubM.answerNotZero` keeps R. -/
instance stp_answerNotZero [Steps R] (r : RoundName) : Stp R (SubM.answerNotZero r) :=
  stp_liftS _

/-- `SubM.point` keeps R. -/
instance stp_point [Steps R] (r : RoundName) (n : Nat) : Stp R (SubM.point r n) := stp_liftS _

/-- `SubM.batch` keeps R. -/
instance stp_batch [Steps R] (rows : Nat) : Stp R (SubM.batch rows) := stp_liftS _

/-- `SubM.batchOpen` keeps R. -/
instance stp_batchOpen [Steps R] : Stp R SubM.batchOpen := stp_liftS _

/-- `SubM.batchRows` keeps R. -/
instance stp_batchRows [Steps R] (rows : Nat) : Stp R (SubM.batchRows rows) := stp_liftS _

/-- `SubM.empty` keeps R. -/
instance stp_empty [Steps R] (r : RoundName) : Stp R (SubM.empty r) := stp_liftS _

/-- `SubM.trits` keeps R. -/
instance stp_trits [Steps R] (a b : Nat) : Stp R (SubM.trits a b) := stp_liftS _

/-- `SubM.slot` keeps R. -/
instance stp_slot [Steps R] : Stp R SubM.slot := stp_ask _

/-- `SubM.shown` keeps R. -/
instance stp_shown [Steps R] (j : Nat) : Stp R (SubM.shown j) := stp_ask _

/-- `SubM.publicPart` keeps R. -/
instance stp_publicPart [Steps R] (a : Aff) : Stp R (SubM.publicPart a) := stp_ask _

/-- `SubM.claims` keeps R. -/
instance stp_claims [Steps R] : Stp R SubM.claims := stp_ask _

/-- `SubM.allTaken` keeps R. -/
instance stp_allTaken [Steps R] : Stp R SubM.allTaken := stp_ask _

/-- `SubM.settle` keeps R. -/
instance stp_settle [Steps R] (used : Nat) : Stp R (SubM.settle used) := stp_ask _

/-- A loop over a range of numbers. -/
theorem stp_range [Steps R] {β : Type} (f : Nat → β → SubM (ForInStep β))
    (hf : ∀ a b, Stp R (f a b)) (r : Std.Legacy.Range) (b : β) : Stp R (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact stp_loop f hf _ b

/-- A function applied to what a routine returns. -/
theorem stp_map [Steps R] {α β : Type} (g : α → β) {x : SubM α} (hx : Stp R x) :
    Stp R (g <$> x) := by
  rw [map_eq_pure_bind]
  exact stp_bind hx fun _ => stp_pure _

/-- A routine for each member of an array, with the values gathered. -/
theorem stp_mapMArr [Steps R] {α β : Type} (f : α → SubM β) (hf : ∀ a, Stp R (f a))
    (as : Array α) : Stp R (as.mapM f) := by
  rw [Array.mapM_eq_foldlM]
  exact stp_foldlMArr _ (fun _ a => stp_map _ (hf a)) as _

/-- One step of a walk through a routine's text. -/
macro "stp_step" : tactic => `(tactic| first
  | exact inferInstance
  | refine stp_bind ?_ ?_ | refine stp_loop _ ?_ _ _ | refine stp_loopArr _ ?_ _ _
  | refine stp_foldlM _ ?_ _ _ | refine stp_foldlMArr _ ?_ _ _ | refine stp_forMArr _ ?_ _
  | refine stp_forM _ ?_ _
  | intro _ | split | dsimp only
  | refine stp_range _ ?_ _ _ | refine stp_map _ ?_ | refine stp_mapMArr _ ?_ _)

/-- A walk through a routine's text. -/
macro "stp" : tactic => `(tactic| repeat' stp_step)

/-- `SubM.claimsIn` keeps R. -/
instance stp_claimsIn [Steps R] (n : Nat) : Stp R (SubM.claimsIn n) := by
  unfold SubM.claimsIn
  stp

/-! ## Routines that also call the chain -/

instance stpL_pure [Steps R] {α : Type} (a : α) : StpL R (pure a : LinkM α) :=
  ⟨fun L F c x L' G c' h => by
    obtain ⟨-, -, rfl, -⟩ := (pureL_ok _ _ _ _ _ _ _ _).1 h
    exact Steps.refl _⟩

/-- «x, then f». -/
theorem stpL_bind [Steps R] {α β : Type} {x : LinkM α} {f : α → LinkM β} (hx : StpL R x)
    (hf : ∀ a, StpL R (f a)) : StpL R (x >>= f) :=
  ⟨fun L F c b L' G c' h => by
    obtain ⟨a, L1, F1, c1, h1, h2⟩ := (bindL_ok _ _ _ _ _ _).1 h
    exact Steps.trans (hx.out L F c a L1 F1 c1 h1) ((hf a).out L1 F1 c1 b L' G c' h2)⟩

/-- A lifted routine of the sub-proof. -/
instance stpL_sub {α : Type} (x : SubM α) [hx : Stp R x] : StpL R (LinkM.sub x) :=
  ⟨fun _ F c a _ G c' h => hx.out F c a G c' ((subL_ok _ _ _ _ _ _ _ _).1 h).1⟩

/-- Reading the link's own state. -/
instance stpL_get [Steps R] : StpL R (get : LinkM LinkCtx) :=
  ⟨fun L F c a L' G c' h => by
    have h' : (pure (L, L) : SubM (LinkCtx × LinkCtx)) F c = .ok (((a, L'), G), c') := h
    obtain ⟨-, rfl, -⟩ := (Port.pure_ok _ _ _ _ _ _).1 h'
    exact Steps.refl _⟩

/-- Setting the link's own state. -/
instance stpL_set [Steps R] (L0 : LinkCtx) : StpL R (set L0 : LinkM PUnit) :=
  ⟨fun L F c a L' G c' h => by
    have h' : (pure (PUnit.unit, L0) : SubM (PUnit × LinkCtx)) F c = .ok (((a, L'), G), c') := h
    obtain ⟨-, rfl, -⟩ := (Port.pure_ok _ _ _ _ _ _).1 h'
    exact Steps.refl _⟩

/-- Changing the link's own state. -/
instance stpL_modify [Steps R] (f : LinkCtx → LinkCtx) : StpL R (modify f : LinkM PUnit) :=
  ⟨fun L F c a L' G c' h => by
    have h' : (pure (PUnit.unit, f L) : SubM (PUnit × LinkCtx)) F c = .ok (((a, L'), G), c') := h
    obtain ⟨-, rfl, -⟩ := (Port.pure_ok _ _ _ _ _ _).1 h'
    exact Steps.refl _⟩

/-- A loop over a list. -/
theorem stpL_loop [Steps R] {α β : Type} (f : α → β → LinkM (ForInStep β))
    (hf : ∀ a b, StpL R (f a b)) : ∀ (l : List α) (b : β), StpL R (forIn l b f)
  | [], b => by
    rw [List.forIn_nil]
    exact stpL_pure b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine stpL_bind (hf a b) fun r => ?_
    cases r with
    | done b1 => exact stpL_pure b1
    | yield b1 => exact stpL_loop f hf l b1

/-- `LinkM.must` keeps R. -/
instance stpL_must [Steps R] (b : Bool) : StpL R (LinkM.must b) := stpL_sub _

/-- `LinkM.mustAs` keeps R. -/
instance stpL_mustAs [Steps R] (name : String) (b : Bool) : StpL R (LinkM.mustAs name b) :=
  stpL_sub _

/-- `LinkM.testAs` keeps R. -/
instance stpL_testAs [Steps R] (name : String) (b : Bool) : StpL R (LinkM.testAs name b) :=
  stpL_sub _

/-- `LinkM.fork` keeps R. -/
instance stpL_fork [Steps R] : StpL R LinkM.fork := stpL_sub _

/-- A call of the chain leaves the sub-proof's state. -/
instance stpL_call [Steps R] (f : ChainCheck → Blk ChainCheck) : StpL R (LinkM.call f) :=
  ⟨fun L F c a L' G c' h => by
    have hp : Stp R (do
        SubM.must (L.link == L.check.link)
        let check ← (liftM (f L.check) : SubM ChainCheck)
        pure ((), { L with check := check }) : SubM (Unit × LinkCtx)) := by
      stp
    exact hp.out F c _ G c' h⟩

/-- One step of a walk through the text of a routine that also calls the chain. -/
macro "stpL_step" : tactic => `(tactic| first
  | exact inferInstance
  | refine stpL_bind ?_ ?_ | refine stpL_loop _ ?_ _ _
  | intro _ | split | dsimp only)

/-- A walk through the text of a routine that also calls the chain. -/
macro "stpL" : tactic => `(tactic| repeat' stpL_step)

end OnBytes.Tie.Pv.Tail.StepsW

#print axioms OnBytes.Tie.Pv.Tail.StepsW.stp_bind
#print axioms OnBytes.Tie.Pv.Tail.StepsW.stp_claimsIn
#print axioms OnBytes.Tie.Pv.Tail.StepsW.stpL_call
