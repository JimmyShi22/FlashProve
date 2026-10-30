-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoHush.lean.
Routines of a sub-proof that change nothing.

`HushB b`: if the block b returns, the context is as it was. `Hush x`: if the routine x of a
sub-proof returns, the sub-proof's state and the context are as they were. The file has the rules by
which the property passes through the ways in which routines are put together, proves it of the
tests and of the questions to the state, and has a tactic, `hush`, that proves it of a routine by
these rules, opening the definitions that it meets. The rules and the tactic follow
OnBytes/Tie/Pv/Lookup/Ends/FoTally.lean.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTally

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- If the block returns, the context is as it was. -/
def HushB {α : Type} (b : Blk α) : Prop :=
  ∀ (c : Ctx) (a : α) (c' : Ctx), b c = .ok (a, c') → c' = c

/-- If the routine returns, the state and the context are as they were. -/
def Hush {α : Type} (x : SubM α) : Prop :=
  ∀ (F : Fork) (c : Ctx) (a : α) (G : Fork) (c' : Ctx), x F c = .ok ((a, G), c') → G = F ∧ c' = c

section
variable {α β : Type}

theorem HushB.must (b : Bool) (name : String) : HushB (Blk.must b name) := by
  intro c a c' h
  unfold Blk.must at h
  split at h
  · exact (congrArg Prod.snd (Except.ok.inj h)).symm
  · cases h

theorem HushB.test (b : Bool) (name : String) : HushB (Blk.test b name) := by
  intro c a c' h
  unfold Blk.test at h
  split at h
  · exact (congrArg Prod.snd (Except.ok.inj h)).symm
  · cases h

theorem HushB.getO (x : Option α) (name : String) : HushB (Blk.get x name) := by
  intro c a c' h
  unfold Blk.get at h
  split at h
  · exact (congrArg Prod.snd (Except.ok.inj h)).symm
  · cases h

theorem HushB.mustAs (name : String) (b : Bool) : HushB (mustAs name b) := by
  intro c a c' h
  unfold OnBytes.Model.mustAs at h
  split at h
  · exact (congrArg Prod.snd (Except.ok.inj h)).symm
  · cases h

theorem HushB.testAs (name : String) (b : Bool) : HushB (testAs name b) := by
  intro c a c' h
  have h' : (if (b || c.ch.dry) = true then (Pure.pure () : Blk Unit) else refuse name) c =
      .ok (a, c') := h
  split at h'
  · exact (congrArg Prod.snd (Except.ok.inj h')).symm
  · cases h'

theorem Hush.pure (a : α) : Hush (Pure.pure a : SubM α) := by
  intro F c b G c' h
  rw [pure_ok] at h
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h
  exact ⟨rfl, rfl⟩

theorem Hush.bind {x : SubM α} {f : α → SubM β} (hx : Hush x) (hf : ∀ a, Hush (f a)) :
    Hush (x >>= f) := by
  intro F c b G c' h
  rw [bind_ok] at h
  obtain ⟨a, F1, c1, h1, h2⟩ := h
  obtain ⟨rfl, rfl⟩ := hx _ _ _ _ _ h1
  exact hf a _ _ _ _ _ h2

theorem Hush.lift {b : Blk α} (hb : HushB b) : Hush (StateT.lift b : SubM α) := by
  intro F c a G c' h
  rw [lift_ok] at h
  obtain ⟨a', c1, h1, e⟩ := h
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e
  exact ⟨rfl, hb _ _ _ h1⟩

theorem Hush.monadLift {b : Blk α} (hb : HushB b) : Hush (MonadLiftT.monadLift b : SubM α) :=
  Hush.lift hb

theorem Hush.liftM {b : Blk α} (hb : HushB b) : Hush (_root_.liftM b : SubM α) := Hush.lift hb

theorem Hush.ask (f : Fork → Option α) : Hush (SubM.ask f) := by
  intro F c a G c' h
  rw [ask_ok] at h
  obtain ⟨a', -, e⟩ := h
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e
  exact ⟨rfl, rfl⟩

theorem Hush.ite {p : Prop} [Decidable p] {x y : SubM α} (hx : Hush x) (hy : Hush y) :
    Hush (if p then x else y) := by
  split
  · exact hx
  · exact hy

theorem Hush.map {x : SubM α} (f : α → β) (hx : Hush x) : Hush (f <$> x) := by
  rw [← bind_pure_comp]
  exact hx.bind fun _ => Hush.pure _

theorem Hush.get : Hush (MonadState.get : SubM Fork) := by
  intro F c a G c' h
  have e : ((F, F), c) = ((a, G), c') := Except.ok.inj h
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e
  exact ⟨rfl, rfl⟩

/-! ### loops -/

theorem Hush.foldlM {σ : Type} {f : σ → α → SubM σ} (hf : ∀ s a, Hush (f s a)) :
    ∀ (l : List α) (s : σ), Hush (l.foldlM f s)
  | [], s => Hush.pure s
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact (hf s a).bind fun s' => Hush.foldlM hf l s'

theorem Hush.arrayFoldlM {σ : Type} {f : σ → α → SubM σ} (hf : ∀ s a, Hush (f s a))
    (l : Array α) (s : σ) : Hush (l.foldlM f s) := by
  rw [← Array.foldlM_toList]
  exact Hush.foldlM hf _ s

theorem Hush.forIn {σ : Type} {f : α → σ → SubM (ForInStep σ)} (hf : ∀ a s, Hush (f a s)) :
    ∀ (l : List α) (s : σ), Hush (ForIn.forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    exact Hush.pure s
  | a :: l, s => by
    rw [List.forIn_cons]
    refine (hf a s).bind fun r => ?_
    cases r with
    | done b => exact Hush.pure b
    | yield b => exact Hush.forIn hf l b

theorem Hush.arrayForIn {σ : Type} {f : α → σ → SubM (ForInStep σ)} (hf : ∀ a s, Hush (f a s))
    (l : Array α) (s : σ) : Hush (ForIn.forIn l s f) := by
  rw [← Array.forIn_toList]
  exact Hush.forIn hf _ s

theorem Hush.forM {f : α → SubM PUnit} (hf : ∀ a, Hush (f a)) :
    ∀ l : List α, Hush (l.forM f)
  | [] => Hush.pure _
  | a :: l => by
    show Hush (f a >>= fun _ => l.forM f)
    exact (hf a).bind fun _ => Hush.forM hf l

theorem Hush.arrayForM {f : α → SubM PUnit} (hf : ∀ a, Hush (f a)) (l : Array α) :
    Hush (l.forM f) := by
  unfold Array.forM
  exact Hush.arrayFoldlM (fun _ a => hf a) l _

theorem Hush.mapM {f : α → SubM β} (hf : ∀ a, Hush (f a)) : ∀ l : List α, Hush (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    exact Hush.pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact (hf a).bind fun _ => (Hush.mapM hf l).bind fun _ => Hush.pure _

theorem Hush.arrayMapM {f : α → SubM β} (hf : ∀ a, Hush (f a)) (l : Array α) :
    Hush (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  exact (Hush.mapM hf _).map _

end

/-! ### the tests and the questions -/

theorem Hush.must (b : Bool) : Hush (SubM.must b) := Hush.lift (HushB.must _ _)
theorem Hush.test (b : Bool) : Hush (SubM.test b) := Hush.lift (HushB.test _ _)
theorem Hush.getO {α : Type} (x : Option α) : Hush (SubM.get x) := Hush.lift (HushB.getO _ _)
theorem Hush.slot : Hush SubM.slot := Hush.ask _
theorem Hush.shown (j : Nat) : Hush (SubM.shown j) := Hush.ask _
theorem Hush.publicPart (a : Aff) : Hush (SubM.publicPart a) := Hush.ask _
theorem Hush.claims : Hush SubM.claims := Hush.ask _
theorem Hush.allTaken : Hush SubM.allTaken := Hush.ask _
theorem Hush.settle (n : Nat) : Hush (SubM.settle n) := Hush.ask _

/-! ### the tactic -/

open Lean Meta Elab Tactic in
/-- Opens the definition at the head of the routine in a goal `Hush x`. -/
elab "hush_open" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Fo.Hush 2 do throwError "not a goal Hush x"
  let x := t.appArg!
  let some n := x.getAppFn.constName? | throwError "no constant at the head"
  unless (`OnBytes).isPrefixOf n do throwError "the head is no routine of the program"
  if [``SubM.change, ``SubM.take, ``SubM.ask].contains n then throwError "a step on the state"
  if ← isMatcher n then throwError "a match"
  let some x' ← unfoldDefinition? x | throwError "no definition to open"
  replaceMainGoal [← g.change (mkApp t.appFn! x'.headBeta)]

open Lean Meta Elab Tactic in
/-- Takes in a bound variable, if the goal begins with one as it is written. -/
elab "hush_intro" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless t.isForall do throwError "no bound variable"
  evalTactic (← `(tactic| intro _))

open Lean Meta Elab Tactic in
/-- Applies a hypothesis. -/
elab "hush_hyp" : tactic => withMainContext do
  let g ← getMainGoal
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    unless (← isProp d.type) do continue
    let s ← saveState
    try
      let gs ← withReducible (g.apply d.toExpr)
      replaceMainGoal gs
      return
    catch _ => s.restore
  throwError "no hypothesis applies"

/-- No step that changes the state has the property. -/
macro "hush_change" : tactic => `(tactic| fail "a step that changes the state")

/-- One step by a rule whose routine is the goal's as it is written. -/
macro "hush_rule" : tactic => `(tactic| with_reducible first
  | exact Hush.pure _ | exact Hush.ask _ | exact Hush.get
  | exact HushB.must _ _ | exact HushB.test _ _ | exact HushB.getO _ _ | exact HushB.mustAs _ _
  | exact HushB.testAs _ _
  | exact Hush.must _ | exact Hush.test _ | exact Hush.getO _
  | exact Hush.slot | exact Hush.shown _
  | exact Hush.publicPart _ | exact Hush.claims | exact Hush.allTaken | exact Hush.settle _
  | apply Hush.lift | apply Hush.monadLift | apply Hush.liftM
  | hush_hyp
  | apply Hush.bind | apply Hush.map
  | apply Hush.foldlM | apply Hush.arrayFoldlM | apply Hush.forIn | apply Hush.arrayForIn
  | apply Hush.forM | apply Hush.arrayForM | apply Hush.mapM | apply Hush.arrayMapM)

open Lean Meta Elab Tactic in
/-- Lays a local definition at the head of the routine in, and applies a function that is written
out to its argument. -/
elab "hush_norm" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isApp do throwError "no routine"
  let x := t.appArg!
  let one (e : Expr) : Expr :=
    match e with
    | .letE _ _ v b _ => b.instantiate1 v
    | .mdata _ b => b
    | _ => e.headBeta
  let x' := one x
  if x' == x then throwError "nothing to do"
  replaceMainGoal [← g.change (mkApp t.appFn! x')]

/-- One step. -/
macro "hush_step" : tactic => `(tactic| first
  | hush_intro
  | hush_norm
  | hush_rule
  | hush_change
  | hush_open
  | split)

/-- Proves `Hush x`. -/
macro "hush" : tactic => `(tactic| repeat' hush_step)

end Fo
