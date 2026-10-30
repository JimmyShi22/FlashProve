-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean.
A run on a view stays on the view: the rules at the three levels of the byte-level verifier's
routines, and a tactic.

`Dry b` (OnBytes/Tie/Pv/Lookup/Ends/FoChan.lean) says of a block b that a run on a view that returns
is still on the view;
`DryS` and `DryL` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) say the same of a sub-proof's routine
and of a link's routine,
from every state.

 * The rules at each level: pure, bind, map, the loops (`foldlM`, `forIn`, `forM`, `mapM`, over
   lists and arrays), the lifts from one level to the next, reading and setting a level's own state.
 * `stays`: a tactic that proves `Dry b`, `DryS x` or `DryL x` by these rules. It opens the
   program's definitions that it meets (names under OnBytes alone), splits if and match, and applies
   hypotheses. A lemma on a named routine is taught to it by a further rule for `stays_rule`. A
   definition by recursion wants a lemma of its own by induction.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoSite

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

section
variable {α β : Type}

/-! ### blocks -/

theorem Dry.map {x : Blk α} (f : α → β) (hx : Dry x) : Dry (f <$> x) := by
  rw [← bind_pure_comp]
  exact hx.bind fun _ => Dry.pure _

theorem Dry.foldlM {σ : Type} {f : σ → α → Blk σ} (hf : ∀ s a, Dry (f s a)) :
    ∀ (l : List α) (s : σ), Dry (l.foldlM f s)
  | [], s => Dry.pure s
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact (hf s a).bind fun s' => Dry.foldlM hf l s'

theorem Dry.arrayFoldlM {σ : Type} {f : σ → α → Blk σ} (hf : ∀ s a, Dry (f s a))
    (l : Array α) (s : σ) : Dry (l.foldlM f s) := by
  rw [← Array.foldlM_toList]
  exact Dry.foldlM hf _ s

theorem Dry.forM {f : α → Blk PUnit} (hf : ∀ a, Dry (f a)) : ∀ l : List α, Dry (l.forM f)
  | [] => Dry.pure _
  | a :: l => by
    show Dry (f a >>= fun _ => l.forM f)
    exact (hf a).bind fun _ => Dry.forM hf l

theorem Dry.arrayForM {f : α → Blk PUnit} (hf : ∀ a, Dry (f a)) (l : Array α) :
    Dry (l.forM f) := by
  unfold Array.forM
  exact Dry.arrayFoldlM (fun _ a => hf a) l _

theorem Dry.mapM {f : α → Blk β} (hf : ∀ a, Dry (f a)) : ∀ l : List α, Dry (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    exact Dry.pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact (hf a).bind fun _ => (Dry.mapM hf l).bind fun _ => Dry.pure _

theorem Dry.arrayMapM {f : α → Blk β} (hf : ∀ a, Dry (f a)) (l : Array α) :
    Dry (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  exact (Dry.mapM hf _).map _

/-! ### a sub-proof's routines -/

theorem DryS.pure (a : α) : DryS (Pure.pure a : SubM α) := (CalmS.pure a).dry
theorem DryS.monadLift {b : Blk α} (h : Dry b) : DryS (MonadLiftT.monadLift b : SubM α) :=
  DryS.lift h
theorem DryS.liftM {b : Blk α} (h : Dry b) : DryS (_root_.liftM b : SubM α) := DryS.lift h
theorem DryS.ask (f : Fork → Option α) : DryS (SubM.ask f) := (CalmS.ask f).dry
theorem DryS.take (f : Fork → Option (α × Fork)) : DryS (SubM.take f) := (CalmS.take f).dry
theorem DryS.change (f : Fork → Option Fork) : DryS (SubM.change f) := (CalmS.change f).dry
theorem DryS.get : DryS (MonadState.get : SubM Fork) := fun F => Dry.pure (F, F)

theorem DryS.map {x : SubM α} (f : α → β) (hx : DryS x) : DryS (f <$> x) := by
  rw [← bind_pure_comp]
  exact hx.bind fun _ => DryS.pure _

theorem DryS.foldlM {σ : Type} {f : σ → α → SubM σ} (hf : ∀ s a, DryS (f s a)) :
    ∀ (l : List α) (s : σ), DryS (l.foldlM f s)
  | [], s => DryS.pure s
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact (hf s a).bind fun s' => DryS.foldlM hf l s'

theorem DryS.arrayFoldlM {σ : Type} {f : σ → α → SubM σ} (hf : ∀ s a, DryS (f s a))
    (l : Array α) (s : σ) : DryS (l.foldlM f s) := by
  rw [← Array.foldlM_toList]
  exact DryS.foldlM hf _ s

theorem DryS.forIn {σ : Type} {f : α → σ → SubM (ForInStep σ)} (hf : ∀ a s, DryS (f a s)) :
    ∀ (l : List α) (s : σ), DryS (ForIn.forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    exact DryS.pure s
  | a :: l, s => by
    rw [List.forIn_cons]
    refine (hf a s).bind fun r => ?_
    cases r with
    | done b => exact DryS.pure b
    | yield b => exact DryS.forIn hf l b

theorem DryS.arrayForIn {σ : Type} {f : α → σ → SubM (ForInStep σ)}
    (hf : ∀ a s, DryS (f a s)) (l : Array α) (s : σ) : DryS (ForIn.forIn l s f) := by
  rw [← Array.forIn_toList]
  exact DryS.forIn hf _ s

theorem DryS.forM {f : α → SubM PUnit} (hf : ∀ a, DryS (f a)) : ∀ l : List α, DryS (l.forM f)
  | [] => DryS.pure _
  | a :: l => by
    show DryS (f a >>= fun _ => l.forM f)
    exact (hf a).bind fun _ => DryS.forM hf l

theorem DryS.arrayForM {f : α → SubM PUnit} (hf : ∀ a, DryS (f a)) (l : Array α) :
    DryS (l.forM f) := by
  unfold Array.forM
  exact DryS.arrayFoldlM (fun _ a => hf a) l _

theorem DryS.mapM {f : α → SubM β} (hf : ∀ a, DryS (f a)) : ∀ l : List α, DryS (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    exact DryS.pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact (hf a).bind fun _ => (DryS.mapM hf l).bind fun _ => DryS.pure _

theorem DryS.arrayMapM {f : α → SubM β} (hf : ∀ a, DryS (f a)) (l : Array α) :
    DryS (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  exact (DryS.mapM hf _).map _

/-! ### a link's routines -/

theorem DryL.pure (a : α) : DryL (Pure.pure a : LinkM α) := (CalmL.pure a).dry
theorem DryL.bind {x : LinkM α} {f : α → LinkM β} (hx : DryL x) (hf : ∀ a, DryL (f a)) :
    DryL (x >>= f) := fun L =>
  DryS.bind (x := x L) (f := fun p => f p.1 p.2) (hx L) fun p => hf p.1 p.2
theorem DryL.lift {x : SubM α} (h : DryS x) : DryL (StateT.lift x : LinkM α) := DryL.sub h
theorem DryL.monadLift {x : SubM α} (h : DryS x) : DryL (MonadLiftT.monadLift x : LinkM α) :=
  DryL.sub h
theorem DryL.liftM {x : SubM α} (h : DryS x) : DryL (_root_.liftM x : LinkM α) := DryL.sub h
theorem DryL.monadLiftB {b : Blk α} (h : Dry b) : DryL (MonadLiftT.monadLift b : LinkM α) :=
  DryL.sub (DryS.lift h)
theorem DryL.liftMB {b : Blk α} (h : Dry b) : DryL (_root_.liftM b : LinkM α) :=
  DryL.sub (DryS.lift h)
theorem DryL.get : DryL (MonadState.get : LinkM LinkCtx) := CalmL.get.dry
theorem DryL.set (s : LinkCtx) : DryL (MonadStateOf.set s : LinkM PUnit) := fun _ =>
  DryS.pure (α := PUnit × LinkCtx) (PUnit.unit, s)
theorem DryL.modify (f : LinkCtx → LinkCtx) : DryL (_root_.modify f : LinkM PUnit) :=
  (CalmL.modify f).dry
theorem DryL.fn {x : LinkCtx → SubM (α × LinkCtx)} (h : ∀ L, DryS (x L)) :
    DryL (x : LinkM α) := h

theorem DryL.map {x : LinkM α} (f : α → β) (hx : DryL x) : DryL (f <$> x) := by
  rw [← bind_pure_comp]
  exact hx.bind fun _ => DryL.pure _

theorem DryL.foldlM {σ : Type} {f : σ → α → LinkM σ} (hf : ∀ s a, DryL (f s a)) :
    ∀ (l : List α) (s : σ), DryL (l.foldlM f s)
  | [], s => DryL.pure s
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact (hf s a).bind fun s' => DryL.foldlM hf l s'

theorem DryL.arrayFoldlM {σ : Type} {f : σ → α → LinkM σ} (hf : ∀ s a, DryL (f s a))
    (l : Array α) (s : σ) : DryL (l.foldlM f s) := by
  rw [← Array.foldlM_toList]
  exact DryL.foldlM hf _ s

theorem DryL.forIn {σ : Type} {f : α → σ → LinkM (ForInStep σ)} (hf : ∀ a s, DryL (f a s)) :
    ∀ (l : List α) (s : σ), DryL (ForIn.forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    exact DryL.pure s
  | a :: l, s => by
    rw [List.forIn_cons]
    refine (hf a s).bind fun r => ?_
    cases r with
    | done b => exact DryL.pure b
    | yield b => exact DryL.forIn hf l b

theorem DryL.arrayForIn {σ : Type} {f : α → σ → LinkM (ForInStep σ)}
    (hf : ∀ a s, DryL (f a s)) (l : Array α) (s : σ) : DryL (ForIn.forIn l s f) := by
  rw [← Array.forIn_toList]
  exact DryL.forIn hf _ s

theorem DryL.forM {f : α → LinkM PUnit} (hf : ∀ a, DryL (f a)) : ∀ l : List α, DryL (l.forM f)
  | [] => DryL.pure _
  | a :: l => by
    show DryL (f a >>= fun _ => l.forM f)
    exact (hf a).bind fun _ => DryL.forM hf l

theorem DryL.arrayForM {f : α → LinkM PUnit} (hf : ∀ a, DryL (f a)) (l : Array α) :
    DryL (l.forM f) := by
  unfold Array.forM
  exact DryL.arrayFoldlM (fun _ a => hf a) l _

theorem DryL.mapM {f : α → LinkM β} (hf : ∀ a, DryL (f a)) : ∀ l : List α, DryL (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    exact DryL.pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact (hf a).bind fun _ => (DryL.mapM hf l).bind fun _ => DryL.pure _

theorem DryL.arrayMapM {f : α → LinkM β} (hf : ∀ a, DryL (f a)) (l : Array α) :
    DryL (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  exact (DryL.mapM hf _).map _

end

/-! ### the tactic -/

open Lean Meta Elab Tactic in
/-- Opens the definition at the head of the routine in a goal `Dry`, `DryS` or `DryL`. -/
elab "stays_open" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Fo.Dry 2 || t.isAppOfArity ``Fo.DryS 2 || t.isAppOfArity ``Fo.DryL 2 do
    throwError "not a goal of the three words"
  let x := t.appArg!
  let some n := x.getAppFn.constName? | throwError "no constant at the head"
  unless (`OnBytes).isPrefixOf n do throwError "the head is no routine of the program"
  if [``SubM.change, ``SubM.take, ``SubM.ask, ``LinkM.sub, ``Blk.item, ``Blk.close].contains n then
    throwError "a step that has its rule"
  if ← isMatcher n then throwError "a match"
  let some x' ← unfoldDefinition? x | throwError "no definition to open"
  replaceMainGoal [← g.change (mkApp t.appFn! x'.headBeta)]

open Lean Meta Elab Tactic in
/-- Takes in a bound variable, if the goal begins with one as it is written. -/
elab "stays_intro" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless t.isForall do throwError "no bound variable"
  evalTactic (← `(tactic| intro _))

open Lean Meta Elab Tactic in
/-- Applies a hypothesis. -/
elab "stays_hyp" : tactic => withMainContext do
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

open Lean Meta Elab Tactic in
/-- Lays a local definition at the head of the routine in, and applies a function that is written
out to its argument. -/
elab "stays_norm" : tactic => do
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

/-- One step by a rule whose routine is the goal's as it is written. -/
syntax "stays_rule" : tactic
macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible first
  | exact Dry.pure _ | exact dry_item _ _ | exact (shut_close _ _ _).dry
  | (refine Calm.dry ?_; calm_atom)
  | exact DryS.pure _ | exact DryS.ask _ | exact DryS.take _ | exact DryS.change _
  | exact DryS.get
  | exact DryL.pure _ | exact DryL.get | exact DryL.set _ | exact DryL.modify _
  | stays_hyp
  | apply DryS.lift | apply DryS.monadLift | apply DryS.liftM
  | apply DryL.sub | apply DryL.monadLiftB | apply DryL.liftMB
  | apply DryL.lift | apply DryL.monadLift | apply DryL.liftM
  | apply Dry.bind | apply Dry.map | apply Dry.foldlM | apply Dry.arrayFoldlM
  | apply Dry.loop | apply Dry.loopA | apply Dry.forM | apply Dry.arrayForM
  | apply Dry.mapM | apply Dry.arrayMapM
  | apply DryS.bind | apply DryS.map | apply DryS.foldlM | apply DryS.arrayFoldlM
  | apply DryS.forIn | apply DryS.arrayForIn | apply DryS.forM | apply DryS.arrayForM
  | apply DryS.mapM | apply DryS.arrayMapM
  | apply DryL.bind | apply DryL.map | apply DryL.foldlM | apply DryL.arrayFoldlM
  | apply DryL.forIn | apply DryL.arrayForIn | apply DryL.forM | apply DryL.arrayForM)

/-- One step. -/
macro "stays_step" : tactic => `(tactic| first
  | stays_intro | stays_norm | stays_rule | stays_open | split)

/-- Proves `Dry`, `DryS` or `DryL` of a routine. -/
macro "stays" : tactic => `(tactic| repeat' stays_step)

end Fo
