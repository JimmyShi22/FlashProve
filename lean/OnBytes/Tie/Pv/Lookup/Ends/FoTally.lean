-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTally.lean.
Routines of a sub-proof that leave the number of claims added and the number of claims planned as
they were.

`TallyRel F G`: the state G has F's nClaim and planClaimsF. `Tally x`: whenever the routine x
returns, the state that it leaves has these two numbers as they were. The file has the rules by
which the property passes through the ways in which routines are put together (pure, bind, a lifted
routine of the channel, a branch, a loop), proves it of the steps on the state that have it, and has
a tactic, `tally`, that proves it of a routine by these rules, opening the definitions that it
meets.
The steps that add a claim (kap, lin) or set the plan's number (setPlanClaims) are given no rule:
that they do not have the property is read off OnBytes/Model/Hide.lean and is no statement here.
The rules and the tactic follow OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean and
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean, which do the same for another property.

Does not say: anything on the one equation, the batching element, the owed claims or the door's
mark. SubM.push, which adds a weighted form to the one equation, and SubM.batchBy, which sets the
batching element, have the property. A routine that never returns has it too.

Not claimed: anything on soundness, completeness or hiding.

-/
import Lean.Elab.Tactic
import OnBytes.Tie.Pv.Psc.PscRun
import OnBytes.Model.Look

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- The two numbers are the same. -/
def TallyRel (F G : Fork) : Prop := G.nClaim = F.nClaim ∧ G.planClaimsF = F.planClaimsF

theorem TallyRel.refl (F : Fork) : TallyRel F F := ⟨rfl, rfl⟩

theorem TallyRel.trans {F G H : Fork} (h1 : TallyRel F G) (h2 : TallyRel G H) : TallyRel F H :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

/-- The routine leaves the two numbers. -/
def Tally {α : Type} (x : SubM α) : Prop :=
  ∀ (F : Fork) (c : Ctx) (a : α) (G : Fork) (c' : Ctx), x F c = .ok ((a, G), c') → TallyRel F G

section
variable {α β : Type}

theorem Tally.pure (a : α) : Tally (Pure.pure a : SubM α) := by
  intro F c b G c' h
  rw [pure_ok] at h
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using h
  exact TallyRel.refl _

theorem Tally.bind {x : SubM α} {f : α → SubM β} (hx : Tally x) (hf : ∀ a, Tally (f a)) :
    Tally (x >>= f) := by
  intro F c b G c' h
  rw [bind_ok] at h
  obtain ⟨a, F1, c1, h1, h2⟩ := h
  exact (hx _ _ _ _ _ h1).trans (hf a _ _ _ _ _ h2)

theorem Tally.lift (b : Blk α) : Tally (StateT.lift b : SubM α) := by
  intro F c a G c' h
  rw [lift_ok] at h
  obtain ⟨a', c1, -, e⟩ := h
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
  exact TallyRel.refl _

theorem Tally.ask (f : Fork → Option α) : Tally (SubM.ask f) := by
  intro F c a G c' h
  rw [ask_ok] at h
  obtain ⟨a', -, e⟩ := h
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
  exact TallyRel.refl _

theorem Tally.change {f : Fork → Option Fork} (hf : ∀ F G, f F = some G → TallyRel F G) :
    Tally (SubM.change f) := by
  intro F c a G c' h
  rw [change_ok] at h
  obtain ⟨G', hG, e⟩ := h
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
  exact hf _ _ hG

theorem Tally.take {f : Fork → Option (α × Fork)} (hf : ∀ F y, f F = some y → TallyRel F y.2) :
    Tally (SubM.take f) := by
  intro F c a G c' h
  rw [take_ok] at h
  obtain ⟨y, hy, e⟩ := h
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
  exact hf _ _ hy

/-- A change of the whole state by a function. -/
theorem Tally.modify {f : Fork → Fork} (hf : ∀ F, TallyRel F (f F)) :
    Tally (_root_.modify f : SubM PUnit) := by
  intro F c a G c' h
  have e : ((PUnit.unit, f F), c) = ((a, G), c') := Except.ok.inj h
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
  exact hf F

theorem Tally.ite {p : Prop} [Decidable p] {x y : SubM α} (hx : Tally x) (hy : Tally y) :
    Tally (if p then x else y) := by
  split
  · exact hx
  · exact hy

theorem Tally.map {x : SubM α} (f : α → β) (hx : Tally x) : Tally (f <$> x) := by
  rw [← bind_pure_comp]
  exact hx.bind fun _ => Tally.pure _

theorem Tally.monadLift (b : Blk α) : Tally (MonadLiftT.monadLift b : SubM α) := Tally.lift b

theorem Tally.liftM (b : Blk α) : Tally (liftM b : SubM α) := Tally.lift b

theorem Tally.get : Tally (MonadState.get : SubM Fork) := by
  intro F c a G c' h
  have e : ((F, F), c) = ((a, G), c') := Except.ok.inj h
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
  exact TallyRel.refl _

/-! ### loops -/

theorem Tally.foldlM {σ : Type} {f : σ → α → SubM σ} (hf : ∀ s a, Tally (f s a)) :
    ∀ (l : List α) (s : σ), Tally (l.foldlM f s)
  | [], s => Tally.pure s
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact (hf s a).bind fun s' => Tally.foldlM hf l s'

theorem Tally.arrayFoldlM {σ : Type} {f : σ → α → SubM σ} (hf : ∀ s a, Tally (f s a))
    (l : Array α) (s : σ) : Tally (l.foldlM f s) := by
  rw [← Array.foldlM_toList]
  exact Tally.foldlM hf _ s

theorem Tally.forIn {σ : Type} {f : α → σ → SubM (ForInStep σ)} (hf : ∀ a s, Tally (f a s)) :
    ∀ (l : List α) (s : σ), Tally (ForIn.forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    exact Tally.pure s
  | a :: l, s => by
    rw [List.forIn_cons]
    refine (hf a s).bind fun r => ?_
    cases r with
    | done b => exact Tally.pure b
    | yield b => exact Tally.forIn hf l b

theorem Tally.arrayForIn {σ : Type} {f : α → σ → SubM (ForInStep σ)} (hf : ∀ a s, Tally (f a s))
    (l : Array α) (s : σ) : Tally (ForIn.forIn l s f) := by
  rw [← Array.forIn_toList]
  exact Tally.forIn hf _ s

theorem Tally.forM {f : α → SubM PUnit} (hf : ∀ a, Tally (f a)) :
    ∀ l : List α, Tally (l.forM f)
  | [] => Tally.pure _
  | a :: l => by
    show Tally (f a >>= fun _ => l.forM f)
    exact (hf a).bind fun _ => Tally.forM hf l

theorem Tally.arrayForM {f : α → SubM PUnit} (hf : ∀ a, Tally (f a)) (l : Array α) :
    Tally (l.forM f) := by
  unfold Array.forM
  exact Tally.arrayFoldlM (fun _ a => hf a) l _

theorem Tally.mapM {f : α → SubM β} (hf : ∀ a, Tally (f a)) : ∀ l : List α, Tally (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    exact Tally.pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact (hf a).bind fun _ => (Tally.mapM hf l).bind fun _ => Tally.pure _

theorem Tally.arrayMapM {f : α → SubM β} (hf : ∀ a, Tally (f a)) (l : Array α) :
    Tally (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  exact (Tally.mapM hf _).map _

end

/-! ### the steps on the state -/

theorem Tally.must (b : Bool) : Tally (SubM.must b) := Tally.lift _
theorem Tally.test (b : Bool) : Tally (SubM.test b) := Tally.lift _
theorem Tally.getO {α : Type} (x : Option α) : Tally (SubM.get x) := Tally.lift _
theorem Tally.read (n : Nat) : Tally (SubM.read n) := Tally.lift _
theorem Tally.readSum : Tally SubM.readSum := Tally.lift _
theorem Tally.answer (r : RoundName) : Tally (SubM.answer r) := Tally.lift _
theorem Tally.answerNotZero (r : RoundName) : Tally (SubM.answerNotZero r) := Tally.lift _
theorem Tally.point (r : RoundName) (n : Nat) : Tally (SubM.point r n) := Tally.lift _
theorem Tally.batch (n : Nat) : Tally (SubM.batch n) := Tally.lift _
theorem Tally.batchOpen : Tally SubM.batchOpen := Tally.lift _
theorem Tally.batchRows (n : Nat) : Tally (SubM.batchRows n) := Tally.lift _
theorem Tally.empty (r : RoundName) : Tally (SubM.empty r) := Tally.lift _
theorem Tally.trits (a b : Nat) : Tally (SubM.trits a b) := Tally.lift _
theorem Tally.slot : Tally SubM.slot := Tally.ask _
theorem Tally.shown (j : Nat) : Tally (SubM.shown j) := Tally.ask _
theorem Tally.publicPart (a : Aff) : Tally (SubM.publicPart a) := Tally.ask _
theorem Tally.claims : Tally SubM.claims := Tally.ask _
theorem Tally.allTaken : Tally SubM.allTaken := Tally.ask _
theorem Tally.settle (n : Nat) : Tally (SubM.settle n) := Tally.ask _

theorem Tally.takeSlots (n : Nat) : Tally (SubM.takeSlots n) :=
  Tally.take fun F y h => by
    obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl⟩
theorem Tally.owe (s : String) : Tally (SubM.owe s) :=
  Tally.take fun F _ h => by
    obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl⟩
theorem Tally.paid (i : Nat) : Tally (SubM.paid i) :=
  Tally.change fun F _ h => by
    obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl⟩
theorem Tally.rootTaken (t w : Nat) : Tally (SubM.rootTaken t w) :=
  Tally.change fun F _ h => by
    obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl⟩

theorem batchBy_cl {F G : Fork} {d : E} (h : F.batchBy d = some G) : TallyRel F G := by
  unfold Fork.batchBy at h
  split at h
  · exact absurd h (by simp)
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl⟩

theorem push_cl {F G : Fork} {w : E} {a : Aff} (h : F.push w a = some G) : TallyRel F G := by
  unfold Fork.push at h
  split at h
  · exact absurd h (by simp)
  · simp only at h
    split at h
    · obtain rfl := Option.some.inj h
      exact ⟨rfl, rfl⟩
    · exact absurd h (by simp)

theorem Tally.batchBy (d : E) : Tally (SubM.batchBy d) := Tally.change fun _ _ h => batchBy_cl h
theorem Tally.push (w : E) (a : Aff) : Tally (SubM.push w a) := Tally.change fun _ _ h => push_cl h

/-! ### the tactic -/

open Lean Meta Elab Tactic in
/-- Opens the definition at the head of the routine in a goal `Tally x`. -/
elab "tally_open" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Fo.Tally 2 do throwError "not a goal Tally x"
  let x := t.appArg!
  let some n := x.getAppFn.constName? | throwError "no constant at the head"
  unless (`OnBytes).isPrefixOf n do throwError "the head is no routine of the program"
  if [``SubM.change, ``SubM.take, ``SubM.ask].contains n then throwError "a step on the state"
  if ← isMatcher n then throwError "a match"
  let some x' ← unfoldDefinition? x | throwError "no definition to open"
  replaceMainGoal [← g.change (mkApp t.appFn! x'.headBeta)]

open Lean Meta Elab Tactic in
/-- Takes in a bound variable, if the goal begins with one as it is written. -/
elab "tally_intro" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless t.isForall do throwError "no bound variable"
  evalTactic (← `(tactic| intro _))

open Lean Meta Elab Tactic in
/-- Applies a hypothesis. -/
elab "tally_hyp" : tactic => withMainContext do
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

/-- A step on the state that is written out and leaves the two numbers alone. -/
macro "tally_change" : tactic => `(tactic| first
  | ((with_reducible refine Tally.change fun F G h => ?_)
     have e := Option.some.inj h
     subst e
     exact ⟨Eq.refl _, Eq.refl _⟩)
  | ((with_reducible refine Tally.take fun F y h => ?_)
     have e := Option.some.inj h
     subst e
     exact ⟨Eq.refl _, Eq.refl _⟩))

/-- One step by a rule whose routine is the goal's as it is written. -/
macro "tally_rule" : tactic => `(tactic| with_reducible first
  | exact Tally.pure _ | exact Tally.lift _ | exact Tally.monadLift _ | exact Tally.liftM _
  | exact Tally.ask _ | exact Tally.get
  | exact Tally.must _ | exact Tally.test _ | exact Tally.getO _ | exact Tally.read _
  | exact Tally.readSum | exact Tally.answer _ | exact Tally.answerNotZero _
  | exact Tally.point _ _ | exact Tally.batch _ | exact Tally.batchOpen | exact Tally.batchRows _
  | exact Tally.empty _ | exact Tally.trits _ _ | exact Tally.slot | exact Tally.shown _
  | exact Tally.publicPart _ | exact Tally.claims | exact Tally.allTaken | exact Tally.settle _
  | exact Tally.takeSlots _ | exact Tally.owe _ | exact Tally.paid _ | exact Tally.rootTaken _ _
  | exact Tally.batchBy _ | exact Tally.push _ _
  | tally_hyp
  | apply Tally.bind | apply Tally.map
  | apply Tally.foldlM | apply Tally.arrayFoldlM | apply Tally.forIn | apply Tally.arrayForIn
  | apply Tally.forM | apply Tally.arrayForM | apply Tally.mapM | apply Tally.arrayMapM)

open Lean Meta Elab Tactic in
/-- Lays a local definition at the head of the routine in, and applies a function that is written
out to its argument. -/
elab "tally_norm" : tactic => do
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
macro "tally_step" : tactic => `(tactic| first
  | tally_intro
  | tally_norm
  | tally_rule
  | tally_change
  | tally_open
  | split)

/-- Proves `Tally x`. -/
macro "tally" : tactic => `(tactic| repeat' tally_step)

end Fo
