-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvSteps.lean.
The steps on a sub-proof's state keep every property that has `Prim`; a tactic.

`inv`: a tactic that proves `Inv I x` of a routine by the rules of
OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean and of this file,
opening the definitions that it meets.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInv

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem Book.refl (F : Fork) : Book F F := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Book.trans {F G H : Fork} (a : Book F G) (b : Book G H) : Book F H :=
  ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.1.trans a.2.2.1, b.2.2.2.1.trans a.2.2.2.1,
    b.2.2.2.2.1.trans a.2.2.2.2.1, b.2.2.2.2.2.1.trans a.2.2.2.2.2.1,
    b.2.2.2.2.2.2.1.trans a.2.2.2.2.2.2.1, b.2.2.2.2.2.2.2.trans a.2.2.2.2.2.2.2⟩

theorem kapTake_book {F : Fork} {c : ℕ} {y : E × Fork} (h : F.kapTake c = some y) :
    Book F y.2 := by
  unfold Fork.kapTake at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Book.refl F
    · split at h
      · obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.mp h
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact absurd h (by simp)

theorem kap_book {F : Fork} {y : E × Fork} (h : F.kap = some y) : Book F y.2 := by
  unfold Fork.kap at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (kapTake_book hx).trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem batchBy_book {F G : Fork} {d : E} (h : F.batchBy d = some G) : Book F G := by
  unfold Fork.batchBy at h
  split at h
  · exact absurd h (by simp)
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

section
variable {I : Fork → Prop} [Prim I]

theorem Inv.push (w : E) (a : Aff) : Inv I (SubM.push w a) :=
  Inv.change fun _ _ h hS => Prim.push _ _ _ _ h hS
theorem Inv.kap : Inv I SubM.kap := Inv.take fun _ _ h hS => Prim.book _ _ (kap_book h) hS
theorem Inv.lin (f : Aff) : Inv I (SubM.lin f) :=
  Inv.change fun F G h hS => by
    unfold Fork.lin at h
    obtain ⟨x, hx, hp⟩ := Option.bind_eq_some_iff.mp h
    exact Prim.push _ _ _ _ hp (Prim.book _ _ (kap_book hx) hS)
theorem Inv.batchBy (d : E) : Inv I (SubM.batchBy d) :=
  Inv.change fun _ _ h hS => Prim.book _ _ (batchBy_book h) hS
theorem Inv.setPlanClaims (n : ℕ) : Inv I (SubM.setPlanClaims n) :=
  Inv.change fun F _ h hS => by
    obtain rfl := Option.some.inj h
    exact Prim.book F _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hS
theorem Inv.owe (s : String) : Inv I (SubM.owe s) :=
  Inv.take fun F _ h hS => by
    obtain rfl := Option.some.inj h
    exact Prim.book F _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hS
theorem Inv.paid (i : ℕ) : Inv I (SubM.paid i) :=
  Inv.change fun F _ h hS => by
    obtain rfl := Option.some.inj h
    exact Prim.book F _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hS
theorem Inv.rootTaken (t w : ℕ) : Inv I (SubM.rootTaken t w) :=
  Inv.change fun F _ h hS => by
    obtain rfl := Option.some.inj h
    exact Prim.rootTaken _ _ _ hS
theorem Inv.pushRuns (k : E) (runs : Array Run2) : Inv I (SubM.change (·.pushRuns k runs)) :=
  Inv.change fun _ _ h hS => Prim.pushRuns _ _ _ _ h hS
theorem Inv.fill (T : Tail2) : Inv I (SubM.change fun F => some (t2FillL F T)) :=
  Inv.change fun F _ h hS => by
    obtain rfl := Option.some.inj h
    exact Prim.fill _ _ hS

theorem Inv.hide (j : ℕ) (y f : E) : Inv I (SubM.hide j y f) :=
  Inv.change fun F G h hS => by
    have h' : F.hideRun j #[y] f = some G := by
      unfold Fork.hideRun
      simp [Fork.hideStep, h]
    exact Prim.hideRun _ _ _ _ _ h' hS

end

/-! ### the tactic -/

open Lean Meta Elab Tactic in
/-- Opens the definition at the head of the routine in a goal `Inv I x`. -/
elab "inv_open" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Fo.Inv 3 do throwError "not a goal Inv I x"
  let x := t.appArg!
  let some n := x.getAppFn.constName? | throwError "no constant at the head"
  unless (`OnBytes).isPrefixOf n do throwError "the head is no routine of the program"
  if [``SubM.change, ``SubM.take, ``SubM.ask].contains n then throwError "a step on the state"
  if ← isMatcher n then throwError "a match"
  let some x' ← unfoldDefinition? x | throwError "no definition to open"
  replaceMainGoal [← g.change (mkApp t.appFn! x'.headBeta)]

open Lean Meta Elab Tactic in
/-- Takes in a bound variable, if the goal begins with one as it is written. -/
elab "inv_intro" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless t.isForall do throwError "no bound variable"
  evalTactic (← `(tactic| intro _))

open Lean Meta Elab Tactic in
/-- Applies a hypothesis. -/
elab "inv_hyp" : tactic => withMainContext do
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

/-- A step on the state that is written out and turns the books alone. -/
macro "inv_change" : tactic => `(tactic| first
  | ((with_reducible refine Inv.change fun F G h hS => ?_)
     have e := Option.some.inj h
     subst e
     exact Prim.book F _ ⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _,
       Eq.refl _, Eq.refl _⟩ hS)
  | ((with_reducible refine Inv.take fun F y h hS => ?_)
     have e := Option.some.inj h
     subst e
     exact Prim.book F _ ⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _,
       Eq.refl _, Eq.refl _⟩ hS))

/-- One step by a rule whose routine is the goal's as it is written. -/
macro "inv_rule" : tactic => `(tactic| with_reducible first
  | exact Inv.pure _ | exact Inv.lift _ | exact Inv.monadLift _ | exact Inv.liftM _
  | exact Inv.ask _ | exact Inv.get
  | exact Inv.must _ | exact Inv.test _ | exact Inv.getO _ | exact Inv.read _
  | exact Inv.readSum | exact Inv.answer _ | exact Inv.answerNotZero _
  | exact Inv.point _ _ | exact Inv.batch _ | exact Inv.batchOpen | exact Inv.batchRows _
  | exact Inv.empty _ | exact Inv.trits _ _ | exact Inv.slot | exact Inv.shown _
  | exact Inv.publicPart _ | exact Inv.claims | exact Inv.allTaken | exact Inv.settle _
  | exact Inv.takeSlots _ | exact Inv.hideRun _ _ _ | exact Inv.hide _ _ _
  | exact Inv.push _ _ | exact Inv.lin _ | exact Inv.kap | exact Inv.batchBy _
  | exact Inv.setPlanClaims _ | exact Inv.owe _ | exact Inv.paid _
  | exact Inv.rootTaken _ _ | exact Inv.pushRuns _ _ | exact Inv.fill _
  | inv_hyp
  | apply Inv.bind | apply Inv.map
  | apply Inv.foldlM | apply Inv.arrayFoldlM | apply Inv.forIn | apply Inv.arrayForIn
  | apply Inv.forM | apply Inv.arrayForM | apply Inv.mapM | apply Inv.arrayMapM)

open Lean Meta Elab Tactic in
/-- Lays a local definition at the head of the routine in, and applies a function that is written
out to its argument. -/
elab "inv_norm" : tactic => do
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
macro "inv_step" : tactic => `(tactic| first
  | inv_intro
  | inv_norm
  | inv_rule
  | inv_change
  | inv_open
  | split)

/-- Proves `Inv I x`. -/
macro "inv" : tactic => `(tactic| repeat' inv_step)

/-! ### the sumcheck's routines -/

section
variable {I : Fork → Prop} [Prim I]

theorem Inv.claimsIn (n : ℕ) : Inv I (SubM.claimsIn n) := by inv
theorem Inv.pscBeginAt (t : E) : Inv I (pscBeginAt t) := by inv
theorem Inv.pscBegin (C : Aff) : Inv I (pscBegin C) := by inv
theorem Inv.pscRound (p : Psc) (w : OnBytes.Psc.Weight) (d : Blk E) : Inv I (pscRound p w d) := by
  inv
theorem Inv.roundIn (f : RoundForm) (p : Psc) (z : E) (d : ℕ) : Inv I (roundIn f p z d) := by
  inv
theorem Inv.pscEnds (p : Psc) (a b : ℕ) : Inv I (pscEnds p a b) := by inv
theorem Inv.pscRow (p : Psc) (S0 : E) (k : Aff) : Inv I (pscRow p S0 k) := by inv


end

end Fo
