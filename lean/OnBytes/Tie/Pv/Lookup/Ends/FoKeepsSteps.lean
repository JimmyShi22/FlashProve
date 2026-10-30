-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean.
The steps on a sub-proof's state that add claims keep what lies under the filled slots; a tactic.

`Slots5 F G`: G has F's slot counter, number of slots, shown values, factors and marks. It holds
of every step that adds a claim or notes something beside the slots (push, kap, lin, batchBy, owe,
paid, rootTaken, setPlanClaims). So each of these routines has `Keeps`. SubM.hide, which fills a
free slot, has it too.
`keeps`: a tactic for a goal `Keeps x`. It goes by the rules of
OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean and of this file and by the hypotheses at hand, takes
branches apart, and opens the definitions below the name OnBytes that it meets. What it builds is a
proof that Lean checks like any other, so it proves no other statement than the one that is
written. A goal that it cannot close stays open, and the proof is then refused. Its steps do not
ask that the goal is a `Keeps x`, so it may close other goals too. Later files add rules to it
(macro_rules on keeps_rule and keeps_open).
Proved by it here: `Keeps` of SubM.claimsIn and of the sumcheck's routines pscBeginAt, pscBegin,
pscRound, roundIn, pscEnds and pscRow (OnBytes/Model/Psc.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeeps

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- The five fields on the slots are the same. -/
def Slots5 (F G : Fork) : Prop :=
  G.next = F.next ∧ G.ns = F.ns ∧ G.vp = F.vp ∧ G.mf = F.mf ∧ G.gotF = F.gotF

theorem Slots5.refl (F : Fork) : Slots5 F F := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Slots5.trans {F G H : Fork} (h1 : Slots5 F G) (h2 : Slots5 G H) : Slots5 F H :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.trans h1.2.2.2.2⟩

theorem Slots5.later {F G : Fork} (h : Slots5 F G) (hS : Sized F) : Later F G ∧ Sized G :=
  later_of_same h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 hS

theorem push_slots5 {F G : Fork} {w : E} {a : Aff} (h : F.push w a = some G) : Slots5 F G := by
  unfold Fork.push at h
  split at h
  · exact absurd h (by simp)
  · simp only at h
    split at h
    · obtain rfl := Option.some.inj h
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact absurd h (by simp)

theorem kapTake_slots5 {F : Fork} {c : ℕ} {y : E × Fork} (h : F.kapTake c = some y) :
    Slots5 F y.2 := by
  unfold Fork.kapTake at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · split at h
      · obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.mp h
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · exact absurd h (by simp)

theorem kap_slots5 {F : Fork} {y : E × Fork} (h : F.kap = some y) : Slots5 F y.2 := by
  unfold Fork.kap at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (kapTake_slots5 hx).trans ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem lin_slots5 {F G : Fork} {f : Aff} (h : F.lin f = some G) : Slots5 F G := by
  unfold Fork.lin at h
  obtain ⟨x, hx, hp⟩ := Option.bind_eq_some_iff.mp h
  exact (kap_slots5 hx).trans (push_slots5 hp)

theorem batchBy_slots5 {F G : Fork} {d : E} (h : F.batchBy d = some G) : Slots5 F G := by
  unfold Fork.batchBy at h
  split at h
  · exact absurd h (by simp)
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Keeps.push (w : E) (a : Aff) : Keeps (SubM.push w a) :=
  Keeps.change fun _ _ h hS => (push_slots5 h).later hS
theorem Keeps.lin (f : Aff) : Keeps (SubM.lin f) :=
  Keeps.change fun _ _ h hS => (lin_slots5 h).later hS
theorem Keeps.kap : Keeps SubM.kap := Keeps.take fun _ _ h hS => (kap_slots5 h).later hS
theorem Keeps.batchBy (d : E) : Keeps (SubM.batchBy d) :=
  Keeps.change fun _ _ h hS => (batchBy_slots5 h).later hS
theorem Keeps.setPlanClaims (n : ℕ) : Keeps (SubM.setPlanClaims n) :=
  Keeps.change fun F _ h hS => by
    obtain rfl := Option.some.inj h
    exact Slots5.later ⟨rfl, rfl, rfl, rfl, rfl⟩ hS
theorem Keeps.owe (s : String) : Keeps (SubM.owe s) :=
  Keeps.take fun F _ h hS => by
    obtain rfl := Option.some.inj h
    exact Slots5.later ⟨rfl, rfl, rfl, rfl, rfl⟩ hS
theorem Keeps.paid (i : ℕ) : Keeps (SubM.paid i) :=
  Keeps.change fun F _ h hS => by
    obtain rfl := Option.some.inj h
    exact Slots5.later ⟨rfl, rfl, rfl, rfl, rfl⟩ hS
theorem Keeps.rootTaken (t w : ℕ) : Keeps (SubM.rootTaken t w) :=
  Keeps.change fun F _ h hS => by
    obtain rfl := Option.some.inj h
    exact Slots5.later ⟨rfl, rfl, rfl, rfl, rfl⟩ hS

theorem Keeps.hide (j : ℕ) (y f : E) : Keeps (SubM.hide j y f) :=
  Keeps.change fun F G h hS => by
    have h' : F.hideRun j #[y] f = some G := by
      unfold Fork.hideRun
      simp [Fork.hideStep, h]
    exact ⟨hideRun_later hS h', (hideRun_ok _ _ _ _ _ hS h').2.1⟩

/-! ### the tactic -/

open Lean Meta Elab Tactic in
/-- Opens the definition at the head of the routine in a goal `Keeps x`. -/
elab "keeps_open" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Fo.Keeps 2 do throwError "not a goal Keeps x"
  let x := t.appArg!
  let some n := x.getAppFn.constName? | throwError "no constant at the head"
  unless (`OnBytes).isPrefixOf n do throwError "the head is no routine of the program"
  if [``SubM.change, ``SubM.take, ``SubM.ask].contains n then throwError "a step on the state"
  if ← isMatcher n then throwError "a match"
  let some x' ← unfoldDefinition? x | throwError "no definition to open"
  replaceMainGoal [← g.change (mkApp t.appFn! x'.headBeta)]

open Lean Meta Elab Tactic in
/-- Takes in a bound variable, if the goal begins with one as it is written. -/
elab "keeps_intro" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless t.isForall do throwError "no bound variable"
  evalTactic (← `(tactic| intro _))

open Lean Meta Elab Tactic in
/-- Applies a hypothesis. -/
elab "keeps_hyp" : tactic => withMainContext do
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

/-- A step on the state that is written out and leaves the five fields on the slots alone. -/
macro "keeps_change" : tactic => `(tactic| first
  | ((with_reducible refine Keeps.change fun F G h hS => ?_)
     have e := Option.some.inj h
     subst e
     exact Slots5.later ⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩ hS)
  | ((with_reducible refine Keeps.take fun F y h hS => ?_)
     have e := Option.some.inj h
     subst e
     exact Slots5.later ⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩ hS))

/-- One step by a rule whose routine is the goal's as it is written. -/
macro "keeps_rule" : tactic => `(tactic| with_reducible first
  | exact Keeps.pure _ | exact Keeps.lift _ | exact Keeps.monadLift _ | exact Keeps.liftM _
  | exact Keeps.ask _ | exact Keeps.get
  | exact Keeps.must _ | exact Keeps.test _ | exact Keeps.getO _ | exact Keeps.read _
  | exact Keeps.readSum | exact Keeps.answer _ | exact Keeps.answerNotZero _
  | exact Keeps.point _ _ | exact Keeps.batch _ | exact Keeps.batchOpen | exact Keeps.batchRows _
  | exact Keeps.empty _ | exact Keeps.trits _ _ | exact Keeps.slot | exact Keeps.shown _
  | exact Keeps.publicPart _ | exact Keeps.claims | exact Keeps.allTaken | exact Keeps.settle _
  | exact Keeps.takeSlots _ | exact Keeps.hideRun _ _ _ | exact Keeps.hide _ _ _
  | exact Keeps.push _ _ | exact Keeps.lin _ | exact Keeps.kap | exact Keeps.batchBy _
  | exact Keeps.setPlanClaims _ | exact Keeps.owe _ | exact Keeps.paid _
  | exact Keeps.rootTaken _ _
  | keeps_hyp
  | apply Keeps.bind | apply Keeps.map
  | apply Keeps.foldlM | apply Keeps.arrayFoldlM | apply Keeps.forIn | apply Keeps.arrayForIn
  | apply Keeps.forM | apply Keeps.arrayForM | apply Keeps.mapM | apply Keeps.arrayMapM)

open Lean Meta Elab Tactic in
/-- Puts the value of a local definition (let) at the head of the routine in its place, or applies
a function that is written out to its argument. -/
elab "keeps_norm" : tactic => do
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
macro "keeps_step" : tactic => `(tactic| first
  | keeps_intro
  | keeps_norm
  | keeps_rule
  | keeps_change
  | keeps_open
  | split)

/-- For a goal `Keeps x`: takes steps until none applies. What it cannot close stays open. -/
macro "keeps" : tactic => `(tactic| repeat' keeps_step)

/-! ### the sumcheck's routines -/

theorem Keeps.claimsIn (n : ℕ) : Keeps (SubM.claimsIn n) := by keeps
theorem Keeps.pscBeginAt (t : E) : Keeps (pscBeginAt t) := by keeps
theorem Keeps.pscBegin (C : Aff) : Keeps (pscBegin C) := by keeps
theorem Keeps.pscRound (p : Psc) (w : OnBytes.Psc.Weight) (d : Blk E) : Keeps (pscRound p w d) := by
  keeps
theorem Keeps.roundIn (f : RoundForm) (p : Psc) (z : E) (d : ℕ) : Keeps (roundIn f p z d) := by
  keeps
theorem Keeps.pscEnds (p : Psc) (a b : ℕ) : Keeps (pscEnds p a b) := by keeps
theorem Keeps.pscRow (p : Psc) (S0 : E) (k : Aff) : Keeps (pscRow p S0 k) := by keeps

end Fo
