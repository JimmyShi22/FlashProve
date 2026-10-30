-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoFixedU.lean.
Routines whose added claims are fixed before the state AND read one array alone.

`FixedU t0 x`: the clauses of Fo.Fixed x (OnBytes/Tie/Pv/Lookup/Ends/FoFixed.lean): there are a
value v and a list L of claims, functions of the arrays' numbers of columns alone and chosen before
the state, such that every run
of x that returns, from a state with a coefficient for each slot, returns v, adds L and keeps the
numbers of columns; AND OF THE SAME v AND L: the value holds only forms whose entries lie in array
t0 (`good`, OnBytes/Tie/Pv/Lookup/Ends/FoGood.lean), and every member of L has its form's entries
and its runs in array t0.
`FixedU.fixed`: it gives Fo.Fixed. The rules are Fixed's, each with what it needs on goodness: a
routine behind a bind may use that the value bound is good; a loop, that its state and its list are.
`fixedu`: a tactic that proves FixedU of a routine by these rules, opening the definitions that it
meets; it leaves the goals on goodness that it cannot close.

Limits: all those of Fo.Fixed (the head of OnBytes/Tie/Pv/Lookup/Ends/FoFixed.lean) hold of FixedU
too. v and L are chosen behind the routine's own arguments and can hang on them. The statements
speak of runs that return. If, for given arguments and numbers of columns, a run returned at one
theta alone, a function of the numbers of columns could still fit that theta. The U in the name is
the array, not "unique": nothing here says that the members' values are unique, and no identity of
polynomials in theta is drawn. The clause on the value is empty for a type without an instance of
HasGood of its own. Beside FoFixedULook.lean, FoFixedUAtt.lean, FoFixedUHead.lean (this folder) and
their test, no file of this library uses FixedU yet.
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a run returns, or which the claims are.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoGood

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- Fixed, with a value and claims that read array t0 alone. -/
def FixedU {α : Type} [HasGood α] (t0 : ℕ) (x : SubM α) : Prop :=
  ∃ (v : (ℕ → ℕ) → Option α) (L : (ℕ → ℕ) → List Cl),
    (∀ (F : Fork) (c : Ctx) (a : α) (G : Fork) (c' : Ctx), x F c = .ok ((a, G), c') →
      F.LS.size = F.ns → v (colsOf F) = some a ∧ Added F G (L (colsOf F)) ∧ colsOf G = colsOf F) ∧
    (∀ k a, v k = some a → good t0 a) ∧ ∀ k, ∀ cl ∈ L k, GoodCl t0 cl

section
variable {α β σ : Type} [HasGood α] [HasGood β] [HasGood σ] {t0 : ℕ}

theorem FixedU.fixed {x : SubM α} (h : FixedU t0 x) : Fixed x := by
  obtain ⟨v, L, hv, -, -⟩ := h
  exact ⟨v, L, hv⟩

/-- From Fixed with no claim and a value that is good whatever it is. -/
theorem FixedU.ofQuiet {x : SubM α} (v : (ℕ → ℕ) → Option α)
    (h : ∀ F c a G c', x F c = .ok ((a, G), c') → F.LS.size = F.ns →
      v (colsOf F) = some a ∧ Added F G [] ∧ colsOf G = colsOf F)
    (hg : ∀ k a, v k = some a → good t0 a) : FixedU t0 x :=
  ⟨v, fun _ => [], h, hg, fun _ _ hc => absurd hc List.not_mem_nil⟩

theorem FixedU.pure (a : α) [h : Good t0 a] : FixedU t0 (Pure.pure a : SubM α) :=
  FixedU.ofQuiet (fun _ => some a) (fun F c b G c' hr hs => by
    have e := (pure_ok _ _ _ _).1 hr
    have e1 : b = a := congrArg (fun x : (α × Fork) × Ctx => x.1.1) e
    have e2 : G = F := congrArg (fun x : (α × Fork) × Ctx => x.1.2) e
    rw [e1, e2]
    exact ⟨rfl, Added.refl hs, rfl⟩) fun _ b hb => by
      rw [← Option.some.inj hb]
      exact h.out

theorem FixedU.bind {x : SubM α} {f : α → SubM β} (hx : FixedU t0 x)
    (hf' : ∀ a, Good t0 a → FixedU t0 (f a)) : FixedU t0 (x >>= f) := by
  classical
  have hf : ∀ a, good t0 a → FixedU t0 (f a) := fun a h => hf' a ⟨h⟩
  obtain ⟨v, L, hv, gv, gL⟩ := hx
  let w : α → (ℕ → ℕ) → Option β := fun a =>
    if h : good t0 a then (hf a h).choose else fun _ => none
  let M : α → (ℕ → ℕ) → List Cl := fun a =>
    if h : good t0 a then (hf a h).choose_spec.choose else fun _ => []
  have hw : ∀ a (h : good t0 a),
      (∀ (F : Fork) (c : Ctx) (b : β) (G : Fork) (c' : Ctx), f a F c = .ok ((b, G), c') →
        F.LS.size = F.ns → w a (colsOf F) = some b ∧ Added F G (M a (colsOf F)) ∧
          colsOf G = colsOf F) ∧
      (∀ k b, w a k = some b → good t0 b) ∧ ∀ k, ∀ cl ∈ M a k, GoodCl t0 cl := by
    intro a h
    have e1 : w a = (hf a h).choose := dif_pos h
    have e2 : M a = (hf a h).choose_spec.choose := dif_pos h
    rw [e1, e2]
    exact (hf a h).choose_spec.choose_spec
  refine ⟨fun k => (v k).bind fun a => w a k,
    fun k => L k ++ match v k with
      | some a => M a k
      | none => [], fun F c b G c' hr hs => ?_, fun k b hb => ?_, fun k cl hc => ?_⟩
  · obtain ⟨a, F1, c1, h1, h2⟩ := (bind_ok _ _ _ _ _).1 hr
    obtain ⟨e1, a1, k1⟩ := hv _ _ _ _ _ h1 hs
    obtain ⟨e2, a2, k2⟩ := (hw a (gv _ _ e1)).1 _ _ _ _ _ h2 a1.sized
    rw [k1] at e2 a2 k2
    refine ⟨?_, ?_, k2⟩
    · show (v (colsOf F)).bind _ = _
      rw [e1]
      exact e2
    · show Added F G (L (colsOf F) ++ match v (colsOf F) with
        | some a => M a (colsOf F)
        | none => [])
      rw [e1]
      exact a1.trans a2
  · obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.1 hb
    exact (hw a (gv _ _ ha)).2.1 k b hb
  · rcases List.mem_append.1 hc with hc | hc
    · exact gL k cl hc
    · cases ha : v k with
      | none =>
        rw [ha] at hc
        exact absurd hc List.not_mem_nil
      | some a =>
        rw [ha] at hc
        exact (hw a (gv _ _ ha)).2.2 k cl hc

theorem FixedU.map {x : SubM α} (f : α → β) (hx : FixedU t0 x)
    (hf : ∀ a, Good t0 a → Good t0 (f a)) : FixedU t0 (f <$> x) := by
  rw [← bind_pure_comp]
  exact hx.bind fun a ha => @FixedU.pure _ _ _ _ (hf a ha)

theorem FixedU.never {x : SubM α} (h : ∀ F c r, x F c ≠ .ok r) : FixedU t0 x :=
  FixedU.ofQuiet (fun _ => none) (fun F c _ _ _ hr _ => absurd hr (h F c _))
    fun _ _ h => by cases h

theorem FixedU.refuse (name : String) : FixedU t0 (liftM (refuse name : Blk α) : SubM α) :=
  FixedU.never fun F c r hr => by
    obtain ⟨_, _, h1, _⟩ := (lift_ok _ _ _ _).1 hr
    exact absurd h1 (by simp [Model.refuse, Blk.fail])

/-- From Fixed of a routine that adds nothing, if every value of the type is good. -/
theorem FixedU.unit [Subsingleton α] [hu : Unasked α] {x : SubM α}
    (h : ∀ F c a G c', x F c = .ok ((a, G), c') → F.LS.size = F.ns →
      Added F G [] ∧ colsOf G = colsOf F) : FixedU t0 x := by
  classical
  refine FixedU.ofQuiet (fun _ => if hn : Nonempty α then some hn.some else none)
    (fun F c a G c' hr hs => ⟨?_, h F c a G c' hr hs⟩) fun _ a _ => hu.all t0 a
  rw [dif_pos ⟨a⟩]
  exact congrArg some (Subsingleton.elim _ _)

theorem FixedU.liftU [Subsingleton α] [Unasked α] (b : Blk α) :
    FixedU t0 (StateT.lift b : SubM α) :=
  FixedU.unit fun F c a G c' hr hs => by
    obtain ⟨_, _, _, e⟩ := (lift_ok _ _ _ _).1 hr
    have e2 : G = F := congrArg (fun x : (α × Fork) × Ctx => x.1.2) e
    rw [e2]
    exact ⟨Added.refl hs, rfl⟩

theorem FixedU.monadLiftU [Subsingleton α] [Unasked α] (b : Blk α) :
    FixedU t0 (MonadLiftT.monadLift b : SubM α) := FixedU.liftU b

theorem FixedU.liftMU [Subsingleton α] [Unasked α] (b : Blk α) :
    FixedU t0 (liftM b : SubM α) := FixedU.liftU b

theorem FixedU.must (b : Bool) : FixedU t0 (SubM.must b) := FixedU.liftU _

theorem FixedU.getO (x : Option α) [hx : Good t0 x] : FixedU t0 (SubM.get x) :=
  FixedU.ofQuiet (fun _ => x) (fun F c a G c' hr hs => by
    obtain ⟨a', h1, e⟩ := (get_ok _ _ _ _).1 hr
    have e1 : a = a' := congrArg (fun x : (α × Fork) × Ctx => x.1.1) e
    have e2 : G = F := congrArg (fun x : (α × Fork) × Ctx => x.1.2) e
    rw [e1, e2]
    exact ⟨h1, Added.refl hs, rfl⟩) fun _ a ha => hx.out a ha

theorem FixedU.uEnt (x : ℕ) : FixedU t0 (uEnt t0 x) :=
  FixedU.ofQuiet (fun k => some (u3Form t0 (k t0) x)) (fun F c a G c' hr hs => by
    have e := uEnt_ok t0 x F c _ hr
    have e1 : a = _ := congrArg (fun x : (Aff × Fork) × Ctx => x.1.1) e
    have e2 : G = F := congrArg (fun x : (Aff × Fork) × Ctx => x.1.2) e
    rw [e1, e2]
    exact ⟨rfl, Added.refl hs, rfl⟩) fun k a ha => by
      rw [← Option.some.inj ha]
      exact InU.u3Form t0 _ _

theorem FixedU.lin (f : Aff) [hf : Good t0 f] : FixedU t0 (SubM.lin f) :=
  ⟨fun _ => some (), fun _ => [(f, #[])], fun F c a G c' hr hs => by
    obtain ⟨h1, _⟩ := (SubM.lin_run f F G c c').1 hr
    exact ⟨rfl, added_lin hs h1, cols_of_frame
      (Fork.lin_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ F G f hs h1).2.2.2.2.2⟩,
    fun _ _ _ => trivial, fun _ cl hc => by
      rw [List.mem_singleton.1 hc]
      exact ⟨hf.out, fun r hr => by simp at hr⟩⟩

theorem FixedU.paid (i : ℕ) : FixedU t0 (SubM.paid i) :=
  FixedU.unit fun F c a G c' hr hs => by
    unfold SubM.paid at hr
    obtain ⟨G', h1, e⟩ := (change_ok _ _ _ _).1 hr
    have e2 : G = G' := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e
    rw [e2, ← Option.some.inj h1]
    exact ⟨added_paid hs i, rfl⟩

theorem FixedU.ite {p : Prop} [Decidable p] {x y : SubM α} (hx : FixedU t0 x)
    (hy : FixedU t0 y) : FixedU t0 (if p then x else y) := by
  split
  · exact hx
  · exact hy

theorem FixedU.foldlM {f : σ → α → SubM σ}
    (hf : ∀ s a, Good t0 s → Good t0 a → FixedU t0 (f s a)) :
    ∀ (l : List α) (s : σ), Good t0 l → Good t0 s → FixedU t0 (l.foldlM f s)
  | [], s, _, _ => FixedU.pure s
  | a :: l, s, hl, hs => by
    rw [List.foldlM_cons]
    exact (hf s a hs ⟨hl.out a List.mem_cons_self⟩).bind fun s' hs' =>
      FixedU.foldlM hf l s' ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩ hs'

theorem FixedU.arrayFoldlM {f : σ → α → SubM σ}
    (hf : ∀ s a, Good t0 s → Good t0 a → FixedU t0 (f s a)) (l : Array α) (s : σ)
    (hl : Good t0 l) (hs : Good t0 s) : FixedU t0 (l.foldlM f s) := by
  rw [← Array.foldlM_toList]
  exact FixedU.foldlM hf _ s ⟨hl.out⟩ hs

theorem FixedU.forIn {f : α → σ → SubM (ForInStep σ)}
    (hf : ∀ a s, Good t0 a → Good t0 s → FixedU t0 (f a s)) :
    ∀ (l : List α) (s : σ), Good t0 l → Good t0 s → FixedU t0 (ForIn.forIn l s f)
  | [], s, _, _ => by
    rw [List.forIn_nil]
    exact FixedU.pure s
  | a :: l, s, hl, hs => by
    rw [List.forIn_cons]
    refine (hf a s ⟨hl.out a List.mem_cons_self⟩ hs).bind fun r hr => ?_
    cases r with
    | done b =>
      have : Good t0 b := ⟨hr.out⟩
      exact FixedU.pure b
    | yield b =>
      exact FixedU.forIn hf l b ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩ ⟨hr.out⟩

theorem FixedU.arrayForIn {f : α → σ → SubM (ForInStep σ)}
    (hf : ∀ a s, Good t0 a → Good t0 s → FixedU t0 (f a s)) (l : Array α) (s : σ)
    (hl : Good t0 l) (hs : Good t0 s) : FixedU t0 (ForIn.forIn l s f) := by
  rw [← Array.forIn_toList]
  exact FixedU.forIn hf _ s ⟨hl.out⟩ hs

theorem FixedU.rangeForIn {f : ℕ → σ → SubM (ForInStep σ)}
    (hf : ∀ a s, Good t0 a → Good t0 s → FixedU t0 (f a s)) (r : Std.Legacy.Range) (s : σ)
    (hs : Good t0 s) : FixedU t0 (ForIn.forIn r s f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact FixedU.forIn hf _ s inferInstance hs

theorem FixedU.forM {f : α → SubM PUnit} (hf : ∀ a, Good t0 a → FixedU t0 (f a)) :
    ∀ l : List α, Good t0 l → FixedU t0 (l.forM f)
  | [], _ => FixedU.pure _
  | a :: l, hl => by
    show FixedU t0 (f a >>= fun _ => l.forM f)
    exact (hf a ⟨hl.out a List.mem_cons_self⟩).bind fun _ _ =>
      FixedU.forM hf l ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩

theorem FixedU.arrayForM {f : α → SubM PUnit} (hf : ∀ a, Good t0 a → FixedU t0 (f a))
    (l : Array α) (hl : Good t0 l) : FixedU t0 (l.forM f) := by
  unfold Array.forM
  exact FixedU.arrayFoldlM (fun _ a _ ha => hf a ha) l _ hl inferInstance

end

/-! ### the tactic -/

open Lean Meta Elab Tactic in
/-- Opens the definition at the head of the routine in a goal FixedU t0 x, or of the value in a goal
Good t0 a. -/
elab "fixedu_open" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOf ``Fo.FixedU || t.isAppOf ``Fo.Good do throwError "no goal of the two kinds"
  let x := t.appArg!
  let some n := x.getAppFn.constName? | throwError "no constant at the head"
  unless (`OnBytes).isPrefixOf n do throwError "the head is no definition of the program"
  if [``SubM.change, ``SubM.take, ``SubM.ask, ``SubM.kap, ``SubM.push, ``Aff.addMul, ``Aff.scale,
      ``Aff.slot, ``Aff.ofConst, ``Aff.ent].contains n then
    throwError "a step on the state, or an operation on forms"
  if ← isMatcher n then throwError "a match"
  if (← getEnv).isProjectionFn n then throwError "a field"
  let some x' ← unfoldDefinition? x | throwError "no definition to open"
  replaceMainGoal [← g.change (mkApp t.appFn! x'.headBeta)]

open Lean Meta Elab Tactic in
/-- Takes in a bound variable, if the goal begins with one as it is written. -/
elab "fixedu_intro" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless t.isForall do throwError "no bound variable"
  evalTactic (← `(tactic| intro _))

open Lean Meta Elab Tactic in
/-- Closes a goal Good t0 a by instance search. -/
elab "fixedu_good" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless t.isAppOf ``Fo.Good do throwError "no goal Good t0 a"
  evalTactic (← `(tactic| exact inferInstance))

open Lean Meta Elab Tactic in
/-- Applies a hypothesis. -/
elab "fixedu_hyp" : tactic => withMainContext do
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

/-- One step by a rule whose routine is the goal's as it is written. -/
macro "fixedu_rule" : tactic => `(tactic| with_reducible first
  | exact FixedU.refuse _ | exact FixedU.liftU _ | exact FixedU.monadLiftU _
  | exact FixedU.liftMU _ | exact FixedU.must _ | exact FixedU.uEnt _ | exact FixedU.paid _
  | refine @FixedU.pure _ _ _ _ ?_ | refine @FixedU.getO _ _ _ _ ?_
  | refine @FixedU.lin _ _ ?_
  | fixedu_hyp
  | refine FixedU.bind ?_ ?_
  | refine FixedU.foldlM ?_ _ _ ?_ ?_ | refine FixedU.arrayFoldlM ?_ _ _ ?_ ?_
  | refine FixedU.forIn ?_ _ _ ?_ ?_ | refine FixedU.arrayForIn ?_ _ _ ?_ ?_
  | refine FixedU.rangeForIn ?_ _ _ ?_
  | refine FixedU.forM ?_ _ ?_ | refine FixedU.arrayForM ?_ _ ?_
  | refine good_foldl _ ?_ _ _ ?_ ?_ | refine good_foldlArr _ ?_ _ _ ?_ ?_
  | refine @good_add _ _ _ ?_ ?_ | refine @good_sub _ _ _ ?_ ?_
  | refine @good_addMul _ _ _ _ ?_ ?_ | refine @good_scale _ _ _ ?_
  | refine @good_ite _ _ _ _ _ _ _ ?_ ?_)

open Lean Meta Elab Tactic in
/-- Lays a local definition at the head of the routine or value in, and applies a function that is
written out to its argument. -/
elab "fixedu_norm" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOf ``Fo.FixedU || t.isAppOf ``Fo.Good do throwError "no goal of the two kinds"
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
macro "fixedu_step" : tactic => `(tactic| first
  | fixedu_intro
  | fixedu_norm
  | fixedu_good
  | fixedu_rule
  | fixedu_open
  | split)

/-- Proves FixedU t0 x; leaves the goals on goodness that it cannot close. -/
macro "fixedu" : tactic => `(tactic| repeat' fixedu_step)

end Fo
