-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoFixed.lean.
Routines of a sub-proof whose returned value and whose added claims are fixed by the arrays' numbers
of columns.

A statement "the run adds SOME list of claims" pins no claim: Fo.Added is an identity of values at
the state's one element theta, and a form may carry any element of the field as a coefficient,
powers of theta among them, so one member of a free list can swallow another. Fixed x says more:
there are a value v and a list L of claims, both functions of the arrays' numbers of columns ALONE
and chosen BEFORE the state, such that every run of x that returns, from a state F with one
coefficient for each slot, returns v (colsOf F), adds L (colsOf F), and keeps the numbers of
columns. So neither can hang on the state's theta, on its coefficients, on its number of claims, or
on what lies under its slots.

States:
  cols_of_frame: states whose arrays agree but for the weights' values have the same numbers of
    columns.
  Fixed; Fixed.pure, .bind, .map, .never (a routine that never returns), .refuse, .unit (a routine
    that returns nothing, adds nothing and keeps the arrays), .liftU, .monadLiftU, .liftMU (a lifted
    routine of the channel that returns nothing), .getO, .must, .uEnt (the one routine that reads
    the state: a number of columns), .lin, .t2Lin, .paid, .hideRun, .ite, .foldlM, .arrayFoldlM,
    .forIn, .arrayForIn, .rangeForIn, .forM, .arrayForM, .mapM.
  fixed: a tactic that proves Fixed of a routine by these rules, opening the definitions that it
    meets.
Limit: v and L are chosen behind the routine's own arguments, so they can hang on these: the members
of L are forms and runs whose coefficients come from the arguments. If an argument (a record of what
was heard, a plan, the tail's record) itself holds a power of theta, Fixed says nothing against it:
that it holds nothing that was drawn with or after theta is the caller's to say. Whether a run
returns can hang on the state. The statements speak of runs that return. If, for given arguments and
numbers of columns, a run returned at one theta alone, a function of the numbers of columns could
still fit that theta: that the run from a state with another theta returns too, with the same value
and the same list, is not shown. A count at totals does not need it: for every theta at which the
run returns, the total has grown by the sum of theta^i times the value of member i of ONE list, the
same for all such runs with these arguments from states with these numbers of columns. No statement
here draws a consequence from that: neither that the members' values are thereby unique, nor an
identity of polynomials in theta.
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a run returns, or which the claims are.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAddsTail
import OnBytes.Tie.Pv.Lookup.Port.FoReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem cols_of_frame {F G : Fork} (h : treesFrame G.trees = treesFrame F.trees) :
    colsOf G = colsOf F := by
  funext t
  have e := congrArg (fun a => (a[t]?).map fun p => p.1.K) h
  simp only [treesFrame, Array.getElem?_map, Option.map_map] at e
  unfold colsOf
  exact congrArg (fun o => o.getD 0) e

theorem cols_of_trees {F G : Fork} (h : G.trees = F.trees) : colsOf G = colsOf F := by
  funext t
  unfold colsOf
  rw [h]

/-- Value and claims are functions of the arrays' numbers of columns, chosen before the state. -/
def Fixed {α : Type} (x : SubM α) : Prop :=
  ∃ (v : (ℕ → ℕ) → Option α) (L : (ℕ → ℕ) → List Cl),
    ∀ (F : Fork) (c : Ctx) (a : α) (G : Fork) (c' : Ctx), x F c = .ok ((a, G), c') →
      F.LS.size = F.ns → v (colsOf F) = some a ∧ Added F G (L (colsOf F)) ∧ colsOf G = colsOf F

section
variable {α β σ : Type}

theorem Fixed.pure (a : α) : Fixed (Pure.pure a : SubM α) :=
  ⟨fun _ => some a, fun _ => [], fun F c b G c' hr hs => by
    have e := (pure_ok _ _ _ _).1 hr
    have e1 : b = a := congrArg (fun x : (α × Fork) × Ctx => x.1.1) e
    have e2 : G = F := congrArg (fun x : (α × Fork) × Ctx => x.1.2) e
    rw [e1, e2]
    exact ⟨rfl, Added.refl hs, rfl⟩⟩

theorem Fixed.bind {x : SubM α} {f : α → SubM β} (hx : Fixed x) (hf : ∀ a, Fixed (f a)) :
    Fixed (x >>= f) := by
  obtain ⟨v, L, hv⟩ := hx
  choose w M hw using hf
  refine ⟨fun k => (v k).bind fun a => w a k,
    fun k => L k ++ match v k with
      | some a => M a k
      | none => [], fun F c b G c' hr hs => ?_⟩
  obtain ⟨a, F1, c1, h1, h2⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨e1, a1, k1⟩ := hv _ _ _ _ _ h1 hs
  obtain ⟨e2, a2, k2⟩ := hw a _ _ _ _ _ h2 a1.sized
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

theorem Fixed.map {x : SubM α} (f : α → β) (hx : Fixed x) : Fixed (f <$> x) := by
  rw [← bind_pure_comp]
  exact hx.bind fun _ => Fixed.pure _

/-- A routine that never returns. -/
theorem Fixed.never {x : SubM α} (h : ∀ F c r, x F c ≠ .ok r) : Fixed x :=
  ⟨fun _ => none, fun _ => [], fun F c _ _ _ hr _ => absurd hr (h F c _)⟩

theorem Fixed.refuse (name : String) : Fixed (liftM (refuse name : Blk α) : SubM α) :=
  Fixed.never fun F c r hr => by
    obtain ⟨_, _, h1, _⟩ := (lift_ok _ _ _ _).1 hr
    exact absurd h1 (by simp [Model.refuse, Blk.fail])

/-- A routine that returns nothing, adds nothing and keeps the arrays. -/
theorem Fixed.unit [Subsingleton α] {x : SubM α}
    (h : ∀ F c a G c', x F c = .ok ((a, G), c') → F.LS.size = F.ns →
      Added F G [] ∧ colsOf G = colsOf F) : Fixed x := by
  classical
  refine ⟨fun _ => if hn : Nonempty α then some hn.some else none, fun _ => [],
    fun F c a G c' hr hs => ⟨?_, h F c a G c' hr hs⟩⟩
  rw [dif_pos ⟨a⟩]
  exact congrArg some (Subsingleton.elim _ _)

theorem Fixed.liftU [Subsingleton α] (b : Blk α) : Fixed (StateT.lift b : SubM α) :=
  Fixed.unit fun F c a G c' hr hs => by
    obtain ⟨_, _, _, e⟩ := (lift_ok _ _ _ _).1 hr
    have e2 : G = F := congrArg (fun x : (α × Fork) × Ctx => x.1.2) e
    rw [e2]
    exact ⟨Added.refl hs, rfl⟩

theorem Fixed.monadLiftU [Subsingleton α] (b : Blk α) :
    Fixed (MonadLiftT.monadLift b : SubM α) := Fixed.liftU b

theorem Fixed.liftMU [Subsingleton α] (b : Blk α) : Fixed (liftM b : SubM α) := Fixed.liftU b

theorem Fixed.must (b : Bool) : Fixed (SubM.must b) := Fixed.liftU _

theorem Fixed.getO (x : Option α) : Fixed (SubM.get x) :=
  ⟨fun _ => x, fun _ => [], fun F c a G c' hr hs => by
    obtain ⟨a', h1, e⟩ := (get_ok _ _ _ _).1 hr
    have e1 : a = a' := congrArg (fun x : (α × Fork) × Ctx => x.1.1) e
    have e2 : G = F := congrArg (fun x : (α × Fork) × Ctx => x.1.2) e
    rw [e1, e2]
    exact ⟨h1, Added.refl hs, rfl⟩⟩

/-- The one routine that reads the state: a number of columns. -/
theorem Fixed.uEnt (t x : ℕ) : Fixed (uEnt t x) :=
  ⟨fun k => some (u3Form t (k t) x), fun _ => [], fun F c a G c' hr hs => by
    have e := uEnt_ok t x F c _ hr
    have e1 : a = _ := congrArg (fun x : (Aff × Fork) × Ctx => x.1.1) e
    have e2 : G = F := congrArg (fun x : (Aff × Fork) × Ctx => x.1.2) e
    rw [e1, e2]
    exact ⟨rfl, Added.refl hs, rfl⟩⟩

theorem Fixed.lin (f : Aff) : Fixed (SubM.lin f) :=
  ⟨fun _ => some (), fun _ => [(f, #[])], fun F c a G c' hr hs => by
    obtain ⟨h1, _⟩ := (SubM.lin_run f F G c c').1 hr
    exact ⟨rfl, added_lin hs h1, cols_of_frame
      (Fork.lin_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ F G f hs h1).2.2.2.2.2⟩⟩

theorem Fixed.t2Lin (a : Aff) (runs : Array Run2) : Fixed (t2Lin a runs) :=
  ⟨fun _ => some (), fun _ => [(a, runs)], fun F c _ G c' hr hs =>
    ⟨rfl, added_t2Lin hr hs, cols_of_frame
      (t2Lin_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ a runs F G c c' hs hr).2.2.2.2.2.2⟩⟩

theorem Fixed.paid (i : ℕ) : Fixed (SubM.paid i) :=
  Fixed.unit fun F c a G c' hr hs => by
    unfold SubM.paid at hr
    obtain ⟨G', h1, e⟩ := (change_ok _ _ _ _).1 hr
    have e2 : G = G' := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e
    rw [e2, ← Option.some.inj h1]
    exact ⟨added_paid hs i, rfl⟩

theorem Fixed.hideRun (first : ℕ) (v : Array E) (f : E) :
    Fixed (SubM.change (·.hideRun first v f)) :=
  Fixed.unit fun F c a G c' hr hs => by
    obtain ⟨G', h1, e⟩ := (change_ok _ _ _ _).1 hr
    have e2 : G = G' := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e
    rw [e2]
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hideRun_fields h1
    exact ⟨added_same hs a1 a2 a3 a4 a5 a6, cols_of_trees a1⟩

theorem Fixed.ite {p : Prop} [Decidable p] {x y : SubM α} (hx : Fixed x) (hy : Fixed y) :
    Fixed (if p then x else y) := by
  split
  · exact hx
  · exact hy

theorem Fixed.foldlM {f : σ → α → SubM σ} (hf : ∀ s a, Fixed (f s a)) :
    ∀ (l : List α) (s : σ), Fixed (l.foldlM f s)
  | [], s => Fixed.pure s
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact (hf s a).bind fun s' => Fixed.foldlM hf l s'

theorem Fixed.arrayFoldlM {f : σ → α → SubM σ} (hf : ∀ s a, Fixed (f s a)) (l : Array α) (s : σ) :
    Fixed (l.foldlM f s) := by
  rw [← Array.foldlM_toList]
  exact Fixed.foldlM hf _ s

theorem Fixed.forIn {f : α → σ → SubM (ForInStep σ)} (hf : ∀ a s, Fixed (f a s)) :
    ∀ (l : List α) (s : σ), Fixed (ForIn.forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    exact Fixed.pure s
  | a :: l, s => by
    rw [List.forIn_cons]
    refine (hf a s).bind fun r => ?_
    cases r with
    | done b => exact Fixed.pure b
    | yield b => exact Fixed.forIn hf l b

theorem Fixed.arrayForIn {f : α → σ → SubM (ForInStep σ)} (hf : ∀ a s, Fixed (f a s))
    (l : Array α) (s : σ) : Fixed (ForIn.forIn l s f) := by
  rw [← Array.forIn_toList]
  exact Fixed.forIn hf _ s

theorem Fixed.rangeForIn {f : ℕ → σ → SubM (ForInStep σ)} (hf : ∀ a s, Fixed (f a s))
    (r : Std.Legacy.Range) (s : σ) : Fixed (ForIn.forIn r s f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact Fixed.forIn hf _ s

theorem Fixed.forM {f : α → SubM PUnit} (hf : ∀ a, Fixed (f a)) : ∀ l : List α, Fixed (l.forM f)
  | [] => Fixed.pure _
  | a :: l => by
    show Fixed (f a >>= fun _ => l.forM f)
    exact (hf a).bind fun _ => Fixed.forM hf l

theorem Fixed.arrayForM {f : α → SubM PUnit} (hf : ∀ a, Fixed (f a)) (l : Array α) :
    Fixed (l.forM f) := by
  unfold Array.forM
  exact Fixed.arrayFoldlM (fun _ a => hf a) l _

theorem Fixed.mapM {f : α → SubM β} (hf : ∀ a, Fixed (f a)) : ∀ l : List α, Fixed (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    exact Fixed.pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact (hf a).bind fun _ => (Fixed.mapM hf l).bind fun _ => Fixed.pure _

end

/-! ### the tactic -/

open Lean Meta Elab Tactic in
/-- Opens the definition at the head of the routine in a goal Fixed x. -/
elab "fixed_open" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Fo.Fixed 2 do throwError "not a goal Fixed x"
  let x := t.appArg!
  let some n := x.getAppFn.constName? | throwError "no constant at the head"
  unless (`OnBytes).isPrefixOf n do throwError "the head is no routine of the program"
  if [``SubM.change, ``SubM.take, ``SubM.ask, ``SubM.kap, ``SubM.push].contains n then
    throwError "a step on the state"
  if ← isMatcher n then throwError "a match"
  let some x' ← unfoldDefinition? x | throwError "no definition to open"
  replaceMainGoal [← g.change (mkApp t.appFn! x'.headBeta)]

open Lean Meta Elab Tactic in
/-- Takes in a bound variable, if the goal begins with one as it is written. -/
elab "fixed_intro" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless t.isForall do throwError "no bound variable"
  evalTactic (← `(tactic| intro _))

open Lean Meta Elab Tactic in
/-- Applies a hypothesis. -/
elab "fixed_hyp" : tactic => withMainContext do
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
macro "fixed_rule" : tactic => `(tactic| with_reducible first
  | exact Fixed.pure _ | exact Fixed.refuse _ | exact Fixed.liftU _ | exact Fixed.monadLiftU _
  | exact Fixed.liftMU _ | exact Fixed.getO _ | exact Fixed.must _ | exact Fixed.uEnt _ _
  | exact Fixed.lin _ | exact Fixed.t2Lin _ _ | exact Fixed.paid _ | exact Fixed.hideRun _ _ _
  | fixed_hyp
  | apply Fixed.bind | apply Fixed.map
  | apply Fixed.foldlM | apply Fixed.arrayFoldlM | apply Fixed.forIn | apply Fixed.arrayForIn
  | apply Fixed.rangeForIn | apply Fixed.forM | apply Fixed.arrayForM | apply Fixed.mapM)

open Lean Meta Elab Tactic in
/-- Lays a local definition at the head of the routine in, and applies a function that is written
out to its argument. -/
elab "fixed_norm" : tactic => do
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
macro "fixed_step" : tactic => `(tactic| first
  | fixed_intro
  | fixed_norm
  | fixed_rule
  | fixed_open
  | split)

/-- Proves Fixed x. -/
macro "fixed" : tactic => `(tactic| repeat' fixed_step)

end Fo
