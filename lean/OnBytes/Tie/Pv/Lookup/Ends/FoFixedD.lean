-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoFixedD.lean.
Routines whose added claims are fixed before the state: the value and the list as data.

`FixedUS t0 x` (OnBytes/Tie/Pv/Lookup/Ends/FoFixedUS.lean) says that there are a value v and a list
L of claims, functions of the arrays' numbers of columns, such that every run of x that returns
gives v and adds L; that what they hold reads one array alone; and that L names slots below the
number of slots. It is a proposition: its v and L stand under an ∃, so nothing can be said of them
from outside, and the rule for a bind picks them by choice.

 * `FixedD t0 x`: the same as a record: the fields `v` and `L` are data; `run`, `goodV`, `goodL` are
   the three clauses of `FixedUS` of them.
 * `FixedD.fixedUS`: it gives `FixedUS`.
 * Every rule of OnBytes/Tie/Pv/Lookup/Ends/FoFixedUS.lean again, as a definition. `FixedD.bind`: `L
   k` is the first routine's list, then the list of the second at the first's value `v k`, and
   nothing if there is none: no choice. `FixedD.lin f`: the list is `[(f, #[])]`. Loops go by
   recursion on the list.
 * `FixedD.cast`: along an equation of routines; the data do not turn.
 * The tactic `fixedd`: that of OnBytes/Tie/Pv/Lookup/Ends/FoFixedUS.lean, with a rule for `if`
   before the step that splits a match. Since the goal is data, WHICH term it builds is the value
   and the list: what they are at a routine is known by unfolding (the lemmas below) or by a run,
   not from the routine's name.
 * `bindV_some`, `bindL_some`, `bind_L`, `lin_L`, `pure_L`, `cast_L`: how the data of a bind, of
   `SubM.lin`, of `pure` and of a cast unfold.

One turn against OnBytes/Tie/Pv/Lookup/Ends/FoFixedUS.lean: its rule for a routine that adds nothing
and has at most one value takes that value by choice; here the type must have a named value
(`Inhabited`).

Limits: those of Fo.Fixed, Fo.FixedU and Fo.FixedUS on the run clause: it speaks of runs that
return; the value and the list hang on the routine's arguments; the identities stand at the one
batching element of the state.
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a run returns.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedUS

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- FixedUS, with the value and the list as data. -/
structure FixedD {α : Type} [HasGood α] (t0 : ℕ) (x : SubM α) where
  v : (ℕ → ℕ) → Option α
  L : (ℕ → ℕ) → List Cl
  run : ∀ (F : Fork) (c : Ctx) (a : α) (G : Fork) (c' : Ctx), x F c = .ok ((a, G), c') →
    F.LS.size = F.ns → v (colsOf F) = some a ∧ Added F G (L (colsOf F)) ∧ colsOf G = colsOf F ∧
      ∀ cl ∈ L (colsOf F), ∀ y ∈ cl.1.slots.toList, y.1 < F.ns
  goodV : ∀ k a, v k = some a → good t0 a
  goodL : ∀ k, ∀ cl ∈ L k, GoodCl t0 cl

section
variable {α β σ : Type} [HasGood α] [HasGood β] [HasGood σ] {t0 : ℕ}

theorem FixedD.fixedUS {x : SubM α} (h : FixedD t0 x) : FixedUS t0 x :=
  ⟨h.v, h.L, h.run, h.goodV, h.goodL⟩

/-- Along an equation of routines. -/
def FixedD.cast {x y : SubM α} (e : x = y) (h : FixedD t0 x) : FixedD t0 y :=
  ⟨h.v, h.L, e ▸ h.run, h.goodV, h.goodL⟩

theorem cast_L {x y : SubM α} (e : x = y) (h : FixedD t0 x) : (h.cast e).L = h.L := rfl

theorem cast_v {x y : SubM α} (e : x = y) (h : FixedD t0 x) : (h.cast e).v = h.v := rfl

/-- A routine that adds nothing. -/
def FixedD.ofQuiet {x : SubM α} (v : (ℕ → ℕ) → Option α)
    (h : ∀ F c a G c', x F c = .ok ((a, G), c') → F.LS.size = F.ns →
      v (colsOf F) = some a ∧ Added F G [] ∧ colsOf G = colsOf F)
    (hg : ∀ k a, v k = some a → good t0 a) : FixedD t0 x :=
  ⟨v, fun _ => [], fun F c a G c' hr hs =>
    ⟨(h F c a G c' hr hs).1, (h F c a G c' hr hs).2.1, (h F c a G c' hr hs).2.2,
      fun _ hc => absurd hc List.not_mem_nil⟩, hg, fun _ _ hc => absurd hc List.not_mem_nil⟩

def FixedD.pure (a : α) [h : Good t0 a] : FixedD t0 (Pure.pure a : SubM α) :=
  FixedD.ofQuiet (fun _ => some a) (fun F c b G c' hr hs => by
    have e := (pure_ok _ _ _ _).1 hr
    have e1 : b = a := congrArg (fun x : (α × Fork) × Ctx => x.1.1) e
    have e2 : G = F := congrArg (fun x : (α × Fork) × Ctx => x.1.2) e
    rw [e1, e2]
    exact ⟨rfl, Added.refl hs, rfl⟩) fun _ b hb => by
      rw [← Option.some.inj hb]
      exact h.out

theorem pure_L (a : α) [Good t0 a] (k : ℕ → ℕ) : (FixedD.pure (t0 := t0) a).L k = [] := rfl

theorem pure_v (a : α) [Good t0 a] (k : ℕ → ℕ) : (FixedD.pure (t0 := t0) a).v k = some a := rfl

/-- The value of a bind. -/
def bindV {x : SubM α} {f : α → SubM β} (hx : FixedD t0 x)
    (hf : ∀ a, Good t0 a → FixedD t0 (f a)) (k : ℕ → ℕ) : Option β :=
  match h : hx.v k with
  | some a => (hf a ⟨hx.goodV k a h⟩).v k
  | none => none

/-- What the second routine of a bind adds. -/
def bindL {x : SubM α} {f : α → SubM β} (hx : FixedD t0 x)
    (hf : ∀ a, Good t0 a → FixedD t0 (f a)) (k : ℕ → ℕ) : List Cl :=
  match h : hx.v k with
  | some a => (hf a ⟨hx.goodV k a h⟩).L k
  | none => []

theorem bindV_some {x : SubM α} {f : α → SubM β} (hx : FixedD t0 x)
    (hf : ∀ a, Good t0 a → FixedD t0 (f a)) {k : ℕ → ℕ} {a : α} (e : hx.v k = some a) :
    bindV hx hf k = (hf a ⟨hx.goodV k a e⟩).v k := by
  unfold bindV
  split
  · rename_i a' h'
    obtain rfl : a' = a := Option.some.inj (h'.symm.trans e)
    rfl
  · rename_i h'
    rw [e] at h'
    cases h'

theorem bindL_some {x : SubM α} {f : α → SubM β} (hx : FixedD t0 x)
    (hf : ∀ a, Good t0 a → FixedD t0 (f a)) {k : ℕ → ℕ} {a : α} (e : hx.v k = some a) :
    bindL hx hf k = (hf a ⟨hx.goodV k a e⟩).L k := by
  unfold bindL
  split
  · rename_i a' h'
    obtain rfl : a' = a := Option.some.inj (h'.symm.trans e)
    rfl
  · rename_i h'
    rw [e] at h'
    cases h'

theorem bindV_none {x : SubM α} {f : α → SubM β} (hx : FixedD t0 x)
    (hf : ∀ a, Good t0 a → FixedD t0 (f a)) {k : ℕ → ℕ} (e : hx.v k = none) :
    bindV hx hf k = none := by
  unfold bindV
  split
  · rename_i a' h'
    rw [e] at h'
    cases h'
  · rfl

theorem bindL_none {x : SubM α} {f : α → SubM β} (hx : FixedD t0 x)
    (hf : ∀ a, Good t0 a → FixedD t0 (f a)) {k : ℕ → ℕ} (e : hx.v k = none) :
    bindL hx hf k = [] := by
  unfold bindL
  split
  · rename_i a' h'
    rw [e] at h'
    cases h'
  · rfl

def FixedD.bind {x : SubM α} {f : α → SubM β} (hx : FixedD t0 x)
    (hf : ∀ a, Good t0 a → FixedD t0 (f a)) : FixedD t0 (x >>= f) where
  v := bindV hx hf
  L k := hx.L k ++ bindL hx hf k
  run F c b G c' hr hs := by
    obtain ⟨a, F1, c1, h1, h2⟩ := (bind_ok _ _ _ _ _).1 hr
    obtain ⟨e1, a1, k1, s1⟩ := hx.run _ _ _ _ _ h1 hs
    obtain ⟨e2, a2, k2, s2⟩ := (hf a ⟨hx.goodV _ _ e1⟩).run _ _ _ _ _ h2 a1.sized
    rw [k1] at e2 a2 k2 s2
    rw [a1.ns] at s2
    rw [bindV_some hx hf e1, bindL_some hx hf e1]
    refine ⟨e2, a1.trans a2, k2, fun cl hc => ?_⟩
    rcases List.mem_append.1 hc with hc | hc
    · exact s1 cl hc
    · exact s2 cl hc
  goodV k b hb := by
    cases ha : hx.v k with
    | none =>
      rw [bindV_none hx hf ha] at hb
      cases hb
    | some a =>
      rw [bindV_some hx hf ha] at hb
      exact (hf a ⟨hx.goodV _ _ ha⟩).goodV k b hb
  goodL k cl hc := by
    rcases List.mem_append.1 hc with hc | hc
    · exact hx.goodL k cl hc
    · cases ha : hx.v k with
      | none =>
        rw [bindL_none hx hf ha] at hc
        exact absurd hc List.not_mem_nil
      | some a =>
        rw [bindL_some hx hf ha] at hc
        exact (hf a ⟨hx.goodV _ _ ha⟩).goodL k cl hc

theorem bind_L {x : SubM α} {f : α → SubM β} (hx : FixedD t0 x)
    (hf : ∀ a, Good t0 a → FixedD t0 (f a)) (k : ℕ → ℕ) :
    (hx.bind hf).L k = hx.L k ++ bindL hx hf k := rfl

theorem bind_v {x : SubM α} {f : α → SubM β} (hx : FixedD t0 x)
    (hf : ∀ a, Good t0 a → FixedD t0 (f a)) (k : ℕ → ℕ) :
    (hx.bind hf).v k = bindV hx hf k := rfl

def FixedD.map {x : SubM α} (f : α → β) (hx : FixedD t0 x)
    (hf : ∀ a, Good t0 a → Good t0 (f a)) : FixedD t0 (f <$> x) :=
  (hx.bind fun a ha => @FixedD.pure _ _ _ _ (hf a ha)).cast (bind_pure_comp f x)

def FixedD.never {x : SubM α} (h : ∀ F c r, x F c ≠ .ok r) : FixedD t0 x :=
  FixedD.ofQuiet (fun _ => none) (fun F c _ _ _ hr _ => absurd hr (h F c _))
    fun _ _ h => by cases h

def FixedD.refuse (name : String) : FixedD t0 (liftM (refuse name : Blk α) : SubM α) :=
  FixedD.never fun F c r hr => by
    obtain ⟨_, _, h1, _⟩ := (lift_ok _ _ _ _).1 hr
    exact absurd h1 (by simp [Model.refuse, Blk.fail])

/-- A routine that adds nothing and whose type has one value. -/
def FixedD.unit [Subsingleton α] [Inhabited α] [hu : Unasked α] {x : SubM α}
    (h : ∀ F c a G c', x F c = .ok ((a, G), c') → F.LS.size = F.ns →
      Added F G [] ∧ colsOf G = colsOf F) : FixedD t0 x :=
  FixedD.ofQuiet (fun _ => some default)
    (fun F c a G c' hr hs => ⟨congrArg some (Subsingleton.elim _ _), h F c a G c' hr hs⟩)
    fun _ a _ => hu.all t0 a

def FixedD.liftU [Subsingleton α] [Inhabited α] [Unasked α] (b : Blk α) :
    FixedD t0 (StateT.lift b : SubM α) :=
  FixedD.unit fun F c a G c' hr hs => by
    obtain ⟨_, _, _, e⟩ := (lift_ok _ _ _ _).1 hr
    have e2 : G = F := congrArg (fun x : (α × Fork) × Ctx => x.1.2) e
    rw [e2]
    exact ⟨Added.refl hs, rfl⟩

def FixedD.monadLiftU [Subsingleton α] [Inhabited α] [Unasked α] (b : Blk α) :
    FixedD t0 (MonadLiftT.monadLift b : SubM α) := FixedD.liftU b

def FixedD.liftMU [Subsingleton α] [Inhabited α] [Unasked α] (b : Blk α) :
    FixedD t0 (liftM b : SubM α) := FixedD.liftU b

def FixedD.must (b : Bool) : FixedD t0 (SubM.must b) := FixedD.liftU _

def FixedD.getO (x : Option α) [hx : Good t0 x] : FixedD t0 (SubM.get x) :=
  FixedD.ofQuiet (fun _ => x) (fun F c a G c' hr hs => by
    obtain ⟨a', h1, e⟩ := (get_ok _ _ _ _).1 hr
    have e1 : a = a' := congrArg (fun x : (α × Fork) × Ctx => x.1.1) e
    have e2 : G = F := congrArg (fun x : (α × Fork) × Ctx => x.1.2) e
    rw [e1, e2]
    exact ⟨h1, Added.refl hs, rfl⟩) fun _ a ha => hx.out a ha

def FixedD.uEnt (x : ℕ) : FixedD t0 (uEnt t0 x) :=
  FixedD.ofQuiet (fun k => some (u3Form t0 (k t0) x)) (fun F c a G c' hr hs => by
    have e := uEnt_ok t0 x F c _ hr
    have e1 : a = _ := congrArg (fun x : (Aff × Fork) × Ctx => x.1.1) e
    have e2 : G = F := congrArg (fun x : (Aff × Fork) × Ctx => x.1.2) e
    rw [e1, e2]
    exact ⟨rfl, Added.refl hs, rfl⟩) fun k a ha => by
      rw [← Option.some.inj ha]
      exact InU.u3Form t0 _ _

def FixedD.lin (f : Aff) [hf : Good t0 f] : FixedD t0 (SubM.lin f) :=
  ⟨fun _ => some (), fun _ => [(f, #[])], fun F c a G c' hr hs => by
    obtain ⟨h1, _⟩ := (SubM.lin_run f F G c c').1 hr
    exact ⟨rfl, added_lin hs h1, cols_of_frame
      (Fork.lin_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ F G f hs h1).2.2.2.2.2,
      fun cl hc => by
        rw [List.mem_singleton.1 hc]
        exact lin_below h1⟩,
    fun _ _ _ => trivial, fun _ cl hc => by
      rw [List.mem_singleton.1 hc]
      exact ⟨hf.out, fun r hr => by simp at hr⟩⟩

theorem lin_L (f : Aff) [Good t0 f] (k : ℕ → ℕ) : (FixedD.lin (t0 := t0) f).L k = [(f, #[])] :=
  rfl

def FixedD.paid (i : ℕ) : FixedD t0 (SubM.paid i) :=
  FixedD.unit fun F c a G c' hr hs => by
    unfold SubM.paid at hr
    obtain ⟨G', h1, e⟩ := (change_ok _ _ _ _).1 hr
    have e2 : G = G' := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e
    rw [e2, ← Option.some.inj h1]
    exact ⟨added_paid hs i, rfl⟩

def FixedD.ite {p : Prop} [Decidable p] {x y : SubM α} (hx : FixedD t0 x)
    (hy : FixedD t0 y) : FixedD t0 (if p then x else y) :=
  if h : p then hx.cast (if_pos h).symm else hy.cast (if_neg h).symm

def FixedD.foldlM {f : σ → α → SubM σ}
    (hf : ∀ s a, Good t0 s → Good t0 a → FixedD t0 (f s a)) :
    ∀ (l : List α) (s : σ), Good t0 l → Good t0 s → FixedD t0 (l.foldlM f s)
  | [], s, _, _ => FixedD.pure s
  | a :: l, s, hl, hs =>
    ((hf s a hs ⟨hl.out a List.mem_cons_self⟩).bind fun s' hs' =>
      FixedD.foldlM hf l s' ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩ hs').cast
      List.foldlM_cons.symm

def FixedD.arrayFoldlM {f : σ → α → SubM σ}
    (hf : ∀ s a, Good t0 s → Good t0 a → FixedD t0 (f s a)) (l : Array α) (s : σ)
    (hl : Good t0 l) (hs : Good t0 s) : FixedD t0 (l.foldlM f s) :=
  (FixedD.foldlM hf l.toList s ⟨hl.out⟩ hs).cast Array.foldlM_toList

/-- A loop over a list: one pass, then by what it yields: the end, or the loop over the rest. -/
def FixedD.forIn {f : α → σ → SubM (ForInStep σ)}
    (hf : ∀ a s, Good t0 a → Good t0 s → FixedD t0 (f a s)) :
    ∀ (l : List α) (s : σ), Good t0 l → Good t0 s → FixedD t0 (ForIn.forIn l s f)
  | [], s, _, _ => (FixedD.pure s).cast List.forIn_nil.symm
  | a :: l, s, hl, hs =>
    ((hf a s ⟨hl.out a List.mem_cons_self⟩ hs).bind fun r hr =>
      match r, hr with
      | .done b, hr => @FixedD.pure _ _ _ b ⟨hr.out⟩
      | .yield b, hr =>
        FixedD.forIn hf l b ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩ ⟨hr.out⟩).cast
      (by rw [List.forIn_cons])

def FixedD.arrayForIn {f : α → σ → SubM (ForInStep σ)}
    (hf : ∀ a s, Good t0 a → Good t0 s → FixedD t0 (f a s)) (l : Array α) (s : σ)
    (hl : Good t0 l) (hs : Good t0 s) : FixedD t0 (ForIn.forIn l s f) :=
  (FixedD.forIn hf l.toList s ⟨hl.out⟩ hs).cast Array.forIn_toList

def FixedD.rangeForIn {f : ℕ → σ → SubM (ForInStep σ)}
    (hf : ∀ a s, Good t0 a → Good t0 s → FixedD t0 (f a s)) (r : Std.Legacy.Range) (s : σ)
    (hs : Good t0 s) : FixedD t0 (ForIn.forIn r s f) :=
  (FixedD.forIn hf _ s inferInstance hs).cast (by rw [Std.Legacy.Range.forIn_eq_forIn_range'])

def FixedD.forM {f : α → SubM PUnit} (hf : ∀ a, Good t0 a → FixedD t0 (f a)) :
    ∀ l : List α, Good t0 l → FixedD t0 (l.forM f)
  | [], _ => FixedD.pure _
  | a :: l, hl =>
    ((hf a ⟨hl.out a List.mem_cons_self⟩).bind fun _ _ =>
      FixedD.forM hf l ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩ :
      FixedD t0 (f a >>= fun _ => l.forM f))

def FixedD.arrayForM {f : α → SubM PUnit} (hf : ∀ a, Good t0 a → FixedD t0 (f a))
    (l : Array α) (hl : Good t0 l) : FixedD t0 (l.forM f) :=
  (FixedD.arrayFoldlM (fun _ a _ ha => hf a ha) l _ hl inferInstance :
    FixedD t0 (l.foldlM (fun _ a => f a) PUnit.unit))

end

/-! ### the tactic -/

open Lean Meta Elab Tactic in
/-- Opens the definition at the head of the routine in a goal FixedD t0 x, or of the value in a
goal Good t0 a. -/
elab "fixedd_open" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOf ``Fo.FixedD || t.isAppOf ``Fo.Good do throwError "no goal of the two kinds"
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
elab "fixedd_intro" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless t.isForall do throwError "no bound variable"
  evalTactic (← `(tactic| intro _))

open Lean Meta Elab Tactic in
/-- Closes a goal Good t0 a by instance search. -/
elab "fixedd_good" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless t.isAppOf ``Fo.Good do throwError "no goal Good t0 a"
  evalTactic (← `(tactic| exact inferInstance))

open Lean Meta Elab Tactic in
/-- Applies a hypothesis. -/
elab "fixedd_hyp" : tactic => withMainContext do
  let g ← getMainGoal
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let s ← saveState
    try
      let gs ← withReducible (g.apply d.toExpr)
      replaceMainGoal gs
      return
    catch _ => s.restore
  throwError "no hypothesis applies"

/-- One step by a rule whose routine is the goal's as it is written. -/
macro "fixedd_rule" : tactic => `(tactic| with_reducible first
  | exact FixedD.refuse _ | exact FixedD.liftU _ | exact FixedD.monadLiftU _
  | exact FixedD.liftMU _ | exact FixedD.must _ | exact FixedD.uEnt _ | exact FixedD.paid _
  | refine @FixedD.pure _ _ _ _ ?_ | refine @FixedD.getO _ _ _ _ ?_
  | refine @FixedD.lin _ _ ?_
  | fixedd_hyp
  | refine FixedD.bind ?_ ?_
  | refine FixedD.ite ?_ ?_
  | refine FixedD.foldlM ?_ _ _ ?_ ?_ | refine FixedD.arrayFoldlM ?_ _ _ ?_ ?_
  | refine FixedD.forIn ?_ _ _ ?_ ?_ | refine FixedD.arrayForIn ?_ _ _ ?_ ?_
  | refine FixedD.rangeForIn ?_ _ _ ?_
  | refine FixedD.forM ?_ _ ?_ | refine FixedD.arrayForM ?_ _ ?_
  | refine good_foldl _ ?_ _ _ ?_ ?_ | refine good_foldlArr _ ?_ _ _ ?_ ?_
  | refine @good_add _ _ _ ?_ ?_ | refine @good_sub _ _ _ ?_ ?_
  | refine @good_addMul _ _ _ _ ?_ ?_ | refine @good_scale _ _ _ ?_
  | refine @good_ite _ _ _ _ _ _ _ ?_ ?_)

open Lean Meta Elab Tactic in
/-- Lays a local definition at the head of the routine or value in, and applies a function that is
written out to its argument. -/
elab "fixedd_norm" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOf ``Fo.FixedD || t.isAppOf ``Fo.Good do throwError "no goal of the two kinds"
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
macro "fixedd_step" : tactic => `(tactic| first
  | fixedd_intro
  | fixedd_norm
  | fixedd_good
  | fixedd_rule
  | fixedd_open
  | split)

/-- Proves FixedD t0 x; leaves the goals on goodness that it cannot close. -/
macro "fixedd" : tactic => `(tactic| repeat' fixedd_step)


end Fo
