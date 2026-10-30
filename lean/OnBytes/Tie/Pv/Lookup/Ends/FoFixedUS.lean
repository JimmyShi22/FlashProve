-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoFixedUS.lean.
Routines whose added claims are fixed before the state, read one array alone, and name slots below
the number of slots.

`FixedUS t0 x`: the clauses of Fo.FixedU t0 x (OnBytes/Tie/Pv/Lookup/Ends/FoFixedU.lean), and OF THE
SAME LIST L one more, under the quantifier on runs: for every run of x that returns from a state F
with a coefficient for each slot, every slot that the form of a member of L (colsOf F) names is
below F.ns.
`lin_below`: a call of Fork.lin that returns has itself tested every slot of its form below ns.
`FixedUS.fixedU`: it gives Fo.FixedU. The rules and the tactic `fixedus` follow FixedU's, rule for
rule; the new clause is proved at three places: a routine that adds nothing, a bind (the number of
slots is kept along a run), SubM.lin.

Limits: those of Fo.Fixed and Fo.FixedU: the value and the list hang on the routine's arguments;
they speak of runs that return; the identities stand at the one batching element of the state; no
consequence is drawn here.
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a run returns, or which the claims are.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedU

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem pushSlot_below (w : E) (ns : ℕ) : ∀ (l : List (ℕ × E)) (LS LS' : Array E),
    l.foldlM (Fork.pushSlot w ns) LS = some LS' → ∀ y ∈ l, y.1 < ns
  | [], _, _, _ => fun _ hy => absurd hy List.not_mem_nil
  | x :: l, LS, LS', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨LS1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · unfold Fork.pushSlot at h1
      split at h1
      · assumption
      · cases h1
    · exact pushSlot_below w ns l LS1 LS' h2 y hy

theorem push_below {F G : Fork} {w : E} {f : Aff} (h : F.push w f = some G) :
    ∀ y ∈ f.slots.toList, y.1 < F.ns := by
  unfold Fork.push at h
  split at h
  · cases h
  · simp only at h
    split at h
    · rename_i t' LS' _ h2
      rw [← Array.foldlM_toList] at h2
      exact pushSlot_below _ _ _ _ _ h2
    · cases h

theorem kap_ns {F : Fork} {x : E × Fork} (h : F.kap = some x) : x.2.ns = F.ns := by
  unfold Fork.kap at h
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
  show y.2.ns = F.ns
  unfold Fork.kapTake at hy
  split at hy
  · cases hy
  · split at hy
    · obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.1 hy
      rfl
    · split at hy
      · obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.1 hy
        rfl
      · cases hy

/-- A call of Fork.lin that returns has tested every slot of its form below ns. -/
theorem lin_below {F G : Fork} {f : Aff} (h : F.lin f = some G) :
    ∀ y ∈ f.slots.toList, y.1 < F.ns := by
  unfold Fork.lin at h
  obtain ⟨x, hx, hp⟩ := Option.bind_eq_some_iff.1 h
  intro y hy
  rw [← kap_ns hx]
  exact push_below hp y hy

/-- FixedU, with slots below the number of slots. -/
def FixedUS {α : Type} [HasGood α] (t0 : ℕ) (x : SubM α) : Prop :=
  ∃ (v : (ℕ → ℕ) → Option α) (L : (ℕ → ℕ) → List Cl),
    (∀ (F : Fork) (c : Ctx) (a : α) (G : Fork) (c' : Ctx), x F c = .ok ((a, G), c') →
      F.LS.size = F.ns → v (colsOf F) = some a ∧ Added F G (L (colsOf F)) ∧ colsOf G = colsOf F ∧
        ∀ cl ∈ L (colsOf F), ∀ y ∈ cl.1.slots.toList, y.1 < F.ns) ∧
    (∀ k a, v k = some a → good t0 a) ∧ ∀ k, ∀ cl ∈ L k, GoodCl t0 cl

section
variable {α β σ : Type} [HasGood α] [HasGood β] [HasGood σ] {t0 : ℕ}

theorem FixedUS.fixedU {x : SubM α} (h : FixedUS t0 x) : FixedU t0 x := by
  obtain ⟨v, L, hv, g1, g2⟩ := h
  exact ⟨v, L, fun F c a G c' hr hs =>
    ⟨(hv F c a G c' hr hs).1, (hv F c a G c' hr hs).2.1, (hv F c a G c' hr hs).2.2.1⟩, g1, g2⟩

/-- From Fixed with no claim and a value that is good whatever it is. -/
theorem FixedUS.ofQuiet {x : SubM α} (v : (ℕ → ℕ) → Option α)
    (h : ∀ F c a G c', x F c = .ok ((a, G), c') → F.LS.size = F.ns →
      v (colsOf F) = some a ∧ Added F G [] ∧ colsOf G = colsOf F)
    (hg : ∀ k a, v k = some a → good t0 a) : FixedUS t0 x :=
  ⟨v, fun _ => [], fun F c a G c' hr hs =>
    ⟨(h F c a G c' hr hs).1, (h F c a G c' hr hs).2.1, (h F c a G c' hr hs).2.2,
      fun _ hc => absurd hc List.not_mem_nil⟩, hg, fun _ _ hc => absurd hc List.not_mem_nil⟩

theorem FixedUS.pure (a : α) [h : Good t0 a] : FixedUS t0 (Pure.pure a : SubM α) :=
  FixedUS.ofQuiet (fun _ => some a) (fun F c b G c' hr hs => by
    have e := (pure_ok _ _ _ _).1 hr
    have e1 : b = a := congrArg (fun x : (α × Fork) × Ctx => x.1.1) e
    have e2 : G = F := congrArg (fun x : (α × Fork) × Ctx => x.1.2) e
    rw [e1, e2]
    exact ⟨rfl, Added.refl hs, rfl⟩) fun _ b hb => by
      rw [← Option.some.inj hb]
      exact h.out

theorem FixedUS.bind {x : SubM α} {f : α → SubM β} (hx : FixedUS t0 x)
    (hf' : ∀ a, Good t0 a → FixedUS t0 (f a)) : FixedUS t0 (x >>= f) := by
  classical
  have hf : ∀ a, good t0 a → FixedUS t0 (f a) := fun a h => hf' a ⟨h⟩
  obtain ⟨v, L, hv, gv, gL⟩ := hx
  let w : α → (ℕ → ℕ) → Option β := fun a =>
    if h : good t0 a then (hf a h).choose else fun _ => none
  let M : α → (ℕ → ℕ) → List Cl := fun a =>
    if h : good t0 a then (hf a h).choose_spec.choose else fun _ => []
  have hw : ∀ a (h : good t0 a),
      (∀ (F : Fork) (c : Ctx) (b : β) (G : Fork) (c' : Ctx), f a F c = .ok ((b, G), c') →
        F.LS.size = F.ns → w a (colsOf F) = some b ∧ Added F G (M a (colsOf F)) ∧
          colsOf G = colsOf F ∧ ∀ cl ∈ M a (colsOf F), ∀ y ∈ cl.1.slots.toList, y.1 < F.ns) ∧
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
    obtain ⟨e1, a1, k1, s1⟩ := hv _ _ _ _ _ h1 hs
    obtain ⟨e2, a2, k2, s2⟩ := (hw a (gv _ _ e1)).1 _ _ _ _ _ h2 a1.sized
    rw [k1] at e2 a2 k2 s2
    rw [a1.ns] at s2
    refine ⟨?_, ?_, k2, ?_⟩
    · show (v (colsOf F)).bind _ = _
      rw [e1]
      exact e2
    · show Added F G (L (colsOf F) ++ match v (colsOf F) with
        | some a => M a (colsOf F)
        | none => [])
      rw [e1]
      exact a1.trans a2
    · show ∀ cl ∈ (L (colsOf F) ++ match v (colsOf F) with
        | some a => M a (colsOf F)
        | none => []), _
      rw [e1]
      intro cl hc
      rcases List.mem_append.1 hc with hc | hc
      · exact s1 cl hc
      · exact s2 cl hc
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

theorem FixedUS.map {x : SubM α} (f : α → β) (hx : FixedUS t0 x)
    (hf : ∀ a, Good t0 a → Good t0 (f a)) : FixedUS t0 (f <$> x) := by
  rw [← bind_pure_comp]
  exact hx.bind fun a ha => @FixedUS.pure _ _ _ _ (hf a ha)

theorem FixedUS.never {x : SubM α} (h : ∀ F c r, x F c ≠ .ok r) : FixedUS t0 x :=
  FixedUS.ofQuiet (fun _ => none) (fun F c _ _ _ hr _ => absurd hr (h F c _))
    fun _ _ h => by cases h

theorem FixedUS.refuse (name : String) : FixedUS t0 (liftM (refuse name : Blk α) : SubM α) :=
  FixedUS.never fun F c r hr => by
    obtain ⟨_, _, h1, _⟩ := (lift_ok _ _ _ _).1 hr
    exact absurd h1 (by simp [Model.refuse, Blk.fail])

/-- From Fixed of a routine that adds nothing, if every value of the type is good. -/
theorem FixedUS.unit [Subsingleton α] [hu : Unasked α] {x : SubM α}
    (h : ∀ F c a G c', x F c = .ok ((a, G), c') → F.LS.size = F.ns →
      Added F G [] ∧ colsOf G = colsOf F) : FixedUS t0 x := by
  classical
  refine FixedUS.ofQuiet (fun _ => if hn : Nonempty α then some hn.some else none)
    (fun F c a G c' hr hs => ⟨?_, h F c a G c' hr hs⟩) fun _ a _ => hu.all t0 a
  rw [dif_pos ⟨a⟩]
  exact congrArg some (Subsingleton.elim _ _)

theorem FixedUS.liftU [Subsingleton α] [Unasked α] (b : Blk α) :
    FixedUS t0 (StateT.lift b : SubM α) :=
  FixedUS.unit fun F c a G c' hr hs => by
    obtain ⟨_, _, _, e⟩ := (lift_ok _ _ _ _).1 hr
    have e2 : G = F := congrArg (fun x : (α × Fork) × Ctx => x.1.2) e
    rw [e2]
    exact ⟨Added.refl hs, rfl⟩

theorem FixedUS.monadLiftU [Subsingleton α] [Unasked α] (b : Blk α) :
    FixedUS t0 (MonadLiftT.monadLift b : SubM α) := FixedUS.liftU b

theorem FixedUS.liftMU [Subsingleton α] [Unasked α] (b : Blk α) :
    FixedUS t0 (liftM b : SubM α) := FixedUS.liftU b

theorem FixedUS.must (b : Bool) : FixedUS t0 (SubM.must b) := FixedUS.liftU _

theorem FixedUS.getO (x : Option α) [hx : Good t0 x] : FixedUS t0 (SubM.get x) :=
  FixedUS.ofQuiet (fun _ => x) (fun F c a G c' hr hs => by
    obtain ⟨a', h1, e⟩ := (get_ok _ _ _ _).1 hr
    have e1 : a = a' := congrArg (fun x : (α × Fork) × Ctx => x.1.1) e
    have e2 : G = F := congrArg (fun x : (α × Fork) × Ctx => x.1.2) e
    rw [e1, e2]
    exact ⟨h1, Added.refl hs, rfl⟩) fun _ a ha => hx.out a ha

theorem FixedUS.uEnt (x : ℕ) : FixedUS t0 (uEnt t0 x) :=
  FixedUS.ofQuiet (fun k => some (u3Form t0 (k t0) x)) (fun F c a G c' hr hs => by
    have e := uEnt_ok t0 x F c _ hr
    have e1 : a = _ := congrArg (fun x : (Aff × Fork) × Ctx => x.1.1) e
    have e2 : G = F := congrArg (fun x : (Aff × Fork) × Ctx => x.1.2) e
    rw [e1, e2]
    exact ⟨rfl, Added.refl hs, rfl⟩) fun k a ha => by
      rw [← Option.some.inj ha]
      exact InU.u3Form t0 _ _

theorem FixedUS.lin (f : Aff) [hf : Good t0 f] : FixedUS t0 (SubM.lin f) :=
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

theorem FixedUS.paid (i : ℕ) : FixedUS t0 (SubM.paid i) :=
  FixedUS.unit fun F c a G c' hr hs => by
    unfold SubM.paid at hr
    obtain ⟨G', h1, e⟩ := (change_ok _ _ _ _).1 hr
    have e2 : G = G' := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e
    rw [e2, ← Option.some.inj h1]
    exact ⟨added_paid hs i, rfl⟩

theorem FixedUS.ite {p : Prop} [Decidable p] {x y : SubM α} (hx : FixedUS t0 x)
    (hy : FixedUS t0 y) : FixedUS t0 (if p then x else y) := by
  split
  · exact hx
  · exact hy

theorem FixedUS.foldlM {f : σ → α → SubM σ}
    (hf : ∀ s a, Good t0 s → Good t0 a → FixedUS t0 (f s a)) :
    ∀ (l : List α) (s : σ), Good t0 l → Good t0 s → FixedUS t0 (l.foldlM f s)
  | [], s, _, _ => FixedUS.pure s
  | a :: l, s, hl, hs => by
    rw [List.foldlM_cons]
    exact (hf s a hs ⟨hl.out a List.mem_cons_self⟩).bind fun s' hs' =>
      FixedUS.foldlM hf l s' ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩ hs'

theorem FixedUS.arrayFoldlM {f : σ → α → SubM σ}
    (hf : ∀ s a, Good t0 s → Good t0 a → FixedUS t0 (f s a)) (l : Array α) (s : σ)
    (hl : Good t0 l) (hs : Good t0 s) : FixedUS t0 (l.foldlM f s) := by
  rw [← Array.foldlM_toList]
  exact FixedUS.foldlM hf _ s ⟨hl.out⟩ hs

theorem FixedUS.forIn {f : α → σ → SubM (ForInStep σ)}
    (hf : ∀ a s, Good t0 a → Good t0 s → FixedUS t0 (f a s)) :
    ∀ (l : List α) (s : σ), Good t0 l → Good t0 s → FixedUS t0 (ForIn.forIn l s f)
  | [], s, _, _ => by
    rw [List.forIn_nil]
    exact FixedUS.pure s
  | a :: l, s, hl, hs => by
    rw [List.forIn_cons]
    refine (hf a s ⟨hl.out a List.mem_cons_self⟩ hs).bind fun r hr => ?_
    cases r with
    | done b =>
      have : Good t0 b := ⟨hr.out⟩
      exact FixedUS.pure b
    | yield b =>
      exact FixedUS.forIn hf l b ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩ ⟨hr.out⟩

theorem FixedUS.arrayForIn {f : α → σ → SubM (ForInStep σ)}
    (hf : ∀ a s, Good t0 a → Good t0 s → FixedUS t0 (f a s)) (l : Array α) (s : σ)
    (hl : Good t0 l) (hs : Good t0 s) : FixedUS t0 (ForIn.forIn l s f) := by
  rw [← Array.forIn_toList]
  exact FixedUS.forIn hf _ s ⟨hl.out⟩ hs

theorem FixedUS.rangeForIn {f : ℕ → σ → SubM (ForInStep σ)}
    (hf : ∀ a s, Good t0 a → Good t0 s → FixedUS t0 (f a s)) (r : Std.Legacy.Range) (s : σ)
    (hs : Good t0 s) : FixedUS t0 (ForIn.forIn r s f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact FixedUS.forIn hf _ s inferInstance hs

theorem FixedUS.forM {f : α → SubM PUnit} (hf : ∀ a, Good t0 a → FixedUS t0 (f a)) :
    ∀ l : List α, Good t0 l → FixedUS t0 (l.forM f)
  | [], _ => FixedUS.pure _
  | a :: l, hl => by
    show FixedUS t0 (f a >>= fun _ => l.forM f)
    exact (hf a ⟨hl.out a List.mem_cons_self⟩).bind fun _ _ =>
      FixedUS.forM hf l ⟨fun x hx => hl.out x (List.mem_cons_of_mem _ hx)⟩

theorem FixedUS.arrayForM {f : α → SubM PUnit} (hf : ∀ a, Good t0 a → FixedUS t0 (f a))
    (l : Array α) (hl : Good t0 l) : FixedUS t0 (l.forM f) := by
  unfold Array.forM
  exact FixedUS.arrayFoldlM (fun _ a _ ha => hf a ha) l _ hl inferInstance

end

/-! ### the tactic -/

open Lean Meta Elab Tactic in
/-- Opens the definition at the head of the routine in a goal FixedUS t0 x, or of the value in a
goal Good t0 a. -/
elab "fixedus_open" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOf ``Fo.FixedUS || t.isAppOf ``Fo.Good do throwError "no goal of the two kinds"
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
elab "fixedus_intro" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless t.isForall do throwError "no bound variable"
  evalTactic (← `(tactic| intro _))

open Lean Meta Elab Tactic in
/-- Closes a goal Good t0 a by instance search. -/
elab "fixedus_good" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless t.isAppOf ``Fo.Good do throwError "no goal Good t0 a"
  evalTactic (← `(tactic| exact inferInstance))

open Lean Meta Elab Tactic in
/-- Applies a hypothesis. -/
elab "fixedus_hyp" : tactic => withMainContext do
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
macro "fixedus_rule" : tactic => `(tactic| with_reducible first
  | exact FixedUS.refuse _ | exact FixedUS.liftU _ | exact FixedUS.monadLiftU _
  | exact FixedUS.liftMU _ | exact FixedUS.must _ | exact FixedUS.uEnt _ | exact FixedUS.paid _
  | refine @FixedUS.pure _ _ _ _ ?_ | refine @FixedUS.getO _ _ _ _ ?_
  | refine @FixedUS.lin _ _ ?_
  | fixedus_hyp
  | refine FixedUS.bind ?_ ?_
  | refine FixedUS.foldlM ?_ _ _ ?_ ?_ | refine FixedUS.arrayFoldlM ?_ _ _ ?_ ?_
  | refine FixedUS.forIn ?_ _ _ ?_ ?_ | refine FixedUS.arrayForIn ?_ _ _ ?_ ?_
  | refine FixedUS.rangeForIn ?_ _ _ ?_
  | refine FixedUS.forM ?_ _ ?_ | refine FixedUS.arrayForM ?_ _ ?_
  | refine good_foldl _ ?_ _ _ ?_ ?_ | refine good_foldlArr _ ?_ _ _ ?_ ?_
  | refine @good_add _ _ _ ?_ ?_ | refine @good_sub _ _ _ ?_ ?_
  | refine @good_addMul _ _ _ _ ?_ ?_ | refine @good_scale _ _ _ ?_
  | refine @good_ite _ _ _ _ _ _ _ ?_ ?_)

open Lean Meta Elab Tactic in
/-- Lays a local definition at the head of the routine or value in, and applies a function that is
written out to its argument. -/
elab "fixedus_norm" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOf ``Fo.FixedUS || t.isAppOf ``Fo.Good do throwError "no goal of the two kinds"
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
macro "fixedus_step" : tactic => `(tactic| first
  | fixedus_intro
  | fixedus_norm
  | fixedus_good
  | fixedus_rule
  | fixedus_open
  | split)

/-- Proves FixedUS t0 x; leaves the goals on goodness that it cannot close. -/
macro "fixedus" : tactic => `(tactic| repeat' fixedus_step)

end Fo
