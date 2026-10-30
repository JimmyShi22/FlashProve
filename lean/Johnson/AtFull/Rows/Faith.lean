-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/Faith.lean: WHAT A NOTING ROUTINE DOES TO THE PLAN IS WHAT THE
REPLAY OF ITS NOTED CALLS DOES. So the second test of callsFrom's «one» ((k2): the list of calls,
replayed alone, gives the planner's plan) is its first ((k1)). Theorems. A law file; no running text
imports it.
  `Still y`     a routine of the planner that leaves the plan as it was wherever it returns.
  `Faith x`     wherever x returns ((a, cs'), q) from (cs, p): cs' is cs and then a list n, and
                `forEach n Call.plan` returns q from p.
  `faith_pure`, `faith_bind`, `faith_ite`, `faith_forIn`, `faith_lift`, `faith_note`, `faith_noteV`;
  the tactic
  `fth`; then each routine by its name.
  `replay_of_runs`   a run (Walk.lean) from ⟨scope,0,0,0⟩ to ⟨sc',0,0,0⟩ of a faithful routine:
                `replay s scope cs.toList = .ok ⟨s, rs.toList⟩`: `noted`'s own plan.
`faith_forIn` goes step for step as the older `keeps_forIn` (OnBytes/Iop/DrySizes.lean).
Limits. A CONDITIONAL ON RETURNS. Nothing on soundness or on hiding.
-/
import Johnson.AtFull.Rows.Walk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

/-- A routine of the planner that leaves the plan as it was. -/
def Still {α : Type} (y : Planning α) : Prop := ∀ p a q, y.run p = .ok (a, q) → q = p

/-- What the routine does to the plan is what the replay of its noted calls does. -/
def Faith {α : Type} (x : N α) : Prop :=
  ∀ cs p a cs' q, (x.run cs).run p = .ok ((a, cs'), q) →
    ∃ n : List Call, cs' = cs ++ n.toArray ∧ (forEach n Call.plan).run p = .ok ((), q)

section
variable {α β : Type}

theorem still_pure (a : α) : Still (pure a : Planning α) := by
  intro p b q h
  cases h
  rfl

theorem still_bind {y : Planning α} {f : α → Planning β} (hy : Still y) (hf : ∀ a, Still (f a)) :
    Still (y >>= f) := by
  intro p b q h
  rw [StateT.run_bind] at h
  obtain ⟨⟨a, p1⟩, h1, h2⟩ := exc_bind h
  have e1 := hy p a p1 h1
  subst e1
  exact hf a _ b q h2

theorem still_refuse (why : String) : Still (refusePlan why : Planning α) := by
  intro p a q h
  cases h

theorem still_needs (b : Bool) (why : String) : Still (needs b why) := by
  unfold needs
  split
  · exact still_pure _
  · exact still_refuse _

theorem still_must (x : Option α) (why : String) : Still (must x why) := by
  cases x with
  | none => exact still_refuse _
  | some a => exact still_pure a

theorem still_theSetting : Still theSetting := by
  intro p a q h
  cases h
  rfl

theorem still_theScope : Still theScope := by
  intro p a q h
  cases h
  rfl

end

/-- Steps through a routine that leaves the plan. -/
macro "still" : tactic => `(tactic| (try dsimp only) <;> repeat' first
  | with_reducible apply still_bind
  | with_reducible exact still_pure _
  | with_reducible exact still_needs _ _
  | with_reducible exact still_must _ _
  | with_reducible exact still_refuse _
  | with_reducible exact still_theSetting
  | with_reducible exact still_theScope
  | with_reducible intro _)

theorem forEach_nil_run {γ : Type} (f : γ → Planning Unit) (p : PlanState) :
    (forEach [] f).run p = .ok ((), p) := by
  unfold forEach
  rfl

theorem forEach_cons_run {γ : Type} (f : γ → Planning Unit) (a : γ) (t : List γ) (p : PlanState) :
    (forEach (a :: t) f).run p = ((f a).run p >>= fun r => (forEach t f).run r.2) := by
  conv => lhs; unfold forEach
  rw [StateT.run_bind]

/-- A replay of two lists, one behind the other. -/
theorem forEach_app_run {γ : Type} {f : γ → Planning Unit} :
    ∀ {l₁ l₂ : List γ} {p q r : PlanState}, (forEach l₁ f).run p = .ok ((), q) →
      (forEach l₂ f).run q = .ok ((), r) → (forEach (l₁ ++ l₂) f).run p = .ok ((), r)
  | [], l₂, p, q, r, h1, h2 => by
    rw [forEach_nil_run] at h1
    cases h1
    exact h2
  | a :: t, l₂, p, q, r, h1, h2 => by
    rw [forEach_cons_run] at h1
    obtain ⟨⟨u, p1⟩, e1, e2⟩ := exc_bind h1
    rw [List.cons_append, forEach_cons_run, e1]
    exact forEach_app_run e2 h2

section
variable {α β : Type}

theorem faith_pure (a : α) : Faith (pure a : N α) := by
  intro cs p b cs' q h
  cases h
  exact ⟨[], by simp, forEach_nil_run _ _⟩

theorem faith_bind {x : N α} {f : α → N β} (hx : Faith x) (hf : ∀ a, Faith (f a)) :
    Faith (x >>= f) := by
  intro cs p b cs' q h
  obtain ⟨a, cs1, p1, h1, h2⟩ := run_bind_ok h
  obtain ⟨n1, e1, g1⟩ := hx cs p a cs1 p1 h1
  obtain ⟨n2, e2, g2⟩ := hf a cs1 p1 b cs' q h2
  refine ⟨n1 ++ n2, ?_, forEach_app_run g1 g2⟩
  rw [e2, e1]
  apply Array.ext'
  simp

theorem faith_ite {c : Prop} [Decidable c] {x y : N α} (hx : Faith x) (hy : Faith y) :
    Faith (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem faith_lift {y : Planning α} (hy : Still y) : Faith (liftM y : N α) := by
  intro cs p b cs' q h
  have h' : (y.run p >>= fun r => (pure ((r.1, cs), r.2) : Except String _)) =
      .ok ((b, cs'), q) := h
  obtain ⟨⟨a, q1⟩, h1, h2⟩ := exc_bind h'
  cases h2
  have e := hy p a q1 h1
  subst e
  exact ⟨[], by simp, forEach_nil_run _ _⟩

/-- A call noted beside a routine y whose effect on the plan is the call's own. -/
theorem faith_noteV (c : Call) {y : Planning α}
    (hy : ∀ p a q, y.run p = .ok (a, q) → c.plan.run p = .ok ((), q)) : Faith (noteV c y) := by
  intro cs p b cs' q h
  have h' : (y.run p >>= fun r => (pure ((r.1, cs.push c), r.2) : Except String _)) =
      .ok ((b, cs'), q) := h
  obtain ⟨⟨a, q1⟩, h1, h2⟩ := exc_bind h'
  cases h2
  refine ⟨[c], by apply Array.ext'; simp, ?_⟩
  rw [forEach_cons_run, hy p a q1 h1]
  exact forEach_nil_run Call.plan q1

/-- The value dropped. -/
theorem drop_run {y : Planning α} {p q : PlanState} {a : α} (h : y.run p = .ok (a, q)) :
    ((y >>= fun _ => pure ()) : Planning Unit).run p = .ok ((), q) := by
  rw [StateT.run_bind, h]
  rfl

theorem faith_forIn {γ : Type} {f : γ → PUnit → N (ForInStep PUnit)} (h : ∀ a r, Faith (f a r)) :
    ∀ (l : List γ) (b : PUnit), Faith (forIn l b f)
  | [], b => by
    rw [List.forIn_nil]
    exact faith_pure b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine faith_bind (h a b) fun s => ?_
    cases s with
    | done b' => exact faith_pure b'
    | yield b' => exact faith_forIn h l b'

end

theorem faith_note (c : Call) : Faith (note c) := by
  intro cs p b cs' q h
  have h' : (c.plan.run p >>= fun r => (pure ((r.1, cs.push c), r.2) : Except String _)) =
      .ok ((b, cs'), q) := h
  obtain ⟨⟨a, q1⟩, h1, h2⟩ := exc_bind h'
  cases h2
  refine ⟨[c], by apply Array.ext'; simp, ?_⟩
  rw [forEach_cons_run, h1]
  exact forEach_nil_run Call.plan q1

/-- One step through a noting routine. Each routine's own lemma is added below it. -/
syntax "fth_step" : tactic
macro_rules | `(tactic| fth_step) => `(tactic| with_reducible intro _)
macro_rules | `(tactic| fth_step) => `(tactic| with_reducible assumption)
macro_rules | `(tactic| fth_step) => `(tactic| (with_reducible refine faith_lift ?_) <;> still)
macro_rules
  | `(tactic| fth_step) =>
    `(tactic| (with_reducible refine faith_noteV _ (fun _ _ _ h => ?_)) <;> exact drop_run h)
macro_rules | `(tactic| fth_step) => `(tactic| with_reducible exact faith_note _)
macro_rules | `(tactic| fth_step) => `(tactic| with_reducible exact faith_pure _)
macro_rules | `(tactic| fth_step) => `(tactic| with_reducible apply faith_forIn)
macro_rules | `(tactic| fth_step) => `(tactic| with_reducible apply faith_ite)
macro_rules | `(tactic| fth_step) => `(tactic| with_reducible apply faith_bind)

/-- Steps through a noting routine. -/
macro "fth" : tactic => `(tactic| (try dsimp only) <;> repeat' fth_step)

theorem faith_nLookup (x : LookupSize) : Faith (nLookup x) := by
  unfold nLookup
  fth
macro_rules | `(tactic| fth_step) => `(tactic| with_reducible exact faith_nLookup _)

theorem faith_nForest (x : ForestSize) : Faith (nForest x) := faith_nLookup _
macro_rules | `(tactic| fth_step) => `(tactic| with_reducible exact faith_nForest _)

theorem faith_nSmall (x : SmallSize) (which : Nat) : Faith (nSmall x which) := by
  unfold nSmall
  fth
macro_rules | `(tactic| fth_step) => `(tactic| with_reducible exact faith_nSmall _ _)

theorem faith_nLayerOwn (x : LayerRounds) : Faith (nLayerOwn x) := by
  unfold nLayerOwn
  fth
macro_rules | `(tactic| fth_step) => `(tactic| with_reducible exact faith_nLayerOwn _)

theorem faith_nLayer (look : ForestSize) (x : LayerRounds) (small : SmallSize)
    (claims moment : Nat) :
    Faith (nLayer look x small claims moment) := by
  unfold nLayer
  fth

theorem faith_nAttentionOwn (x : AttentionRounds) : Faith (nAttentionOwn x) := by
  unfold nAttentionOwn
  fth
macro_rules | `(tactic| fth_step) => `(tactic| with_reducible exact faith_nAttentionOwn _)

theorem faith_nAttention (look : ForestSize) (x : AttentionRounds) (small : SmallSize)
    (moment : Nat) :
    Faith (nAttention look x small moment) := by
  unfold nAttention
  fth

theorem faith_nHead (look : ForestSize) (x : HeadRounds) (small : SmallSize) (moment : Nat) :
    Faith (nHead look x small moment) := by
  unfold nHead
  fth

theorem faith_nArm (a : Arm) (moment : Nat) : Faith (nArm a moment) := by
  cases a with
  | head l x s => exact faith_nHead l x s moment
  | layer l x s c => exact faith_nLayer l x s c moment
  | attention l x s => exact faith_nAttention l x s moment
  | none => exact faith_lift (still_needs _ _)
macro_rules | `(tactic| fth_step) => `(tactic| with_reducible exact faith_nArm _ _)

theorem faith_nStages (f : Nat) (m : Bool) :
    ∀ (first : Bool) (st : List StageSize), Faith (nStages f m first st)
  | first, x :: y :: rest => by
    have := faith_nStages f m false (y :: rest)
    unfold nStages
    fth
  | _, [x] => by
    unfold nStages
    fth
  | _, [] => by
    unfold nStages
    fth
macro_rules | `(tactic| fth_step) => `(tactic| with_reducible exact faith_nStages _ _ _ _)

theorem faith_nIopp (st : List StageSize) (rows f : Nat) (m : Bool) :
    Faith (nIopp st rows f m) := by
  unfold nIopp
  fth
macro_rules | `(tactic| fth_step) => `(tactic| with_reducible exact faith_nIopp _ _ _ _)

theorem faith_nReqSend (codes : Codes) (sent : List OracleNotice) (group atStart : GroupSize)
    (riders : Nat) (ownRound : Bool) :
        Faith (nReqSend codes sent group atStart riders ownRound) := by
  unfold nReqSend
  fth
macro_rules | `(tactic| fth_step) => `(tactic| with_reducible exact faith_nReqSend _ _ _ _ _ _)

theorem faith_nMomentsA (A : Nat → Arm) (z : ProofSized) (l : Nat) (msgs : List ReqMessage) :
    ∀ fuel moment, Faith (nMomentsA A z l msgs fuel moment)
  | 0, _ => faith_pure _
  | fuel + 1, moment => by
    have := faith_nMomentsA A z l msgs fuel (moment + 1)
    unfold nMomentsA
    fth
macro_rules | `(tactic| fth_step) => `(tactic| with_reducible exact faith_nMomentsA _ _ _ _ _ _)

theorem faith_nFrameA (A : Nat → Arm) (z : ProofSized) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink) (open_ : List Nat) (before : GroupSize),
    Faith (nFrameA A z l gs links open_ before)
  | [], _, _, _, _ => by
    unfold nFrameA
    exact faith_pure _
  | g :: gs, l, links, open_, before => by
    have ih := fun c => faith_nFrameA A z gs (l + 1) (links.drop 1) (open_.drop 1) c
    unfold nFrameA
    cases links.head? with
    | none =>
      fth
    | some lk =>
      fth
      all_goals exact ih _

theorem faith_nLinFirst (codes : Codes) (x : LinSized) : Faith (nLinFirst codes x) := by
  unfold nLinFirst
  fth

theorem faith_nLinShared (codes : Codes) (x : LinSized) : Faith (nLinShared codes x) := by
  unfold nLinShared
  fth

theorem faith_nLinSecond (x : LinSized) : Faith (nLinSecond x) := by
  unfold nLinSecond
  fth

theorem faith_nLinkPlan (x : LinkSized) : Faith (nLinkPlan x) := by
  unfold nLinkPlan
  fth

open OnBytes.Plan in
theorem faith_nRanges (codes : Codes) (z : RangesSized) : Faith (nRanges codes z) := by
  unfold nRanges
  fth

/-- **The replay of what a faithful routine has noted gives `noted`'s own plan.** -/
theorem replay_of_runs {s : Setting} {scope sc' : Scope} {x : N Unit} {cs : Array Call}
    {rs : Array PlanRound} (hx : Faith x) (h : RunsN s ⟨scope, 0, 0, 0⟩ x () cs rs ⟨sc', 0, 0, 0⟩) :
    replay s scope cs.toList = .ok ⟨s, rs.toList⟩ := by
  obtain ⟨n, e, g⟩ := hx _ _ _ _ _ h
  have en : cs.toList = n := by
    rw [e]
    simp
  rw [en]
  unfold replay finish
  have g' : (forEach n Call.plan) { set := s, scope := scope } =
      .ok ((), (⟨sc', 0, 0, 0⟩ : SmallSt).plan s rs) := g
  rw [g']
  rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.faith_bind
#print axioms VerifiableInference.Desc.LinkJoin.faith_note
#print axioms VerifiableInference.Desc.LinkJoin.faith_nArm
#print axioms VerifiableInference.Desc.LinkJoin.faith_nFrameA
#print axioms VerifiableInference.Desc.LinkJoin.faith_nLinFirst
#print axioms VerifiableInference.Desc.LinkJoin.faith_nLinShared
#print axioms VerifiableInference.Desc.LinkJoin.faith_nLinSecond
#print axioms VerifiableInference.Desc.LinkJoin.faith_nLinkPlan
#print axioms VerifiableInference.Desc.LinkJoin.faith_nRanges
#print axioms VerifiableInference.Desc.LinkJoin.replay_of_runs
