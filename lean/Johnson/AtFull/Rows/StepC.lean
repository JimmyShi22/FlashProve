-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/StepC.lean: A PIECE WALKED CALL BY CALL. Steps.lean's test `pieceB`
reads all the rounds that a piece has written in one run; for Lean's kernel that grows dear with the
piece's length. Here the piece is run once FOR ITS CALLS ALONE, and then each call's own routine is
run from no round at the small state, its rounds held against the next written ones. Definitions and
theorems. A law file; no running text imports it.
  `RunsP`, `RunsP.bind`   Walk.lean's run and law of composition at the planner's own level.
  `walkCalls s truth st cs`   with code: the calls' routines one behind the other, each from no
                              round.
  `walk_runs`     what a «some» of it says of `forEach cs Call.plan`.
  `pieceC`        with code: the test of a piece by its calls.
  `good_oneC`     a faithful routine (Faith.lean) at which pieceC ends at counters 0 and at truth's
                  length is `Good`.
Limits. No closed fact is here. Nothing on soundness or on hiding.
-/
import Johnson.AtFull.Rows.Parts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

/-- y, from no round at σ, returns a, has written rs, and ends at σ'. -/
def RunsP {α : Type} (s : Setting) (σ : SmallSt) (y : Planning α) (a : α) (rs : Array PlanRound)
    (σ' : SmallSt) : Prop :=
  y.run (σ.plan s) = .ok (a, σ'.plan s rs)

/-- The law of composition at the planner's own level. -/
theorem RunsP.bind {α β : Type} {s : Setting} {σ σ₁ σ₂ : SmallSt} {y : Planning α}
    {f : α → Planning β}
    {a : α} {b : β} {rs rs' : Array PlanRound}
    (h1 : RunsP s σ y a rs σ₁) (hf : FrP (f a)) (h2 : RunsP s σ₁ (f a) b rs' σ₂) :
    RunsP s σ (y >>= f) b (rs ++ rs') σ₂ := by
  unfold RunsP at *
  have g := (hf (σ₁.plan s) b (σ₂.plan s rs') h2).2 rs
  rw [under_plan, under_plan, Array.append_empty] at g
  rw [StateT.run_bind, h1]
  exact g

/-- The calls' routines one behind the other, each from no round at the small state. -/
def walkCalls (s : Setting) (truth : List PlanRound) :
    SmallSt × Nat → List Call → Option (SmallSt × Nat)
  | st, [] => some st
  | st, c :: cs =>
    match c.plan.run (st.1.plan s) with
    | .error _ => none
    | .ok (_, q) =>
      if sameAll q.rounds.toList ((truth.drop st.2).take q.rounds.size) then
        walkCalls s truth (smallOf q, st.2 + q.rounds.size) cs
      else none

theorem forEach_cons_eq {γ : Type} (f : γ → Planning Unit) (a : γ) (t : List γ) :
    forEach (a :: t) f = (f a >>= fun _ => forEach t f) := by
  conv => lhs; unfold forEach

theorem walk_runs {s : Setting} {truth : List PlanRound} :
    ∀ (cs : List Call) (st st' : SmallSt × Nat), walkCalls s truth st cs = some st' →
      ∃ rs, RunsP s st.1 (forEach cs Call.plan) () rs st'.1 ∧ st'.2 = st.2 + rs.size ∧
        sameAll rs.toList ((truth.drop st.2).take rs.size) = true
  | [], st, st', h => by
    unfold walkCalls at h
    cases h
    exact ⟨#[], forEach_nil_run _ _, rfl, by simp [sameAll]⟩
  | c :: cs, st, st', h => by
    unfold walkCalls at h
    cases e : c.plan.run (st.1.plan s) with
    | error m =>
      rw [e] at h
      cases h
    | ok r =>
      obtain ⟨u, q⟩ := r
      rw [e] at h
      dsimp only at h
      split at h
      · rename_i c1
        obtain ⟨rs', hr', e2', hs'⟩ := walk_runs cs _ _ h
        have hset : q.set = s := (frP_plan c _ _ _ e).1
        subst hset
        have h1 : RunsP q.set st.1 c.plan () q.rounds (smallOf q) := e
        refine ⟨q.rounds ++ rs', ?_, ?_, ?_⟩
        · rw [forEach_cons_eq]
          exact RunsP.bind (f := fun _ => forEach cs Call.plan) h1 (frP_forEach frP_plan cs) hr'
        · rw [e2', Array.size_append]
          show st.2 + q.rounds.size + rs'.size = _
          omega
        · have hs2 :
              sameAll rs'.toList ((truth.drop (st.2 + q.rounds.size)).take rs'.size) = true := hs'
          rw [Array.toList_append, Array.size_append, List.take_add, List.drop_drop]
          exact sameAll_app c1 hs2
      · cases h

/-- The test of a piece by its calls. -/
def pieceC (s : Setting) (truth : List PlanRound) (st : SmallSt × Nat) (x : N Unit) :
    Option (SmallSt × Nat) :=
  match (x.run #[]).run (st.1.plan s) with
  | .error _ => none
  | .ok ((_, cs), _) => walkCalls s truth st cs.toList

/-- What a «some» of pieceC says: Steps.lean's step_runs, for a faithful routine. -/
theorem stepC_runs {s : Setting} {truth : List PlanRound} {st st' : SmallSt × Nat} {x : N Unit}
    (hx : Faith x) (h : pieceC s truth st x = some st') :
    ∃ cs rs, RunsN s st.1 x () cs rs st'.1 ∧ st'.2 = st.2 + rs.size ∧
      sameAll rs.toList ((truth.drop st.2).take rs.size) = true := by
  unfold pieceC at h
  cases e : (x.run #[]).run (st.1.plan s) with
  | error m =>
    rw [e] at h
    cases h
  | ok r =>
    obtain ⟨⟨u, cs⟩, q⟩ := r
    rw [e] at h
    dsimp only at h
    obtain ⟨n, en, g⟩ := hx _ _ _ _ _ e
    have ecs : cs.toList = n := by
      rw [en]
      simp
    rw [ecs] at h
    obtain ⟨rs, hr, e2, hs⟩ := walk_runs n _ _ h
    have eq : q = st'.1.plan s rs := congrArg Prod.snd (Except.ok.inj (g.symm.trans hr))
    subst eq
    exact ⟨cs, rs, e, e2, hs⟩

/-- **A faithful routine at which the walk by calls ends at counters 0 and at truth's length.** -/
theorem good_oneC {s : Setting} {truth : List PlanRound} {st : SmallSt × Nat} {sc' : Scope}
    {x : N Unit}
    (hx : Faith x) (h : pieceC s truth st x = some (⟨sc', 0, 0, 0⟩, truth.length)) :
        Good s truth st x := by
  obtain ⟨cs, rs, hr, e2, hs⟩ := stepC_runs hx h
  refine ⟨cs, rs, sc', hr, ?_⟩
  have e2' : truth.length = st.2 + rs.size := e2
  have e : (truth.drop st.2).take rs.size = truth.drop st.2 :=
    List.take_of_length_le (by rw [List.length_drop]; omega)
  rw [e] at hs
  exact hs

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.RunsP.bind
#print axioms VerifiableInference.Desc.LinkJoin.walk_runs
#print axioms VerifiableInference.Desc.LinkJoin.stepC_runs
#print axioms VerifiableInference.Desc.LinkJoin.good_oneC
