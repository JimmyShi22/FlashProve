-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Req/Flow.lean: a small calculus on the planner's routines: a routine only adds rounds
to the plan that is being written, and in which state it leaves the plan.

The planner is that of the verifier on bytes (OnBytes/Params/Planner.lean). A routine there changes
a plan that is being written, or refuses. The state holds the setting, the scope, the rounds so far,
and the bytes, roots and answers of a prover's message that no round has taken in yet. This file has
three properties of a routine, their rules for one routine behind another, and each routine of the
frame of a request's first chain (OnBytes/Params/DeriveReq.lean) under one of them.

Main names:
  `Live st p`: the state p has the setting st and a request's scope; whatever message is open.
    (`Idle st p`, OnBytes/Tie/Pv/Tail/Plan.lean: also no open message.)
  `Adds p q F`: q has the rounds of p and, behind them, the rounds F.
  `Runs st x`, `Keeps st x`, `Shuts st x`: x ends well only in a live state from a live one; in an
    idle state from an idle one; in an idle state from a live one; and it only adds rounds.
  `Runs.bind`, `Keeps.bind`, `Runs.then`, `Shuts.then`, `Keeps.ite`, `Runs.ite`: the rules.
  `shuts_close`, `shuts_none`, `runs_scalars`, `runs_answers`, `runs_roots`: the planner's own
    steps.
  `runs_reqSend`, `shuts_reqSend`: the frame's sending, without and with a round of its own for the
    answers. `shuts_loc`, `shuts_bat`, `shuts_fold`, `shuts_iopp` (with `shuts_cs`, `shuts_base`,
    `shuts_stages`), `shuts_batt`, `shuts_linFirst`, `shuts_seal`: the other routines of the frame.

Limits: no statement says that a routine ends well, which rounds it adds, or that a round's bound
holds of the protocol. Nothing is said on hiding.
-/
import OnBytes.Params.DeriveReq
import OnBytes.Tie.Pv.Lay.PlanLook
import OnBytes.Tie.Pv.Tail.CallFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Req

open OnBytes OnBytes.Params
open OnBytes.Tie.Pv.Tail (Idle Shut Reads plan_bind needs_ok close_shuts none_shuts)

/-- The setting st and a request's scope, whatever message is open. -/
structure Live (st : Setting) (p : PlanState) : Prop where
  set : p.set = st
  scope : p.scope = .request

theorem live_of_idle {st : Setting} {p : PlanState} (h : Idle st p) : Live st p :=
  ⟨h.set, h.scope⟩

/-- q has the rounds of p and, behind them, the rounds F. -/
def Adds (p q : PlanState) (F : List PlanRound) : Prop := q.rounds = p.rounds ++ F.toArray

theorem Adds.refl (p : PlanState) : Adds p p [] := by simp [Adds]

theorem Adds.trans {p q r : PlanState} {F G : List PlanRound} (h : Adds p q F) (k : Adds q r G) :
    Adds p r (F ++ G) := by
  unfold Adds at *
  rw [k, h]
  simp

theorem Adds.push {p q : PlanState} {R : PlanRound} (h : q.rounds = p.rounds.push R) :
    Adds p q [R] := by
  unfold Adds
  rw [h]
  simp

/-- From a live state x ends well only in a live state, and only adds rounds. -/
def Runs (st : Setting) {α : Type} (x : Planning α) : Prop :=
  ∀ p a q, Live st p → x p = .ok (a, q) → Live st q ∧ ∃ F, Adds p q F

/-- From an idle state x ends well only in an idle state, and only adds rounds. -/
def Keeps (st : Setting) {α : Type} (x : Planning α) : Prop :=
  ∀ p a q, Idle st p → x p = .ok (a, q) → Idle st q ∧ ∃ F, Adds p q F

/-- From a live state x ends well only in an idle state, and only adds rounds. -/
def Shuts (st : Setting) {α : Type} (x : Planning α) : Prop :=
  ∀ p a q, Live st p → x p = .ok (a, q) → Idle st q ∧ ∃ F, Adds p q F

section Calculus
variable {st : Setting} {α β : Type}

theorem Shuts.runs {x : Planning α} (h : Shuts st x) : Runs st x := fun p a q hp hq =>
  ⟨live_of_idle (h p a q hp hq).1, (h p a q hp hq).2⟩

theorem Shuts.keeps {x : Planning α} (h : Shuts st x) : Keeps st x := fun p a q hp hq =>
  h p a q (live_of_idle hp) hq

theorem runs_of_reads {x : Planning α} (h : Reads x) : Runs st x := fun p a q hp hq => by
  obtain rfl := h p a q hq
  exact ⟨hp, [], Adds.refl _⟩

theorem keeps_of_reads {x : Planning α} (h : Reads x) : Keeps st x := fun p a q hp hq => by
  obtain rfl := h p a q hq
  exact ⟨hp, [], Adds.refl _⟩

theorem Runs.bind {x : Planning α} {f : α → Planning β} (hx : Runs st x)
    (hf : ∀ a, Runs st (f a)) : Runs st (x >>= f) := fun p b q hp h => by
  obtain ⟨a, m, h1, h2⟩ := plan_bind h
  obtain ⟨l1, F, e1⟩ := hx p a m hp h1
  obtain ⟨l2, G, e2⟩ := hf a m b q l1 h2
  exact ⟨l2, F ++ G, e1.trans e2⟩

theorem Keeps.bind {x : Planning α} {f : α → Planning β} (hx : Keeps st x)
    (hf : ∀ a, Keeps st (f a)) : Keeps st (x >>= f) := fun p b q hp h => by
  obtain ⟨a, m, h1, h2⟩ := plan_bind h
  obtain ⟨l1, F, e1⟩ := hx p a m hp h1
  obtain ⟨l2, G, e2⟩ := hf a m b q l1 h2
  exact ⟨l2, F ++ G, e1.trans e2⟩

/-- Whatever runs, and then a routine that shuts. -/
theorem Runs.then {x : Planning α} {f : α → Planning β} (hx : Runs st x)
    (hf : ∀ a, Shuts st (f a)) : Shuts st (x >>= f) := fun p b q hp h => by
  obtain ⟨a, m, h1, h2⟩ := plan_bind h
  obtain ⟨l1, F, e1⟩ := hx p a m hp h1
  obtain ⟨l2, G, e2⟩ := hf a m b q l1 h2
  exact ⟨l2, F ++ G, e1.trans e2⟩

/-- A routine that shuts, and then one that keeps an idle state. -/
theorem Shuts.then {x : Planning α} {f : α → Planning β} (hx : Shuts st x)
    (hf : ∀ a, Keeps st (f a)) : Shuts st (x >>= f) := fun p b q hp h => by
  obtain ⟨a, m, h1, h2⟩ := plan_bind h
  obtain ⟨l1, F, e1⟩ := hx p a m hp h1
  obtain ⟨l2, G, e2⟩ := hf a m b q l1 h2
  exact ⟨l2, F ++ G, e1.trans e2⟩

theorem keeps_pure (a : α) : Keeps st (pure a : Planning α) := keeps_of_reads (Reads.pure a)
theorem runs_pure (a : α) : Runs st (pure a : Planning α) := runs_of_reads (Reads.pure a)

theorem Keeps.ite {c : Prop} [Decidable c] {x y : Planning α} (hx : Keeps st x)
    (hy : Keeps st y) : Keeps st (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem Runs.ite {c : Prop} [Decidable c] {x y : Planning α} (hx : Runs st x)
    (hy : Runs st y) : Runs st (if c then x else y) := by
  split
  · exact hx
  · exact hy

end Calculus

/-! ### The planner's own steps -/

section Steps
variable (st : Setting)

theorem shuts_close (name : String) (why : ErrorKind) (e : Bound) (d : Draws) :
    Shuts st (close name why e d) := fun p _ q hp h => by
  obtain ⟨a1, a2, a3, a4, a5, R, r, _⟩ := close_shuts h
  exact ⟨⟨a1.trans hp.set, a2.trans hp.scope, a3, a4, a5⟩, [R], Adds.push r⟩

theorem shuts_none (name : String) : Shuts st (closeNone name) := fun p _ q hp h => by
  obtain ⟨a1, a2, a3, a4, a5, R, r, _⟩ := none_shuts h
  exact ⟨⟨a1.trans hp.set, a2.trans hp.scope, a3, a4, a5⟩, [R], Adds.push r⟩

theorem runs_scalars (n : Nat) : Runs st (planScalars n) := fun p _ q hp h => by
  obtain rfl : { p with openBytes := p.openBytes + 24 * n } = q :=
    (Prod.mk.inj (Except.ok.inj h)).2
  exact ⟨⟨hp.set, hp.scope⟩, [], Adds.refl _⟩

theorem runs_answers (n : Nat) : Runs st (planAnswers n) := fun p _ q hp h => by
  obtain rfl : { p with openBytes := p.openBytes + 24 * n,
                        openAnswers := p.openAnswers + n } = q :=
    (Prod.mk.inj (Except.ok.inj h)).2
  exact ⟨⟨hp.set, hp.scope⟩, [], Adds.refl _⟩

theorem runs_roots (n : Nat) : Runs st (planRoots n) := fun p _ q hp h => by
  obtain rfl : { p with openBytes := p.openBytes + 32 * n,
                        openRoots := p.openRoots + n } = q :=
    (Prod.mk.inj (Except.ok.inj h)).2
  exact ⟨⟨hp.set, hp.scope⟩, [], Adds.refl _⟩

theorem reads_scope : Reads theScope := fun _ _ _ h => ((Prod.mk.inj (Except.ok.inj h)).2).symm

theorem reads_must {α : Type} (x : Option α) (why : String) : Reads (must x why) :=
  fun p a m h => by
  unfold must at h
  cases x with
  | none => cases h
  | some y => exact ((Prod.mk.inj (Except.ok.inj h)).2).symm

theorem reads_positions (agree extra : Bound) : Reads (planPositions agree extra) :=
  Reads.bind Tail.reads_setting fun _ => Reads.bind reads_scope fun _ => Reads.pure _

theorem reads_listed (logN t : Nat) : Reads (planListed logN t) :=
  Reads.bind Tail.reads_setting fun _ => Tail.reads_needs _ _

end Steps

/-! ### The frame's routines -/

section Routines
variable (st : Setting)

theorem runs_send (o : List SampleSize) (roots : Nat) (b : Bool) : Runs st (planSend o roots b) :=
  Runs.bind (runs_of_reads Tail.reads_setting) fun s =>
    Runs.bind (runs_roots st roots) fun _ =>
      Runs.bind (runs_of_reads (Tail.reads_errors s o _)) fun _ =>
        Runs.bind (shuts_close st _ _ _ _).runs fun _ =>
          Runs.bind (runs_answers st _) fun _ =>
            Runs.ite (shuts_none st _).runs (runs_pure _)

theorem shuts_send (o : List SampleSize) (roots : Nat) : Shuts st (planSend o roots true) :=
  Runs.then (runs_of_reads Tail.reads_setting) fun s =>
    Runs.then (runs_roots st roots) fun _ =>
      Runs.then (runs_of_reads (Tail.reads_errors s o _)) fun _ =>
        Runs.then (shuts_close st _ _ _ _).runs fun _ =>
          Runs.then (runs_answers st _) fun _ => by
            rw [if_pos rfl]
            exact shuts_none st _

theorem runs_reqSend (codes : Codes) (sent : List OracleNotice) (group atStart : GroupSize)
    (riders : Nat) (b : Bool) : Runs st (reqSend codes sent group atStart riders b) :=
  Runs.bind (runs_of_reads (reads_must _ _)) fun _ => runs_send st _ _ _

theorem shuts_reqSend (codes : Codes) (sent : List OracleNotice) (group atStart : GroupSize)
    (riders : Nat) : Shuts st (reqSend codes sent group atStart riders true) :=
  Runs.then (runs_of_reads (reads_must _ _)) fun _ => shuts_send st _ _

theorem shuts_bat (groups : List GroupSize) (rows : Nat) : Shuts st (planBat groups rows) :=
  Runs.then (runs_of_reads Tail.reads_setting) fun _ =>
    Runs.then (runs_of_reads (Tail.reads_list groups)) fun _ => shuts_close st _ _ _ _

theorem shuts_batSigma (rows : Nat) : Shuts st (planBatSigma rows) :=
  Runs.then (runs_of_reads Tail.reads_setting) fun _ => shuts_close st _ _ _ _

theorem shuts_loc (g : GroupSize) : Shuts st (planLoc g) :=
  Runs.then (runs_of_reads (Tail.reads_analysis g)) fun _ =>
    Runs.then (runs_of_reads (reads_positions _ _)) fun _ =>
      Runs.then (runs_of_reads (Tail.reads_needs _ _)) fun _ =>
        Shuts.then (shuts_close st _ _ _ _) fun _ =>
          Keeps.bind (keeps_of_reads (reads_listed _ _)) fun _ => keeps_pure _

theorem keeps_foldFrom (s : Setting) (g : GroupSize) (a : Analysis) :
    ∀ fuel j, Keeps st (planFoldFrom s g a fuel j)
  | 0, _ => keeps_pure ()
  | fuel + 1, j =>
    (Runs.then (runs_scalars st 2) fun _ =>
      Shuts.then (shuts_close st _ _ _ _) fun _ => keeps_foldFrom s g a fuel (j + 1)).keeps

theorem keeps_foldRounds (g : GroupSize) : Keeps st (planFoldRounds g) :=
  Keeps.bind (keeps_of_reads (Tail.reads_analysis g)) fun _ =>
    Keeps.bind (keeps_of_reads Tail.reads_setting) fun _ => keeps_foldFrom st _ g _ _ _

theorem shuts_fold (g : GroupSize) (roots : Nat) : Shuts st (planFold g roots) :=
  Runs.then (runs_of_reads Tail.reads_setting) fun _ =>
    Runs.then (runs_of_reads (Tail.reads_analysis g)) fun _ =>
      Runs.then (runs_roots st roots) fun _ =>
        Runs.then (runs_scalars st 1) fun _ =>
          Shuts.then (shuts_close st _ _ _ _) fun _ => keeps_foldRounds st g

theorem shuts_cs (source target : GroupSize) (cubeBits oldRows symbols roots : Nat) :
    Shuts st (planCs source target cubeBits oldRows symbols roots) :=
  Runs.then (runs_of_reads Tail.reads_setting) fun _ =>
    Runs.then (runs_of_reads (Tail.reads_analysis source)) fun _ =>
      Runs.then (runs_of_reads (Tail.reads_analysis target)) fun _ =>
        Runs.then (runs_send st _ _ _) fun _ =>
          Runs.then (runs_of_reads reads_scope) fun _ =>
            Runs.then (runs_of_reads (Tail.reads_needs _ _)) fun _ =>
              Shuts.then (shuts_close st _ _ _ _) fun _ =>
                Keeps.bind (keeps_of_reads (reads_listed _ _)) fun _ => keeps_pure _

theorem shuts_base (g : GroupSize) (roots : Nat) : Shuts st (planBase g roots) :=
  Runs.then (runs_of_reads Tail.reads_setting) fun _ =>
    Runs.then (runs_of_reads (Tail.reads_analysis g)) fun _ =>
      Runs.then (runs_roots st roots) fun _ =>
        Runs.then (runs_scalars st 1) fun _ =>
          Runs.then (shuts_close st _ _ _ _).runs fun _ =>
            Runs.then (runs_scalars st _) fun _ =>
              Runs.then (runs_of_reads (reads_positions _ _)) fun _ =>
                Runs.then (runs_of_reads (Tail.reads_needs _ _)) fun _ =>
                  Shuts.then (shuts_close st _ _ _ _) fun _ =>
                    Keeps.bind (keeps_of_reads (reads_listed _ _)) fun _ => keeps_pure _

theorem shuts_stages (fm : Nat) (ride : Bool) :
    ∀ (l : List StageSize) (first : Bool), Shuts st (planStages fm ride first l)
  | [], _ => fun _ _ _ _ h => by cases h
  | [x], _ =>
    Shuts.then (shuts_base st x.g _) fun _ => keeps_of_reads (Tail.reads_needs _ _)
  | x :: y :: rest, _ =>
    Runs.then (shuts_fold st x.g _).runs fun _ =>
      Runs.then (shuts_cs st _ _ _ _ _ _).runs fun _ =>
        Runs.then (runs_of_reads (Tail.reads_needs _ _)) fun _ =>
          shuts_stages fm ride (y :: rest) false

theorem shuts_iopp (l : List StageSize) (rows fm : Nat) (ride : Bool) :
    Shuts st (planIopp l rows fm ride) :=
  Runs.then (runs_of_reads (Tail.reads_needs _ _)) fun _ =>
    Runs.then (shuts_bat st _ _).runs fun _ => shuts_stages st fm ride l true

theorem shuts_seal : Shuts st planSeal := shuts_close st _ _ _ _

theorem shuts_linFirst (codes : Codes) (x : LinSized) : Shuts st (linPlanFirst codes x) :=
  Runs.then (runs_of_reads (reads_must _ _)) fun _ => shuts_send st _ _

/-- A routine that keeps a state At s 0 (OnBytes/Tie/Pv/Lay/PlanLook.lean) keeps an idle state. -/
theorem keeps_of_lay {x : Planning Unit} (h : Lay.Keeps st x) : Keeps st x :=
  fun p _ q hp hq => by
    obtain ⟨a, F, r⟩ := h p q ⟨hp.set, hp.scope, hp.bytes, hp.roots, hp.answers⟩ hq
    exact ⟨⟨a.set, a.scope, a.bytes, a.roots, a.answers⟩, F, r⟩

theorem shuts_batt (rows kCol : Nat) : Shuts st (planBatt rows kCol) :=
  Shuts.then (shuts_batSigma st rows) fun _ => keeps_of_lay st (Lay.keeps_psc st 0 _)

end Routines

end OnBytes.Tie.Pv.Req

#print axioms OnBytes.Tie.Pv.Req.runs_reqSend
#print axioms OnBytes.Tie.Pv.Req.shuts_reqSend
#print axioms OnBytes.Tie.Pv.Req.shuts_loc
#print axioms OnBytes.Tie.Pv.Req.shuts_bat
#print axioms OnBytes.Tie.Pv.Req.shuts_fold
#print axioms OnBytes.Tie.Pv.Req.shuts_iopp
#print axioms OnBytes.Tie.Pv.Req.shuts_batt
#print axioms OnBytes.Tie.Pv.Req.shuts_linFirst
#print axioms OnBytes.Tie.Pv.Req.shuts_seal
