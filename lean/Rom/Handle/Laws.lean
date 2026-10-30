-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Handle/Laws.lean: the laws of the run of an oracle algorithm under any rule for answering its
queries (Rom/Handle/Defs.lean). General in the family of oracles.

General lemmas. This file states no goal of the release.

  interp_bind          The run of "c, then g" is the run of c, then that of g from c's last state.
  interp_lazy          Under lazy sampling the run is runLazy (Rom/OComp.lean).
  interp_map_state     A map of states that commutes with two rules' moves commutes with the runs.
  interp_sample_comm   A draw before an algorithm, or after it: the same run, under any rule.
  interp_defer_shift, interp_replay_shift   Entries that stand in the log at the start stay at its
                       head and change nothing else.
  lay_append, lay_of_some   Writing two logs one after the other; an entry that stands is kept.
  InStep.bind, InStep.mono   How "in step" is shown for algorithms made of parts.
  replay_of_inStep     **First a run that keeps its answers, then a replay.** If c and c' ask their
                       deferred queries in step, and c's output is a function φ of c' 's, then: keep
                       the answers of a run of c, and replay them at c'. The joint law of (c's
                       output, the recorded answers, the replay) is that of ONE run of c' with fresh
                       answers, of which φ of the output and the log's answers are read off. The
                       replay uses the list up and misses nothing.
  record_runReplay     The same for the dry run and for a replay with a table and a log.
Sources. interp_map_state has the form of interact_lump (Compile/Step1_defc_Gen.lean): a map of
states that commutes with the moves; there for an adversary and with an invariant, here for an
oracle algorithm and without one.

-/
import Rom.Handle.Defs
import Prob.Count

set_option autoImplicit false

noncomputable section

namespace Rom
open Prob
variable {S : OSpec} {σ τ α β γ : Type}

/-! ## The rules, at a query of either kind -/

namespace Handler
variable {mk : Mark S} {o : S.ι} {q : S.Dom o}

theorem defer_of_mark (h : Handler S σ) (hm : mk o q = true) (b : σ) (l : Trace S) :
    defer mk h (b, l) o q = (unif (S.Rng o)).map fun r => (r, (b, l ++ [⟨o, q, r⟩])) :=
  if_pos hm

theorem defer_of_not (h : Handler S σ) (hm : mk o q = false) (b : σ) (l : Trace S) :
    defer mk h (b, l) o q = (h b o q).map fun p => (p.1, (p.2, l)) :=
  if_neg (by rw [hm]; exact Bool.false_ne_true)

theorem replay_of_mark (h : Handler S σ) (hm : mk o q = true) (b : σ) (l : Trace S) (R : Record S)
    (m : Bool) :
    replay mk h ⟨b, l, R, m⟩ o q = (Record.next o R).map fun p =>
      (p.1, ⟨b, l ++ [⟨o, q, p.1⟩], p.2.1, m || p.2.2⟩) :=
  if_pos hm

theorem replay_of_not (h : Handler S σ) (hm : mk o q = false) (b : σ) (l : Trace S) (R : Record S)
    (m : Bool) :
    replay mk h ⟨b, l, R, m⟩ o q = (h b o q).map fun p => (p.1, ⟨p.2, l, R, m⟩) :=
  if_neg (by rw [hm]; exact Bool.false_ne_true)

end Handler

theorem Record.next_self (o : S.ι) (r : S.Rng o) (R : Record S) :
    Record.next o (⟨o, r⟩ :: R) = PMF.pure (r, R, false) :=
  dif_pos rfl

theorem Trace.answers_nil : Trace.answers ([] : Trace S) = [] := rfl

theorem Trace.answers_cons (e : QA S) (l : Trace S) :
    Trace.answers (e :: l) = ⟨e.1, e.2.2⟩ :: Trace.answers l := rfl

theorem Trace.answers_append (l l' : Trace S) :
    Trace.answers (l ++ l') = Trace.answers l ++ Trace.answers l' :=
  List.map_append

/-! ## Runs -/

namespace OComp

theorem interp_pure (h : Handler S σ) (a : α) (s : σ) :
    (OComp.pure a : OComp S α).interp h s = PMF.pure (a, s) := rfl

theorem interp_query (h : Handler S σ) (o : S.ι) (q : S.Dom o) (k : S.Rng o → OComp S α) (s : σ) :
    (OComp.query o q k).interp h s = (h s o q).bind fun p => (k p.1).interp h p.2 := rfl

theorem interp_sample (h : Handler S σ) (n : ℕ) (k : Fin (n + 1) → OComp S α) (s : σ) :
    (OComp.sample n k).interp h s = (unif (Fin (n + 1))).bind fun r => (k r).interp h s := rfl

/-- The run of "c, then g" is the run of c, then the run of g from c's last state. -/
theorem interp_bind (h : Handler S σ) (c : OComp S α) (g : α → OComp S β) :
    ∀ s, (c.bind g).interp h s = (c.interp h s).bind fun p => (g p.1).interp h p.2 := by
  induction c with
  | pure a =>
    intro s
    simp only [OComp.bind, interp, PMF.pure_bind]
  | query o q k ih =>
    intro s
    simp only [OComp.bind, interp, PMF.bind_bind, ih]
  | sample n k ih =>
    intro s
    simp only [OComp.bind, interp, PMF.bind_bind, ih]

/-- The same, for the Monad instance's notation. -/
theorem interp_bind' (h : Handler S σ) (c : OComp S α) (g : α → OComp S β) (s : σ) :
    (c >>= g).interp h s = (c.interp h s).bind fun p => (g p.1).interp h p.2 :=
  interp_bind h c g s

/-- Under lazy sampling the run is runLazy. -/
theorem interp_lazy (c : OComp S α) : ∀ T, c.interp Handler.lazy T = c.runLazy T := by
  induction c with
  | pure a =>
    intro T
    rfl
  | query o q k ih =>
    intro T
    cases hT : T o q with
    | none =>
      simp only [interp, Handler.lazy, lazyAnswer, runLazy, hT, PMF.bind_map, Function.comp_def, ih]
    | some r =>
      simp only [interp, Handler.lazy, lazyAnswer, runLazy, hT, PMF.pure_bind, ih]
  | sample n k ih =>
    intro T
    simp only [interp, runLazy, ih]

/-- A map of states that commutes with the moves of two rules commutes with the runs. -/
theorem interp_map_state (h : Handler S σ) (h' : Handler S τ) (φ : σ → τ)
    (hφ : ∀ s o q, (h s o q).map (fun p => (p.1, φ p.2)) = h' (φ s) o q) (c : OComp S α) :
    ∀ s, (c.interp h s).map (fun x => (x.1, φ x.2)) = c.interp h' (φ s) := by
  induction c with
  | pure a =>
    intro s
    simp only [interp, PMF.pure_map]
  | query o q k ih =>
    intro s
    simp only [interp, PMF.map_bind, ih]
    rw [← hφ, PMF.bind_map]
    rfl
  | sample n k ih =>
    intro s
    simp only [interp, PMF.map_bind, ih]

/-- A draw before an algorithm, or after it: the same run, under any rule. -/
theorem interp_sample_comm (h : Handler S σ) (n : ℕ) (c : OComp S α)
    (g : Fin (n + 1) → α → OComp S β) (s : σ) :
    (OComp.sample n fun r => c.bind (g r)).interp h s =
      (c.bind fun a => OComp.sample n fun r => g r a).interp h s := by
  simp only [interp_sample, interp_bind]
  exact PMF.bind_comm _ _ _

/-- Entries that stand in the log at the start stay at its head and change nothing else. -/
theorem interp_defer_shift (mk : Mark S) (h : Handler S σ) (c : OComp S α) (s : σ)
    (l l' : Trace S) :
    c.interp (Handler.defer mk h) (s, l ++ l') =
      (c.interp (Handler.defer mk h) (s, l')).map fun x => (x.1, (x.2.1, l ++ x.2.2)) := by
  refine (interp_map_state (Handler.defer mk h) (Handler.defer mk h)
    (fun s => (s.1, l ++ s.2)) ?_ c (s, l')).symm
  rintro ⟨b, l₀⟩ o q
  cases hm : mk o q with
  | false =>
    simp only [Handler.defer_of_not h hm, PMF.map_comp, Function.comp_def]
  | true =>
    simp only [Handler.defer_of_mark h hm, PMF.map_comp, Function.comp_def, List.append_assoc]

theorem interp_defer_cons (mk : Mark S) (h : Handler S σ) (c : OComp S α) (s : σ) (e : QA S)
    (l : Trace S) :
    c.interp (Handler.defer mk h) (s, e :: l) =
      (c.interp (Handler.defer mk h) (s, l)).map fun x => (x.1, (x.2.1, e :: x.2.2)) :=
  interp_defer_shift mk h c s [e] l

/-- The same for a replay. -/
theorem interp_replay_shift (mk : Mark S) (h : Handler S σ) (c : OComp S α) (b : σ)
    (l l' : Trace S) (R : Record S) (m : Bool) :
    c.interp (Handler.replay mk h) ⟨b, l ++ l', R, m⟩ =
      (c.interp (Handler.replay mk h) ⟨b, l', R, m⟩).map fun y =>
        (y.1, ⟨y.2.base, l ++ y.2.log, y.2.left, y.2.miss⟩) := by
  refine (interp_map_state (Handler.replay mk h) (Handler.replay mk h)
    (fun s => ⟨s.base, l ++ s.log, s.left, s.miss⟩) ?_ c ⟨b, l', R, m⟩).symm
  rintro ⟨b₀, l₀, R₀, m₀⟩ o q
  cases hm : mk o q with
  | false =>
    simp only [Handler.replay_of_not h hm, PMF.map_comp, Function.comp_def]
  | true =>
    simp only [Handler.replay_of_mark h hm, PMF.map_comp, Function.comp_def, List.append_assoc]

theorem interp_replay_cons (mk : Mark S) (h : Handler S σ) (c : OComp S α) (b : σ) (e : QA S)
    (l : Trace S) (R : Record S) (m : Bool) :
    c.interp (Handler.replay mk h) ⟨b, e :: l, R, m⟩ =
      (c.interp (Handler.replay mk h) ⟨b, l, R, m⟩).map fun y =>
        (y.1, ⟨y.2.base, e :: y.2.log, y.2.left, y.2.miss⟩) :=
  interp_replay_shift mk h c b [e] l R m

end OComp

/-! ## Writing where there is no entry -/

namespace Table

theorem lay1_of_none {T : Table S} {o : S.ι} {q : S.Dom o} (h : T o q = none) (r : S.Rng o) :
    T.lay1 o q r = T.set o q r := by
  simp only [lay1, h]

theorem lay1_of_some {T : Table S} {o : S.ι} {q : S.Dom o} {r' : S.Rng o} (h : T o q = some r')
    (r : S.Rng o) : T.lay1 o q r = T := by
  simp only [lay1, h]

theorem lay_nil (T : Table S) : T.lay [] = T := rfl

theorem lay_cons (T : Table S) (e : QA S) (l : Trace S) :
    T.lay (e :: l) = (T.lay1 e.1 e.2.1 e.2.2).lay l := rfl

theorem lay_append (l l' : Trace S) : ∀ T : Table S, T.lay (l ++ l') = (T.lay l).lay l' := by
  induction l with
  | nil =>
    intro T
    rfl
  | cons e l ih =>
    intro T
    exact ih _

/-- One write where there is no entry keeps every entry that stands. -/
theorem lay1_keeps {T : Table S} {o' : S.ι} {q' : S.Dom o'} {r' : S.Rng o'}
    (h : T o' q' = some r') (o : S.ι) (q : S.Dom o) (r : S.Rng o) :
    T.lay1 o q r o' q' = some r' := by
  cases hT : T o q with
  | some r₀ => rw [lay1_of_some hT]; exact h
  | none =>
    rw [lay1_of_none hT]
    by_cases ho : o' = o
    · subst ho
      by_cases hq : q' = q
      · subst hq
        rw [hT] at h
        exact absurd h (by simp)
      · simp only [Table.set, Function.update_self, Function.update_of_ne hq]
        exact h
    · simp only [Table.set, Function.update_of_ne ho]
      exact h

/-- Writing a log keeps every entry that stands. -/
theorem lay_of_some (l : Trace S) : ∀ {T : Table S} {o : S.ι} {q : S.Dom o} {r : S.Rng o},
    T o q = some r → T.lay l o q = some r := by
  induction l with
  | nil =>
    intro T o q r h
    exact h
  | cons e l ih =>
    intro T o q r h
    exact ih (lay1_keeps h _ _ _)

end Table

/-! ## In step -/

namespace InStep
variable {mk : Mark S} {R : α → β → Prop} {α' β' : Type}

/-- A weaker relation on the outputs. -/
theorem mono {R' : α → β → Prop} (hR : ∀ a b, R a b → R' a b) {c : OComp S α} {c' : OComp S β}
    (hc : InStep mk R c c') : InStep mk R' c c' := by
  induction hc with
  | done hab => exact .done (hR _ _ hab)
  | drawL _ ih => exact .drawL ih
  | drawR _ ih => exact .drawR ih
  | plainL hm _ ih => exact .plainL hm ih
  | plainR hm _ ih => exact .plainR hm ih
  | both hm hm' _ ih => exact .both hm hm' ih

/-- Two algorithms made of parts that are in step are in step. -/
theorem bind {R' : α' → β' → Prop} {c : OComp S α} {c' : OComp S β} {g : α → OComp S α'}
    {g' : β → OComp S β'} (hc : InStep mk R c c')
    (hg : ∀ a b, R a b → InStep mk R' (g a) (g' b)) : InStep mk R' (c.bind g) (c'.bind g') := by
  induction hc with
  | done hab => exact hg _ _ hab
  | drawL _ ih => exact .drawL ih
  | drawR _ ih => exact .drawR ih
  | plainL hm _ ih => exact .plainL hm ih
  | plainR hm _ ih => exact .plainR hm ih
  | both hm hm' _ ih => exact .both hm hm' ih

end InStep

/-! ## First a run that keeps its answers, then a replay -/

namespace OComp

/-- **First a run that keeps its answers, then a replay.** c and c' ask their deferred queries in
step, and c's output is φ of c' 's. Then the answers recorded in a run of c, replayed at c', give
jointly what one run of c' with fresh answers gives: they are the list of the answers in that run's
log. h, h': the rules for the other queries, in the two runs. -/
theorem replay_of_inStep {mk : Mark S} {R : α → β → Prop} {φ : β → α}
    (hR : ∀ a b, R a b → a = φ b) (h : Handler S σ) (h' : Handler S τ)
    {c : OComp S α} {c' : OComp S β} (hc : InStep mk R c c') : ∀ (s : σ) (s' : τ),
    ((c.interp (Handler.defer mk h) (s, [])).bind fun x =>
      (c'.interp (Handler.replay mk h') ⟨s', [], x.2.2.answers, false⟩).map fun y =>
        ((x.1, x.2.2.answers), y)) =
    (c'.interp (Handler.defer mk h') (s', [])).map fun y =>
      ((φ y.1, y.2.2.answers), (y.1, (⟨y.2.1, y.2.2, [], false⟩ : RSt S τ))) := by
  induction hc with
  | done hab =>
    intro s s'
    simp only [interp, PMF.pure_bind, PMF.pure_map, Trace.answers_nil]
    rw [hR _ _ hab]
  | drawL _ ih =>
    intro s s'
    simp only [interp_sample, PMF.bind_bind, ih, PMF.bind_const]
  | drawR _ ih =>
    intro s s'
    simp only [interp_sample, PMF.map_bind]
    rw [PMF.bind_comm]
    simp only [ih]
  | plainL hm _ ih =>
    intro s s'
    simp only [interp_query, Handler.defer_of_not h hm, PMF.bind_bind, PMF.bind_map,
      Function.comp_def, ih, PMF.bind_const]
  | plainR hm _ ih =>
    intro s s'
    simp only [interp_query, Handler.defer_of_not h' hm, Handler.replay_of_not h' hm, PMF.bind_map,
      Function.comp_def, PMF.map_bind]
    rw [PMF.bind_comm]
    simp only [ih]
  | @both o q q' k k' hm hm' _ ih =>
    intro s s'
    simp only [interp_query, Handler.defer_of_mark h hm, Handler.defer_of_mark h' hm',
      PMF.bind_map, Function.comp_def, List.nil_append, interp_defer_cons, PMF.bind_bind,
      PMF.map_bind, PMF.map_comp, Trace.answers_cons, Handler.replay_of_mark h' hm',
      Record.next_self, PMF.pure_map, PMF.pure_bind, Bool.or_false, interp_replay_cons]
    refine congrArg _ (funext fun r => ?_)
    have e := congrArg (PMF.map fun z : (α × Record S) × β × RSt S τ =>
      (((z.1.1, ⟨o, r⟩ :: z.1.2), (z.2.1, ⟨z.2.2.base, ⟨o, q', r⟩ :: z.2.2.log, z.2.2.left,
        z.2.2.miss⟩)) : (α × Record S) × β × RSt S τ)) (ih r s s')
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at e
    exact e

/-- **The dry run's recorded answers, replayed with a table and a log.** -/
theorem record_runReplay {mk : Mark S} {R : α → β → Prop} {φ : β → α}
    (hR : ∀ a b, R a b → a = φ b) {c : OComp S α} {c' : OComp S β} (hc : InStep mk R c c')
    (T : Table S) (lg : Trace S) :
    ((c.record mk).bind fun x => (c'.runReplay mk T lg x.2).map fun y => (x, y)) =
    (c'.runDefer mk T []).map fun y =>
      ((φ y.1, y.2.2.answers), (y.1, (⟨y.2.1, lg ++ y.2.2, [], false⟩ : RSt S (Table S)))) := by
  have e := congrArg (PMF.map fun z : (α × Record S) × β × RSt S (Table S) =>
    ((z.1, (z.2.1, ⟨z.2.2.base, lg ++ z.2.2.log, z.2.2.left, z.2.2.miss⟩)) :
      (α × Record S) × β × RSt S (Table S)))
    (replay_of_inStep hR Handler.idle Handler.lazy hc () T)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at e
  have e' : ∀ Rc : Record S, c'.runReplay mk T lg Rc =
      (c'.interp (Handler.replay mk Handler.lazy) ⟨T, [], Rc, false⟩).map fun y =>
        (y.1, ⟨y.2.base, lg ++ y.2.log, y.2.left, y.2.miss⟩) := fun Rc => by
    have := interp_replay_shift mk Handler.lazy c' T lg [] Rc false
    rwa [List.append_nil] at this
  simp only [record, runDefer, e', PMF.bind_map, Function.comp_def, PMF.map_comp]
  exact e

end OComp
end Rom

#print axioms Rom.OComp.interp_defer_shift
#print axioms Rom.OComp.replay_of_inStep
#print axioms Rom.OComp.record_runReplay
