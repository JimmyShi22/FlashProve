-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/Steps.lean: A CHAIN's ROUTINE WALKED IN PIECES: one closed test a
piece; a table of the states between the pieces; from these callsFrom's «one» at the whole routine.
Definitions and theorems. A law file; no running text imports it.
  `pieceB s truth st x`   with code: x is run FROM NO CALL AND NO ROUND at the small state st.1; its
                          rounds are held by
                  `sameAll` against as many of the written rounds `truth` from place st.2 on;
                  returns the small state at which it ends and the next place; none where x refuses
                  or a round differs.
  `seqN xs`       the pieces one behind the other.
  `Good s truth st y`   y, run so at st.1, returns, ends at counters 0, and its rounds are, by
                  `sameAll`, ALL the written rounds from place st.2 on.
  `good_of_table` a table `tab` with pieceB s truth (tab i) (xs[i]) = some (tab (i + 1)) for each i,
                  which ends at counters 0 and at truth's length: Good s truth (tab 0) (seqN xs).
  `oneAt`         the text of callsFrom's local «one»
                  (Johnson/Desc/First/Link/RowsRun.lean:165-173), by name.
  `one_of_good`   Good at ⟨scope,0,0,0⟩ and place 0, of a faithful routine: `oneAt` returns the
                  chain with
                  `noted`'s own calls: (k1) by the walk, (k2) by Faith.lean.
Limits. No closed fact is here. `sameAll` holds four of a round's fields (entry, error, why, scope),
as callsFrom's own test does. Nothing on soundness or on hiding.
-/
import Johnson.AtFull.Rows.Faith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

theorem sameAll_app : ∀ {a c b d : List PlanRound}, sameAll a c = true → sameAll b d = true →
    sameAll (a ++ b) (c ++ d) = true
  | [], [], _, _, _, h => h
  | x :: a, y :: c, b, d, h1, h2 => by
    simp only [sameAll, Bool.and_eq_true] at h1
    simp only [List.cons_append, sameAll, Bool.and_eq_true]
    exact ⟨h1.1, sameAll_app h1.2 h2⟩
  | [], _ :: _, _, _, h, _ => by simp [sameAll] at h
  | _ :: _, [], _, _, h, _ => by simp [sameAll] at h

/-- The closed test of a piece. -/
def pieceB (s : Setting) (truth : List PlanRound) (st : SmallSt × Nat) (x : N Unit) :
    Option (SmallSt × Nat) :=
  match (x.run #[]).run (st.1.plan s) with
  | .error _ => none
  | .ok (_, q) =>
    if sameAll q.rounds.toList ((truth.drop st.2).take q.rounds.size) then
      some (smallOf q, st.2 + q.rounds.size)
    else none

/-- The pieces one behind the other. -/
def seqN : List (N Unit) → N Unit
  | [] => pure ()
  | x :: xs => x >>= fun _ => seqN xs

/-- y returns, ends at counters 0, and has written all the written rounds from place st.2 on. -/
def Good (s : Setting) (truth : List PlanRound) (st : SmallSt × Nat) (y : N Unit) : Prop :=
  ∃ cs rs sc', RunsN s st.1 y () cs rs ⟨sc', 0, 0, 0⟩ ∧ sameAll rs.toList (truth.drop st.2) = true

theorem step_runs {s : Setting} {truth : List PlanRound} {st st' : SmallSt × Nat} {x : N Unit}
    (hx : Fr x) (h : pieceB s truth st x = some st') :
    ∃ cs rs, RunsN s st.1 x () cs rs st'.1 ∧ st'.2 = st.2 + rs.size ∧
      sameAll rs.toList ((truth.drop st.2).take rs.size) = true := by
  unfold pieceB at h
  cases e : (x.run #[]).run (st.1.plan s) with
  | error m =>
    rw [e] at h
    cases h
  | ok r =>
    obtain ⟨⟨u, cs⟩, q⟩ := r
    rw [e] at h
    dsimp only at h
    split at h
    · rename_i c
      cases h
      have hs : q.set = s := (hx _ _ _ _ _ e).1
      subst hs
      exact ⟨cs, q.rounds, e, rfl, c⟩
    · cases h

theorem good_nil {s : Setting} {truth : List PlanRound} {sc' : Scope} :
    Good s truth (⟨sc', 0, 0, 0⟩, truth.length) (seqN []) :=
  ⟨#[], #[], sc', rfl, by simp [sameAll]⟩

theorem good_cons {s : Setting} {truth : List PlanRound} {st st' : SmallSt × Nat} {x y : N Unit}
    (hx : Fr x) (hy : Fr y) (h : pieceB s truth st x = some st') (g : Good s truth st' y) :
    Good s truth st (x >>= fun _ => y) := by
  obtain ⟨cs, rs, hr, e2, hs⟩ := step_runs hx h
  obtain ⟨cs', rs', sc', hr', hs'⟩ := g
  refine ⟨cs ++ cs', rs ++ rs', sc', RunsN.bind hr hy hr', ?_⟩
  rw [e2] at hs'
  have e : truth.drop st.2 = (truth.drop st.2).take rs.size ++ truth.drop (st.2 + rs.size) := by
    rw [← List.drop_drop, List.take_append_drop]
  rw [e, Array.toList_append]
  exact sameAll_app hs hs'

theorem fr_seqN : ∀ {xs : List (N Unit)}, (∀ x ∈ xs, Fr x) → Fr (seqN xs)
  | [], _ => fr_pure _
  | x :: _, h => fr_bind (h x (List.mem_cons_self ..)) fun _ =>
      fr_seqN fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem faith_seqN : ∀ {xs : List (N Unit)}, (∀ x ∈ xs, Faith x) → Faith (seqN xs)
  | [], _ => faith_pure _
  | x :: _, h => faith_bind (h x (List.mem_cons_self ..)) fun _ =>
      faith_seqN fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- The walk from place k of the table on. -/
theorem good_from {s : Setting} {truth : List PlanRound} {sc' : Scope} (tab : Nat → SmallSt × Nat) :
    ∀ (xs : List (N Unit)) (k : Nat), (∀ x ∈ xs, Fr x) →
      (∀ i, i < xs.length →
        pieceB s truth (tab (k + i)) (xs.getD i (pure ())) = some (tab (k + i + 1))) →
      tab (k + xs.length) = (⟨sc', 0, 0, 0⟩, truth.length) → Good s truth (tab k) (seqN xs)
  | [], k, _, _, he => by
    rw [List.length_nil, Nat.add_zero] at he
    rw [he]
    exact good_nil
  | x :: xs, k, hf, h, he => by
    have h0 := h 0 (Nat.succ_pos _)
    rw [Nat.add_zero, List.getD_cons_zero] at h0
    refine good_cons (hf x (List.mem_cons_self ..))
      (fr_seqN fun y hy => hf y (List.mem_cons_of_mem _ hy)) h0 ?_
    refine good_from (sc' := sc') tab xs (k + 1) (fun y hy => hf y (List.mem_cons_of_mem _ hy))
        (fun i hi => ?_) ?_
    · have hi' := h (i + 1) (Nat.succ_lt_succ hi)
      rw [List.getD_cons_succ] at hi'
      have e : k + (i + 1) = k + 1 + i := by omega
      rw [e] at hi'
      exact hi'
    · have e : k + 1 + xs.length = k + (x :: xs).length := by
        rw [List.length_cons]
        omega
      rw [e]
      exact he

/-- **A table of the states between the pieces gives the walk.** -/
theorem good_of_table {s : Setting} {truth : List PlanRound} {sc' : Scope}
    (tab : Nat → SmallSt × Nat)
    (xs : List (N Unit)) (hf : ∀ x ∈ xs, Fr x)
    (h : ∀ i, i < xs.length → pieceB s truth (tab i) (xs.getD i (pure ())) = some (tab (i + 1)))
    (he : tab xs.length = (⟨sc', 0, 0, 0⟩, truth.length)) : Good s truth (tab 0) (seqN xs) := by
  refine good_from (sc' := sc') tab xs 0 hf (fun i hi => ?_) ?_
  · rw [Nat.zero_add]
    exact h i hi
  · rw [Nat.zero_add]
    exact he

/-- callsFrom's local «one», by name. -/
def oneAt (s : Setting) (file : String) (ch : Nat) (scope : Scope) (x : N Unit) (truth : Planned) :
    Except String Johnson.G.Chain := do
  let (calls, P) ← noted s scope x
  unless sameAll P.rounds truth.rounds do
    throw s!"(k1) fails at {file} {ch}: the plan written while the calls were noted differs"
  let Q ← replay s scope calls
  unless sameAll Q.rounds truth.rounds do
    throw s!"(k2) fails at {file} {ch}: the list of calls, replayed alone, gives another plan"
  pure ⟨file, ch, scope, calls⟩

/-- **From the walk to callsFrom's «one».** -/
theorem one_of_good {s : Setting} {file : String} {ch : Nat} {scope : Scope} {y : N Unit}
    {truth : Planned} (hy : Faith y) (g : Good s truth.rounds (⟨scope, 0, 0, 0⟩, 0) y) :
    ∃ calls P, noted s scope y = .ok (calls, P) ∧
      oneAt s file ch scope y truth = .ok ⟨file, ch, scope, calls⟩ := by
  obtain ⟨cs, rs, sc', hr, hs⟩ := g
  rw [List.drop_zero] at hs
  refine ⟨cs.toList, ⟨s, rs.toList⟩, noted_of_runs hr, ?_⟩
  unfold oneAt
  rw [noted_of_runs hr]
  simp only [bind, Except.bind]
  rw [replay_of_runs hy hr]
  simp only [hs]
  rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.good_cons
#print axioms VerifiableInference.Desc.LinkJoin.good_of_table
#print axioms VerifiableInference.Desc.LinkJoin.one_of_good
