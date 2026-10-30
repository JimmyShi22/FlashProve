-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/RunsStep.lean: kind K5: what each of the kind's four named runs does
to the first chain's record: nothing, or it marks the join's debt in the ledger as paid.

Main names:
  `joinF_fork`: the ledger that the lookup's joinF (Johnson/Desc/First/Look/LookClaims.lean) leaves
    is F.paid g.owedJoin.
  `StepIs s s'`: s' = s, or there are the ledger F and what the lookup heard g of s with s' =
    s.putFork (F.paid g.owedJoin).
  `named_ok` (private); `runsK_step`: over every seat, "first", "keys" and "second" (runsK,
    Johnson/Desc/First/Att/RunsK.lean) return the very record. `joinRun_step`: the run "join"
    (K3.joinRun at K3.seatCalls, Johnson/Desc/First/Look/K3Runs.lean). `with_join_step`.
  `runsW_step`, `runsH_step`: StepIs at every run of runsW A (Johnson/Desc/First/Att/SeatW.lean) and
    of runsH A (SeatH.lean) that returns.
For whom: laws that ask of every run of claims that it carries something from s to s': they follow
where that thing holds of (s, s) and of (s, s.putFork (F.paid i)).
Used: the runs spoken of are texts under Johnson/Desc/First: the kind's own three (Att/RunsK.lean,
over Att/RunsP.lean), the lists runsW and runsH, and the lookup's kind's K3.joinRun
(Look/K3Runs.lean) with Look.joinF, a function on a ledger and a tape (the type OnBytes.K.Kc.Fl):
both are unfolded. The statements name the record First.S, which holds the record type OnBytes.Run.
Of OnBytes and Johnson/Road no routine that runs in a context is named, and no theorem on such a
routine's return.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.SeatW
import Johnson.Desc.First.Att.SeatH
import Johnson.Desc.First.Att.Claims.PortJoin

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open OnBytes.K.Kc
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att

/-- The ledger that the lookup's joinF leaves: the debt of the join is marked as paid, and nothing else turns. -/
theorem joinF_fork {g : Forest.Heard} {KF : Array Aff} {F : Fork} {t : Tape} {x : Aff × Fork × Tape}
    (h : Look.joinF g KF F t = some x) : x.2.1 = F.paid g.owedJoin := by
  unfold Look.joinF at h
  simp only [bind, Fl.andThen, Fl.must, Look.joinAddedF, Look.paidF, Fl.change, pure, Fl.ret,
    Option.map_some] at h
  split at h
  · rename_i a G u hm
    split at hm
    · rename_i hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨_, e1, _⟩ := hm
      subst e1
      simp only [Option.some.injEq] at h
      rw [← h]
    · cases hm
  · cases h

/-- What a run of the kind does to the record: nothing, or it marks the join's debt in the ledger as paid. -/
def StepIs (s s' : First.S) : Prop :=
  s' = s ∨ ∃ F g, s.fork? = some F ∧ s.lookHeard? = some g ∧ s' = s.putFork (F.paid g.owedJoin)

private theorem named_ok {α : Type} {n : String} {x : Option α} {y : α} (h : named n x = .ok y) : x = some y := by
  cases x with
  | none => cases h
  | some a => exact congrArg some (Except.ok.inj h)

/-- The three runs of the kind's own return the very record. -/
theorem runsK_step {St : Type} (seat : P.SeatC St) (c : P.ParC) :
    ∀ r ∈ P.runsK seat c, ∀ n s y s', r.2 n s = .ok (y, s') → s' = s := by
  intro r hr n s y s' h
  unfold P.runsK at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have e := named_ok h
    unfold P.firstK at e
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e
    obtain ⟨_, _, _, _, r⟩ := e
    exact (Prod.mk.inj (Option.some.inj r)).2.symm
  · have e := named_ok h
    unfold P.keysK at e
    obtain ⟨_, _, r⟩ := Option.map_eq_some_iff.1 e
    exact (Prod.mk.inj r).2.symm
  · have e := named_ok h
    unfold P.secondK at e
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e
    obtain ⟨_, _, _, _, r⟩ := e
    exact (Prod.mk.inj (Option.some.inj r)).2.symm

/-- The lookup's run "join" at the calls' seat. -/
theorem joinRun_step (keys : First.S → Option (Array Aff)) (n : ℕ) (s : First.S) (y : List Aff) (s' : First.S)
    (h : K3.joinRun (K3.seatCalls (Cl := Aff) id) keys n s = .ok (y, s')) : StepIs s s' := by
  unfold K3.joinRun at h
  simp only [bind, Except.bind] at h
  cases hF : named "K3 join: no sub-proof is open" ((K3.seatCalls (Cl := Aff) id).fork s) with
  | error e => rw [hF] at h; cases h
  | ok F =>
    rw [hF] at h
    simp only at h
    cases hg : named "K3 join: nothing was heard" ((K3.seatCalls (Cl := Aff) id).heard s) with
    | error e => rw [hg] at h; cases h
    | ok g =>
      rw [hg] at h
      simp only at h
      cases hn : need "K3 join: it is made once" (K3.unpaid F g.owedJoin) with
      | error e => rw [hn] at h; cases h
      | ok _ =>
        rw [hn] at h
        simp only at h
        cases hk : named "K3 join: the caller's keys" (keys s) with
        | error e => rw [hk] at h; cases h
        | ok KF =>
          rw [hk] at h
          simp only at h
          cases hx : named "K3 join: one form and one weight a call" (First.Look.joinF g KF F []) with
          | error e => rw [hx] at h; cases h
          | ok x =>
            rw [hx] at h
            have e := (Prod.mk.inj (Except.ok.inj h)).2
            refine .inr ⟨F, g, named_ok hF, named_ok hg, ?_⟩
            rw [← e, ← joinF_fork (named_ok hx)]
            rfl

theorem with_join_step (rs : List (String × (ℕ → First.S → Except String (List Aff × First.S))))
    (keys : First.S → Option (Array Aff)) (hrs : ∀ r ∈ rs, ∀ n s y s', r.2 n s = .ok (y, s') → s' = s) :
    ∀ r ∈ rs.flatMap (fun r => if r.1 == "keys" then
        [r, ("join", K3.joinRun (K3.seatCalls (Cl := Aff) id) keys)] else [r]),
      ∀ n s y s', r.2 n s = .ok (y, s') → StepIs s s' := by
  intro r hr n s y s' h
  obtain ⟨r0, h0, hm⟩ := List.mem_flatMap.1 hr
  split at hm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact .inl (hrs _ h0 n s y s' h)
    · exact joinRun_step keys n s y s' h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    exact .inl (hrs _ h0 n s y s' h)

/-- **Every run of the kind's four, at either seat, leaves the record as it is or marks the join's debt as paid.** -/
theorem runsW_step (A : Attention.Plan) :
    ∀ r ∈ P.runsW A, ∀ n s y s', r.2 n s = .ok (y, s') → StepIs s s' :=
  with_join_step _ _ (runsK_step _ _)

theorem runsH_step (A : Attention.Plan) :
    ∀ r ∈ P.runsH A, ∀ n s y s', r.2 n s = .ok (y, s') → StepIs s s' :=
  with_join_step _ _ (runsK_step _ _)

end K5Law
