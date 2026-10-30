-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Flat/HeldAll.lean: every round of a plan that the planner hands out as held meets the
conditions of `held_round`, against the written rounds' data.

`held_round` (OnBytes/Slice/HeldRound.lean) and the theorems kind by kind behind it
(OnBytes/Slice/HeldKinds.lean and the files that import it) speak of one round r of a plan and one
written round d, under the record `Held s r d`. Here that record is shown for all rounds of a
chain at once, from what `finishHeld` hands out (`finishHeld_set`, OnBytes/Params/HoldsLaws.lean;
`finishHeld_holds`, OnBytes/Params/SizedForward.lean). `priced_of_plan`
(OnBytes/Slice/PricedRound.lean) is its like with a price in the record; here the count is left to
the caller, and the entry RECORD is passed over for every plan. Definitions, statements and
proofs.

Main names, all in the namespace `OnBytes.Flat.Held`:
  `sideB P`: a test on a finished plan, by evaluation: the setting has the format's field; in
    every round `logN` is at most 64, drawNZ is at most drawE, and work + 66 ≤ target if the round
    draws an element.
  `chainRounds P`: the plan's rounds without the entry under the name RECORD, which is no round of
    the chain (`Fmt.Plan.rounds`, Fmt/Rules4.lean). `Aligned ds P`: the written rounds' entries
    are theirs, one by one (the name and eleven numbers). Decidable.
  `aligned_of_spec`: `Aligned (rds S) P` for every description S of a chain whose rounds have the
    entries of its plan's rounds and whose plan is P's.
  `held_all`: if `finishHeld s scope x = .ok P`, `Aligned ds P` and `sideB P = true`, then `Held s
    r d` for each pair of a written round d and its round r of `chainRounds P`.

Limits: the routine x and the setting s are variables: a routine written for the purpose could
close the same entries at other errors. Where this is used, x should be the planner's own named
routine for the chain, at the numbers read from the public files, and s the setting that these
files give. Nothing on any count. Nothing on the entry RECORD.
-/
import OnBytes.Params.HoldsLaws
import OnBytes.Params.SizedForward
import OnBytes.Slice.HeldKinds
import Run.PlanQS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Flat.Held
open _root_.Run _root_.Run.PQ OnBytes.Params OnBytes.Slice

/-! ### The side conditions -/

/-- one round's side conditions, on its entry -/
def sideE (target : ℕ) (e : Fmt.Entry) : Bool :=
  decide (e.logN ≤ 64) && decide (e.drawNZ ≤ e.drawE) &&
    (e.drawE == 0 || decide (e.work + 66 ≤ target))

/-- one round's side conditions -/
def sideR (target : ℕ) (r : PlanRound) : Bool := sideE target r.entry

/-- The side conditions of `held_round`, on a finished plan. -/
def sideB (P : Planned) : Bool :=
  decide (P.set.p = 2 ^ 64 - 2 ^ 32 + 1) && decide (P.set.degree = 3) &&
    P.rounds.all (sideR P.set.target)

theorem held_list (s : Setting) (hp : s.p = 2 ^ 64 - 2 ^ 32 + 1) (hd : s.degree = 3) :
    ∀ (ds : List RD) (rs : List PlanRound), ds.map (·.entry) = rs.map (·.entry) →
      rs.all (sideR s.target) = true → rs.all (roundHolds s (capped s)) = true →
      List.Forall₂ (fun d r => Held s r d) ds rs
  | [], [], _, _, _ => .nil
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | d :: ds, r :: rs, h, h1, h2 => by
    have he : d.entry = r.entry ∧ ds.map (·.entry) = rs.map (·.entry) := by simpa using h
    have a1 := Bool.and_eq_true_iff.1 (by simpa [List.all_cons] using h1 :
      (sideR s.target r && rs.all (sideR s.target)) = true)
    have a2 := Bool.and_eq_true_iff.1 (by simpa [List.all_cons] using h2 :
      (roundHolds s (capped s) r && rs.all (roundHolds s (capped s))) = true)
    have b1 := Bool.and_eq_true_iff.1 a1.1
    have b2 := Bool.and_eq_true_iff.1 b1.1
    refine .cons ⟨hp, hd, he.1, of_decide_eq_true b2.1, of_decide_eq_true b2.2, ?_, a2.1⟩
      (held_list s hp hd ds rs he.2 a1.2 a2.2)
    intro hne
    rcases Bool.or_eq_true_iff.1 b1.2 with h0 | h0
    · exact absurd (by simpa using h0) hne
    · exact of_decide_eq_true h0

/-- A test that holds of all members of a list holds of all that a filter keeps. -/
theorem all_filter {α : Type} (p q : α → Bool) (l : List α) (h : l.all p = true) :
    (l.filter q).all p = true :=
  List.all_eq_true.2 fun x hx => List.all_eq_true.1 h x (List.mem_of_mem_filter hx)

/-! ### The rounds of the chain -/

/-- The plan's rounds that are rounds of the chain: the entry under the name RECORD is none
(`Fmt.Plan.rounds`, Fmt/Rules4.lean). -/
def chainRounds (P : Planned) : List PlanRound :=
  P.rounds.filter fun r => r.entry.name != Fmt.recordName

/-- The written rounds' entries are those of the plan's rounds of the chain, one by one. -/
def Aligned (ds : List RD) (P : Planned) : Prop :=
  ds.map (·.entry) = (chainRounds P).map (·.entry)

instance (ds : List RD) (P : Planned) : Decidable (Aligned ds P) :=
  inferInstanceAs (Decidable (_ = _))

theorem chainRounds_entries (P : Planned) : (chainRounds P).map (·.entry) = P.plan.rounds := by
  show (P.rounds.filter fun r => r.entry.name != Fmt.recordName).map (·.entry) =
    (P.rounds.map (·.entry)).filter fun e => e.name != Fmt.recordName
  rw [List.filter_map]
  rfl

theorem rdsFrom_entries (S : Fmt.Spec) : ∀ (n : ℕ) (rs : List Fmt.Round),
    (rdsFrom S n rs).map (·.entry) = rs.map (·.entry)
  | _, [] => rfl
  | n, r :: rs => congrArg (r.entry :: ·) (rdsFrom_entries S (n + r.entry.roots) rs)

/-- For every description of a chain whose rounds have the entries of its plan's rounds (a clause
of the format's test: `ok_entries`, Fmt/Rules8Ok.lean) and whose plan is the planner's. -/
theorem aligned_of_spec (S : Fmt.Spec) (P : Planned)
    (h1 : S.rounds.map (·.entry) = S.plan.rounds) (h2 : S.plan = P.plan) :
    Aligned (rds S) P := by
  unfold Aligned rds
  rw [rdsFrom_entries, h1, h2, chainRounds_entries]

/-- Every round of the chain, of a plan that is handed out as held, against its written round. -/
theorem held_all (s : Setting) (scope : Scope) (x : Planning Unit) (P : Planned)
    (h : finishHeld s scope x = .ok P) (ds : List RD) (ha : Aligned ds P)
    (hs : sideB P = true) : List.Forall₂ (fun d r => Held s r d) ds (chainRounds P) := by
  have hset := finishHeld_set h
  have c1 := Bool.and_eq_true_iff.1 hs
  have c2 := Bool.and_eq_true_iff.1 c1.1
  have hh := finishHeld_holds h
  unfold Planned.holds at hh
  have hr := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hh).1).1
  unfold Planned.roundsHold at hr
  rw [hset] at c1 c2 hr
  exact held_list s (of_decide_eq_true c2.1) (of_decide_eq_true c2.2) ds (chainRounds P) ha
    (all_filter _ _ _ c1.2) (all_filter _ _ _ hr)

end OnBytes.Flat.Held

#print axioms OnBytes.Flat.Held.held_all
#print axioms OnBytes.Flat.Held.aligned_of_spec
