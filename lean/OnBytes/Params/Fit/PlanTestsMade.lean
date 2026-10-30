-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/PlanTestsMade.lean: in the plans that the planner makes, the first chain of a key
and of a proof has two rounds at least, and the last round of the first and of the shared chain
asks for no work.

The routines that plan a key's one-time chain (OnBytes/Plan/KeyOneTime.lean, oneTimeRounds) and a
proof's first chain (OnBytes/Params/DeriveReq.lean, firstPlan) end in linPlanFirst and planSeal;
the routine of a shared chain (OnBytes/Params/DeriveLin.lean, sharedPlan) ends in planSeal.
linPlanFirst's last act adds the round "SEND answer"; planSeal adds the round "SEAL", whose bits
of work are the setting's for an error of the kind zero: 0 by definition
(OnBytes/Params/Setting.lean, workOf). What a routine has done before its last acts does not
matter: so nothing is asked of the sub-proofs' routines, which are letters of firstPlan.

Main definitions: EndsSeal (the last entry asks for no work); Ends (wherever a routine ends well,
the plan's rounds then meet a condition).
Main theorems: Ends.after, Ends.when, oneTime_tests, shared_tests, first_tests, planTests_made.

What is not claimed: anything on the plans as they are read back from the parameter bytes
(OnBytes/Model/Fit/PlanTestsPlanned.lean); that a plan is finished or holds: that is each theorem's
hypothesis. Nothing on soundness. For proofs only; the program does not import this file.


-/
import OnBytes.Plan.PlanListsProof

set_option autoImplicit false

namespace OnBytes.Params

/-- The last entry asks for no work. -/
def EndsSeal (e : List Fmt.Entry) : Prop := e.getLast?.map (·.work) = some 0

/-- Wherever the routine ends well, the plan's rounds then meet Q. -/
def Ends {α : Type} (y : Planning α) (Q : Array PlanRound → Prop) : Prop :=
  ∀ (p : PlanState) (v : α) (p' : PlanState), y p = .ok (v, p') → Q p'.rounds

/-- The last round has the name n. -/
def LastIs (n : String) (R : Array PlanRound) : Prop :=
  ∃ (q : Array PlanRound) (r : PlanRound), R = q.push r ∧ r.entry.name = n

/-- The last round is SEAL and asks for no work. -/
def LastSeal (R : Array PlanRound) : Prop :=
  ∃ (q : Array PlanRound) (r : PlanRound),
    R = q.push r ∧ r.entry.name = "SEAL" ∧ r.entry.work = 0

/-- The last two rounds are "SEND answer" and SEAL, and SEAL asks for no work. -/
def LastTwo (R : Array PlanRound) : Prop :=
  ∃ (q : Array PlanRound) (r₁ r₂ : PlanRound), R = (q.push r₁).push r₂ ∧
    r₁.entry.name = "SEND answer" ∧ r₂.entry.name = "SEAL" ∧ r₂.entry.work = 0

/-- Whatever stands before, one routine after another ends as the second ends. -/
theorem Ends.after {α β : Type} {x : Planning α} {f : α → Planning β}
    {Q : Array PlanRound → Prop} (h : ∀ a, Ends (f a) Q) : Ends (x >>= f) Q := by
  intro p v p' e
  obtain ⟨a, p1, _, e2⟩ := bind_ends e
  exact h a p1 v p' e2

/-- A routine that is run or left out, and what follows in both cases. -/
theorem Ends.when {β : Type} {P : Prop} [Decidable P] {x : Planning PUnit}
    {k : PUnit → Planning β} {Q : Array PlanRound → Prop} (h : ∀ a, Ends (k a) Q) :
    Ends (if P then x >>= k else pure PUnit.unit >>= k) Q := by
  by_cases hp : P
  · rw [if_pos hp]
    exact Ends.after h
  · rw [if_neg hp]
    exact Ends.after h

/-- What planSeal adds. -/
theorem seal_run {p p' : PlanState} {v : Unit} (h : planSeal p = .ok (v, p')) :
    ∃ r : PlanRound, p'.rounds = p.rounds.push r ∧ r.entry.name = "SEAL" ∧
      r.entry.work = 0 := by
  unfold planSeal at h
  rw [close_run] at h
  split at h
  · cases h
  · cases h
    exact ⟨_, rfl, rfl, rfl⟩

theorem ends_seal : Ends planSeal LastSeal := by
  intro p v p' h
  obtain ⟨r, e, n, w⟩ := seal_run h
  exact ⟨p.rounds, r, e, n, w⟩

theorem ends_closeNone (n : String) : Ends (closeNone n) (LastIs n) := by
  intro p v p' h
  unfold closeNone at h
  split at h
  · cases h
  · cases h
    exact ⟨p.rounds, _, rfl, rfl⟩

/-- SEND with the round of the answers ends in that round. -/
theorem ends_send (o : List SampleSize) (roots : Nat) :
    Ends (planSend o roots) (LastIs "SEND answer") := by
  unfold planSend
  rw [if_pos rfl]
  exact Ends.after fun _ => Ends.after fun _ => Ends.after fun _ => Ends.after fun _ =>
    Ends.after fun _ => ends_closeNone _

theorem ends_linPlanFirst (codes : Codes) (x : LinSized) :
    Ends (linPlanFirst codes x) (LastIs "SEND answer") := by
  unfold linPlanFirst
  refine Ends.after fun L => ?_
  unfold planLinFirst
  exact ends_send _ _

/-- A routine that ends in "SEND answer", and then planSeal. -/
theorem ends_two {y : Planning Unit} (h : Ends y (LastIs "SEND answer")) :
    Ends (y >>= fun _ => planSeal) LastTwo := by
  intro p v p' e
  obtain ⟨a, p1, e1, e2⟩ := bind_ends e
  obtain ⟨q, r₁, hq, n₁⟩ := h p a p1 e1
  obtain ⟨r₂, hr, n₂, w⟩ := seal_run e2
  exact ⟨q, r₁, r₂, by rw [hr, hq], n₁, n₂, w⟩

/-- A finished plan that holds has the rounds with which its routine ended. -/
theorem finishHeld_ends {s : Setting} {c : Scope} {x : Planning Unit}
    {Q : Array PlanRound → Prop} {P : Planned} (hx : Ends x Q)
    (h : finishHeld s c x = .ok P) : ∃ R : Array PlanRound, Q R ∧ P.rounds = R.toList := by
  unfold finishHeld at h
  cases hf : finish s c x with
  | error e =>
    rw [hf] at h
    cases h
  | ok P' =>
    rw [hf] at h
    have h' : (if P'.holds = true then (Except.ok P' : Except String Planned)
        else .error notAdmitted) = .ok P := h
    split at h'
    · cases h'
      unfold finish at hf
      split at hf
      · cases hf
      · rename_i u p hp
        split at hf
        · cases hf
        · cases hf
          exact ⟨p.rounds, hx _ u p hp, rfl⟩
    · cases h'

/-- The plan's rounds, where the made rounds end in SEAL. -/
theorem rounds_seal {P : Planned} {R : Array PlanRound} (hR : LastSeal R)
    (h : P.rounds = R.toList) : EndsSeal P.plan.rounds := by
  obtain ⟨q, r, rfl, n, w⟩ := hR
  have f : ([r.entry].filter fun e => e.name != Fmt.recordName) = [r.entry] := by
    rw [List.filter_cons_of_pos (by rw [n]; decide), List.filter_nil]
  show (((P.rounds.map (·.entry)).filter fun e => e.name != Fmt.recordName).getLast?.map
    (·.work)) = some 0
  rw [h, Array.toList_push, List.map_append, List.filter_append]
  show ((_ ++ [r.entry].filter _).getLast?.map (·.work)) = some 0
  rw [f, List.getLast?_concat, Option.map_some, w]

/-- The plan's rounds, where the made rounds end in "SEND answer" and SEAL. -/
theorem rounds_two {P : Planned} {R : Array PlanRound} (hR : LastTwo R)
    (h : P.rounds = R.toList) : 2 ≤ P.plan.rounds.length ∧ EndsSeal P.plan.rounds := by
  obtain ⟨q, r₁, r₂, rfl, n₁, n₂, w⟩ := hR
  refine ⟨?_, rounds_seal ⟨q.push r₁, r₂, rfl, n₂, w⟩ h⟩
  have f₁ : ([r₁.entry].filter fun e => e.name != Fmt.recordName) = [r₁.entry] := by
    rw [List.filter_cons_of_pos (by rw [n₁]; decide), List.filter_nil]
  have f₂ : ([r₂.entry].filter fun e => e.name != Fmt.recordName) = [r₂.entry] := by
    rw [List.filter_cons_of_pos (by rw [n₂]; decide), List.filter_nil]
  show 2 ≤ ((P.rounds.map (·.entry)).filter fun e => e.name != Fmt.recordName).length
  rw [h, Array.toList_push, Array.toList_push, List.map_append, List.map_append,
    List.filter_append, List.filter_append]
  show 2 ≤ ((_ ++ [r₁.entry].filter _) ++ [r₂.entry].filter _).length
  rw [f₁, f₂, List.length_append, List.length_append, List.length_singleton,
    List.length_singleton]
  omega

/-- The plan of a key's one-time chain. -/
theorem oneTime_tests {z : Plan.KeySized} {P : Planned} (h : Plan.oneTimePlan z = .ok P) :
    2 ≤ P.plan.rounds.length ∧ EndsSeal P.plan.rounds := by
  unfold Plan.oneTimePlan at h
  have e : Ends (Plan.oneTimeRounds z) LastTwo := by
    unfold Plan.oneTimeRounds
    exact Ends.after fun _ => Ends.after fun _ => Ends.after fun _ =>
      ends_two (ends_linPlanFirst _ _)
  obtain ⟨R, hR, hP⟩ := finishHeld_ends e h
  exact rounds_two hR hP

/-- The plan of a shared chain. -/
theorem shared_tests {s : Setting} {codes : Codes} {x : LinSized} {P : Planned}
    (h : sharedPlan s codes x = .ok P) : EndsSeal P.plan.rounds := by
  unfold sharedPlan at h
  obtain ⟨R, hR, hP⟩ := finishHeld_ends (Ends.after fun _ => ends_seal) h
  exact rounds_seal hR hP

/-- The plan of a proof's first chain, for all routines of the sub-proofs. -/
theorem first_tests {z : ProofSized} {sub : Subproofs} {P : Planned}
    (h : firstPlan z sub = .ok P) : 2 ≤ P.plan.rounds.length ∧ EndsSeal P.plan.rounds := by
  have e : Ends (do
      reqPlan z sub
      sub.afterLinks
      modify fun p => { p with scope := .request }
      if 1 < sub.pendingRows then planBatt sub.pendingRows z.batch.shape.kCol
      linPlanFirst z.codes z.batch
      planSeal : Planning Unit) LastTwo := by
    refine Ends.after fun _ => Ends.after fun _ => Ends.after fun _ => ?_
    exact Ends.when fun _ => ends_two (ends_linPlanFirst _ _)
  obtain ⟨R, hR, hP⟩ := finishHeld_ends e h
  exact rounds_two hR hP

/-- **From the planner's yes: the tests on the made plans of a key and of a proof.** hk and hp
only name the members of the two lists of made plans. -/
theorem planTests_made {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (h : configure l x cfg bits = .ok made) {K1 K2 K3 F S2 S3 : Planned}
    (hk : made.key = [K1, K2, K3]) (hp : made.proof = [F, S2, S3]) :
    (2 ≤ K1.plan.rounds.length ∧ EndsSeal K1.plan.rounds ∧ EndsSeal K2.plan.rounds) ∧
      (2 ≤ F.plan.rounds.length ∧ EndsSeal F.plan.rounds ∧ EndsSeal S2.plan.rounds) := by
  obtain ⟨_, _, P1, P2, P3, ek, h1, h2, _, _⟩ := configure_plans h
  obtain ⟨G, T2, T3, ep, g1, g2, _⟩ := configure_proofPlans h
  rw [hk] at ek
  rw [hp] at ep
  obtain ⟨rfl, rfl, rfl⟩ : K1 = P1 ∧ K2 = P2 ∧ K3 = P3 := by simpa using ek
  obtain ⟨rfl, rfl, rfl⟩ : F = G ∧ S2 = T2 ∧ S3 = T3 := by simpa using ep
  exact ⟨⟨(oneTime_tests h1).1, (oneTime_tests h1).2, shared_tests h2⟩,
    (first_tests g1).1, (first_tests g1).2, shared_tests g2⟩

end OnBytes.Params
