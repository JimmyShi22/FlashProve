-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/TwoLanes.lean: two lanes in one bad event under one bound: two protocols
at two tags.

This file belongs to the second form of the verifier's side of the library's compiler under
OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`). What that form is, and in which five respects it differs
from the library's own, is told in the head of OnBytes/TypedOracleCompiler/Iop/BatchWire.lean. The folder has the
verifier's side alone: no prover and no completeness. Nothing here is on hiding. The library has no
file of this name.

Why. `bcsSoundBatchG` (Sound.lean; its conclusion is `BcsAt`, SpecSoundG.lean) carries three lanes
in one event under one t · εs, but at three fixed state functions and languages. Here is the same at
any two lanes with different tags: for example a protocol at Batch, and beside it, at the
interface's Test, a protocol whose state says that a drawn value is bad.

  `step2`, `Bad2`
      The entry causes the state event of one of the two lanes; `Bad2` is `EM` or `EF` or that.
  `pr_step2_le`
      The bound for one query: a query belongs to one tag only: εs once, not twice (after
      `pr_stepS_le`).
  `bad2_rare`
      Pr[`Bad2`] ≤ t · εs + 2 (t + 1)² / 2^lam, for every algorithm with at most t queries: the form
      of the first clause of `BcsAt`. The second lane adds no summand; but εs must lie above both
      lanes' errors (`Err.Below` at each): a maximum: where the second lane has the larger error a
      query, that one is paid at every query.
  `bad2_mono`
      `Bad2` is never undone.
  `not_bad2`
      Outside `Bad2`: not `EM`, not `EF`, neither lane's step event.
  `twice`, `OneAns`, `step3`, `Bad3`, `bad3_rare`, `bad3_mono`, `not_bad3`
      "One query, two answers" as a third disjunct, with the same bound to the letter (a true log
      never does it: `pr_stepEvent_le` asks its bound only at queries never asked). Outside `Bad3`
      each query of the list has one answer (`OneAns`): so two runs of one chain in it yield the
      same verifier messages.

How it is meant to be used; no one statement here says it. Outside `Bad3`, by `not_bad3`:
`mem_off_ours` (SoundOurs.lean) at the first lane gives `extS tr cms ≠ s ∨ Lg (a, s) (extY tr cms)`;
`no_coll` (LaneStays.lean) at the second gives `bad (extY₂ tr cms₂) ρ = false`. `OneAns` can also be
had from "every entry is a family's answer" (not proved in this folder).

Limits. `bad3_rare` gives t times the larger of the two lanes' errors, with t the number of queries
after any wrapping of the algorithm; a finer count, (names asked + 1) times the second lane's error,
is not here. Not said: that `extY` and `extY₂` are one string; any protocol, `bad` or reading; the
lanes' laws (hypotheses here: `lane_off_ok`, `laneOf_ok`); anything that makes the two hypotheses of
stability true (`hstab` of `mem_off_ours` and of `no_coll`): they stand as hypotheses.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.LaneStays

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L}

/-- the entry e, after the trace pre, causes the state event of one of two lanes -/
def step2 (ℓ₁ ℓ₂ : Lane W) (pre : Tc W) (e : QA (typedOracleFamily lam W.K L)) : Prop :=
    ℓ₁.step pre e ∨ ℓ₂.step pre e

def Bad2 (ℓ₁ ℓ₂ : Lane W) (tr : Tc W) : Prop := (EM tr ∨ EF tr) ∨ StepEvent (step2 ℓ₁ ℓ₂) tr

/-- The bound for one query, for two lanes with different tags: a query belongs to one tag only. -/
theorem pr_step2_le {ℓ₁ ℓ₂ : Lane W} (hne : ℓ₁.t ≠ ℓ₂.t) {N₁ N₂ : ℕ} (hN₁ : N₁ = 2 ^ W.dReq ℓ₁.t)
    (hN₂ : N₂ = 2 ^ W.dReq ℓ₂.t) (o₁ : ℓ₁.OK N₁)
    (o₂ : ℓ₂.OK N₂) {εs : ℝ≥0∞} (b₁ : Err.Below ℓ₁.ε εs) (b₂ : Err.Below ℓ₂.ε εs)
        (pre : Tc W) (o : OracleName)
    (q : domOf lam L o) :
    pr (unif ((typedOracleFamily lam W.K L).Rng o)) {r | step2 ℓ₁ ℓ₂ pre
                     (⟨o, q, r⟩ : QA (typedOracleFamily lam W.K L))} ≤ εs := by
  by_cases h1 : o = OracleName.fb ℓ₁.t
  · subst h1
    refine le_trans (pr_mono _ ?_) (Lane.pr_step_le ℓ₁ hN₁ o₁ b₁ pre q)
    rintro r (h | h)
    · exact h
    · exact absurd (OracleName.fb.inj (Lane.step_oracle h)) hne
  · by_cases h2 : o = OracleName.fb ℓ₂.t
    · subst h2
      refine le_trans (pr_mono _ ?_) (Lane.pr_step_le ℓ₂ hN₂ o₂ b₂ pre q)
      rintro r (h | h)
      · exact absurd (Lane.step_oracle h) h1
      · exact h
    · refine le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)) (zero_le _)
      rintro r - (h | h)
      · exact h1 (Lane.step_oracle h)
      · exact h2 (Lane.step_oracle h)

/-- Bad2 is rare, in the form of the first clause of `BcsAt`: the second lane adds no summand; εs
lies above both lanes' errors: a maximum. -/
theorem bad2_rare {ℓ₁ ℓ₂ : Lane W} (hne : ℓ₁.t ≠ ℓ₂.t) {N₁ N₂ : ℕ} (hN₁ : N₁ = 2 ^ W.dReq ℓ₁.t)
    (hN₂ : N₂ = 2 ^ W.dReq ℓ₂.t) (o₁ : ℓ₁.OK N₁)
    (o₂ : ℓ₂.OK N₂) {εs : ℝ≥0∞} (b₁ : Err.Below ℓ₁.ε εs) (b₂ : Err.Below ℓ₂.ε εs)
    (β : Type) (A : TypedOracleComputation lam W.K L β) (t : ℕ) (hA : A.QueryBound t) :
    pr A.withTrace.law {o | Bad2 ℓ₁ ℓ₂ o.2} ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2
        / 2 ^ lam := by
  have h := pr_stepEvent_le (S := typedOracleFamily lam W.K L) (step2 ℓ₁ ℓ₂) (fun _ => εs)
    (fun pre e he hs => hs.elim (fun h1 => h1.1 he) fun h1 => h1.1 he)
    (fun pre o q _ => pr_step2_le hne hN₁ hN₂ o₁ o₂ b₁ b₂ pre o q) A t hA
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  calc
    pr A.withTrace.law {o | (EM o.2 ∨ EF o.2) ∨ StepEvent (step2 ℓ₁ ℓ₂) o.2} ≤
        pr A.withTrace.law {o | EM o.2 ∨ EF o.2} + pr A.withTrace.law
            {o | StepEvent (step2 ℓ₁ ℓ₂) o.2} :=
      pr_union_le _ _ _
    _ ≤ 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam + (t : ℝ≥0∞) * εs := add_le_add (hashEvents A t hA) h
    _ ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
        rw [add_comm]
        gcongr
        exact Nat.le_succ t

theorem bad2_mono {ℓ₁ ℓ₂ : Lane W} (tr tr' : Tc W) : Bad2 ℓ₁ ℓ₂ tr → Bad2 ℓ₁ ℓ₂ (tr ++ tr') := by
  rintro ((h | h) | h)
  · exact Or.inl (Or.inl (h.append tr'))
  · exact Or.inl (Or.inr (h.append tr'))
  · exact Or.inr (StepEvent.append h tr')

theorem not_bad2 {ℓ₁ ℓ₂ : Lane W} {tr : Tc W} (h : ¬ Bad2 ℓ₁ ℓ₂ tr) :
    ¬ EM tr ∧ ¬ EF tr ∧ ¬ StepEvent ℓ₁.step tr ∧ ¬ StepEvent ℓ₂.step tr :=
  ⟨fun e => h (Or.inl (Or.inl e)), fun e => h (Or.inl (Or.inr e)),
    fun ⟨pre, e, post, h1, h2⟩ => h (Or.inr ⟨pre, e, post, h1, Or.inl h2⟩),
    fun ⟨pre, e, post, h1, h2⟩ => h (Or.inr ⟨pre, e, post, h1, Or.inr h2⟩)⟩

/-! ## "One query, two answers": a third disjunct, at no term

`RunsIn` is by membership, and the statements are for all lists of entries. A list may hold one
query with two answers: no `EM`, no `EF`; two runs of one chain, two verifier messages, one reading.
A true log never does. So the event costs nothing: `pr_stepEvent_le` asks its bound only at queries
never asked, and there it cannot happen. -/

/-- the entry e is new, and its query stands in pre already (so with another answer) -/
def twice {S : OSpec} (pre : Trace S) (e : QA S) : Prop := e ∉ pre ∧ ∃ r,
    (⟨e.1, e.2.1, r⟩ : QA S) ∈ pre

/-- each query has one answer -/
def OneAns {S : OSpec} (tr : Trace S) : Prop :=
  ∀ (o : S.ι) (q : S.Dom o) (r r' : S.Rng o), (⟨o, q, r⟩ : QA S) ∈ tr →
      (⟨o, q, r'⟩ : QA S) ∈ tr → r = r'

theorem oneAns_of_not_twice {S : OSpec} : ∀ tr : Trace S, ¬ StepEvent twice tr → OneAns tr := by
  intro tr
  induction tr using List.reverseRecOn with
  | nil => intro _ o q r r' h; cases h
  | append_singleton tr e ih =>
    intro hn
    have h1 : OneAns tr := ih fun h => hn (StepEvent.append h [e])
    have h2 : ¬ twice tr e := fun h => hn ⟨tr, e, [], rfl, h⟩
    have key : ∀ (o : S.ι) (q : S.Dom o) (r r' : S.Rng o), (⟨o, q, r⟩ : QA S) ∈ tr →
        (⟨o, q, r'⟩ : QA S) = e → r = r' := by
      intro o q r r' ha hb
      subst hb
      by_cases he : (⟨o, q, r'⟩ : QA S) ∈ tr
      · exact h1 o q r r' ha he
      · exact absurd ⟨he, r, ha⟩ h2
    intro o q r r' ha hb
    rcases List.mem_append.1 ha with ha | ha <;> rcases List.mem_append.1 hb with hb | hb
    · exact h1 o q r r' ha hb
    · exact key o q r r' ha (List.mem_singleton.1 hb)
    · exact (key o q r' r hb (List.mem_singleton.1 ha)).symm
    · have e1 := (List.mem_singleton.1 ha).trans (List.mem_singleton.1 hb).symm
      exact (Prod.mk.inj (eq_of_heq (Sigma.mk.inj e1).2)).2

/-- the state event of one of two lanes, or one query with two answers -/
def step3 (ℓ₁ ℓ₂ : Lane W) (pre : Tc W) (e : QA (typedOracleFamily lam W.K L)) : Prop :=
    step2 ℓ₁ ℓ₂ pre e ∨ twice pre e

def Bad3 (ℓ₁ ℓ₂ : Lane W) (tr : Tc W) : Prop := (EM tr ∨ EF tr) ∨ StepEvent (step3 ℓ₁ ℓ₂) tr

/-- Bad3 is as rare as Bad2: the third disjunct costs nothing. -/
theorem bad3_rare {ℓ₁ ℓ₂ : Lane W} (hne : ℓ₁.t ≠ ℓ₂.t) {N₁ N₂ : ℕ} (hN₁ : N₁ = 2 ^ W.dReq ℓ₁.t)
    (hN₂ : N₂ = 2 ^ W.dReq ℓ₂.t) (o₁ : ℓ₁.OK N₁)
    (o₂ : ℓ₂.OK N₂) {εs : ℝ≥0∞} (b₁ : Err.Below ℓ₁.ε εs) (b₂ : Err.Below ℓ₂.ε εs)
    (β : Type) (A : TypedOracleComputation lam W.K L β) (t : ℕ) (hA : A.QueryBound t) :
    pr A.withTrace.law {o | Bad3 ℓ₁ ℓ₂ o.2} ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2
        / 2 ^ lam := by
  have h := pr_stepEvent_le (S := typedOracleFamily lam W.K L) (step3 ℓ₁ ℓ₂) (fun _ => εs)
    (fun pre e he hs => hs.elim (fun h2 => h2.elim (fun h1 => h1.1 he) fun h1 => h1.1 he) fun
        h1 => h1.1 he)
    (fun pre o q hq => le_trans (pr_mono _ (fun r hr => hr.elim id fun h3 => by
      obtain ⟨-, r', hr'⟩ := h3
      exact absurd hr' (hq r'))) (pr_step2_le hne hN₁ hN₂ o₁ o₂ b₁ b₂ pre o q)) A t hA
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  calc
    pr A.withTrace.law {o | (EM o.2 ∨ EF o.2) ∨ StepEvent (step3 ℓ₁ ℓ₂) o.2} ≤
        pr A.withTrace.law {o | EM o.2 ∨ EF o.2} + pr A.withTrace.law
            {o | StepEvent (step3 ℓ₁ ℓ₂) o.2} :=
      pr_union_le _ _ _
    _ ≤ 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam + (t : ℝ≥0∞) * εs := add_le_add (hashEvents A t hA) h
    _ ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
        rw [add_comm]
        gcongr
        exact Nat.le_succ t

theorem bad3_mono {ℓ₁ ℓ₂ : Lane W} (tr tr' : Tc W) : Bad3 ℓ₁ ℓ₂ tr → Bad3 ℓ₁ ℓ₂ (tr ++ tr') := by
  rintro ((h | h) | h)
  · exact Or.inl (Or.inl (h.append tr'))
  · exact Or.inl (Or.inr (h.append tr'))
  · exact Or.inr (StepEvent.append h tr')

/-- outside Bad3: not `EM`, not `EF`, neither lane's step event, and each query has one answer -/
theorem not_bad3 {ℓ₁ ℓ₂ : Lane W} {tr : Tc W} (h : ¬ Bad3 ℓ₁ ℓ₂ tr) :
    ¬ EM tr ∧ ¬ EF tr ∧ ¬ StepEvent ℓ₁.step tr ∧ ¬ StepEvent ℓ₂.step tr ∧ OneAns tr :=
  ⟨fun e => h (Or.inl (Or.inl e)), fun e => h (Or.inl (Or.inr e)),
    fun ⟨pre, e, post, h1, h2⟩ => h (Or.inr ⟨pre, e, post, h1, Or.inl (Or.inl h2)⟩),
    fun ⟨pre, e, post, h1, h2⟩ => h (Or.inr ⟨pre, e, post, h1, Or.inl (Or.inr h2)⟩),
    oneAns_of_not_twice tr fun ⟨pre, e, post, h1, h2⟩ => h (Or.inr ⟨pre, e, post, h1, Or.inr h2⟩)⟩

end TypedOracleCompiler.Compile.Batch
