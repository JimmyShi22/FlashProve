-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Arms.lean: index binding of a scheme whose verifier is the conjunction of three checks,
from one bound for each check.

What this file states. Definitions and theorems with their proofs, over any family of oracles S, in
the terms of ZKCP/Gen.lean; the intended use is S := one hash function (`Rom.rom 256`).
  `ArmBound v Holds ε`: for every committer with at most tC queries and every prover with at most
    tP: the probability that the check accepts while what it promises (`Holds`, of the key, the
    committer's log, the instance, the proof and the prover's log) fails is at most ε tC tP.
  `threeArms vK vE vP`: the verifier that runs the three checks one after the other and accepts if
    all three do.
  `ArmBound.mono`: a check that accepts only where another accepts has that other's bound.
  `binds_of_arms`: three such bounds, and "where all three promises hold, the instance is in the
    language of the extracted index and the extractor's witness is one", give index binding at the
    sum of the three bounds.
The proof is a union bound, pointwise in the hash function, the committer's outcome and the prover's
outcome. No independence of the checks is used.

Under which hypotheses. `binds_of_arms` takes the three bounds, the sentence in quotation marks
above, and that the scheme's verifier is `threeArms vK vE vP`.

What it does not show. The three bounds are hypotheses here. No coding of typed oracles stands here:
each check's bound may have been proved through a coding of its own. The logs are those of the
committer and the prover: the verifier's own queries are in neither. Each bound is taken at the
budgets tC and tP; what a check's own verifier asks has to stand inside that check's ε.

-/
import ZKCP.GenKeyTag

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace ZKCP.Gen

open Rom (OSpec Fam)
open Prob (pr expect)

variable {S : OSpec} {I X W PP IVK ISK Pf : Type}

/-- What a check's experiment produces. -/
structure ArmOut (S : OSpec) (X IVK Pf : Type) where
  bit : Bool
  key : IVK
  trC : Rom.Trace S
  x : X
  proof : Pf
  trP : Rom.Trace S

/-- The committer, the prover, then one check of the verifier on what they have put out. -/
def armExp (v : IVK → X → Pf → Rom.OComp S Bool) {St : Type} (Ct : Rom.OComp S (IVK × St))
    (Pt : St → Rom.OComp S (X × Pf)) : Rom.OComp S (ArmOut S X IVK Pf) :=
  Ct.withTrace.bind fun o => (Pt o.1.2).withTrace.bind fun o' =>
    (v o.1.1 o'.1.1 o'.1.2).bind fun b => .pure ⟨b, o.1.1, o.2, o'.1.1, o'.1.2, o'.2⟩

/-- The check accepts, and what it promises fails. -/
def armBad (Holds : IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop) : Set (ArmOut S X IVK Pf) :=
  {o | o.bit = true ∧ ¬ Holds o.key o.trC o.x o.proof o.trP}

/-- For every committer with at most tC queries and every prover with at most tP queries: the check
accepts while what it promises fails with probability at most ε tC tP. -/
def ArmBound (v : IVK → X → Pf → Rom.OComp S Bool)
    (Holds : IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop) (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (tC tP : ℕ) (St : Type) (Ct : Rom.OComp S (IVK × St)) (Pt : St → Rom.OComp S (X × Pf)),
    Ct.QueryBound tC → (∀ st, (Pt st).QueryBound tP) →
      Rom.Pr (armExp v Ct Pt) (fun _ => armBad Holds) ≤ ε tC tP

/-- A check v' that, at every hash function, key, instance and proof, accepts with at most the
probability with which the check v accepts has v's bound. (For checks without coins: v' accepts only
where v accepts.) -/
theorem ArmBound.mono {v v' : IVK → X → Pf → Rom.OComp S Bool}
    {Holds : IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop} {ε : ℕ → ℕ → ℝ≥0∞}
    (h : ArmBound v Holds ε)
    (le : ∀ f k x π,
      pr ((v' k x π).runEager f) {b | b = true} ≤ pr ((v k x π).runEager f) {b | b = true}) :
    ArmBound v' Holds ε := by
  classical
  intro tC tP St Ct Pt hC hP
  refine le_trans ?_ (h tC tP St Ct Pt hC hP)
  unfold Rom.Pr Rom.PrCoins
  refine MeasureTheory.lintegral_mono fun f => ?_
  show pr ((armExp v' Ct Pt).runEager f) _ ≤ pr ((armExp v Ct Pt).runEager f) _
  unfold armExp
  rw [runEager_bindO, runEager_bindO, Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o => ?_
  rw [runEager_bindO, runEager_bindO, Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o' => ?_
  have key : ∀ u : Rom.OComp S Bool,
      pr ((u.bind fun b => (.pure ⟨b, o.1.1, o.2, o'.1.1, o'.1.2, o'.2⟩ :
        Rom.OComp S (ArmOut S X IVK Pf))).runEager f) (armBad Holds) =
        if Holds o.1.1 o.2 o'.1.1 o'.1.2 o'.2 then 0 else pr (u.runEager f) {b | b = true} := by
    intro u
    rw [runEager_bindO, Prob.pr_bind]
    split_ifs with hh
    · refine le_antisymm
        (le_trans (Prob.expect_mono _ fun b => ?_) (le_of_eq (Prob.expect_const _ 0)))
        (zero_le _)
      show pr (PMF.pure _) _ ≤ 0
      rw [Prob.pr_pure, if_neg]
      rintro ⟨-, hn⟩
      exact hn hh
    · rw [Prob.pr_eq_expect (u.runEager f)]
      refine Prob.expect_congr _ fun b => ?_
      show pr (PMF.pure _) _ = _
      rw [Prob.pr_pure]
      simp [armBad, hh]
  rw [key, key]
  split_ifs
  · exact le_rfl
  · exact le f _ _ _

/-- The three checks one after the other; accepted if all three accept. -/
def threeArms (vK vE vP : IVK → X → Pf → Rom.OComp S Bool) (k : IVK) (x : X) (π : Pf) :
    Rom.OComp S Bool :=
  (vK k x π).bind fun a => (vE k x π).bind fun b => (vP k x π).bind fun c => .pure (a && b && c)

/-- Three bits drawn one after the other, then anything that can reach the event only from "all
three are true": the event's probability is at most the probability that the first bit is true; the
like for the second and the third. -/
theorem pr_three_le {β : Type} (p q r : PMF Bool) (G : Bool → PMF β) (Ev : Set β)
    (h0 : pr (G false) Ev = 0) :
    pr (p.bind fun a => q.bind fun b => r.bind fun c => G (a && b && c)) Ev ≤
        pr p {b | b = true} ∧
      pr (p.bind fun a => q.bind fun b => r.bind fun c => G (a && b && c)) Ev ≤
        pr q {b | b = true} ∧
      pr (p.bind fun a => q.bind fun b => r.bind fun c => G (a && b && c)) Ev ≤
        pr r {b | b = true} := by
  classical
  have one : ∀ (s : PMF Bool) (H : Bool → PMF β), pr (H false) Ev = 0 →
      pr (s.bind H) Ev ≤ pr s {b | b = true} := by
    intro s H hH
    rw [Prob.pr_bind, Prob.pr_eq_expect s]
    refine Prob.expect_mono s fun a => ?_
    cases a
    · rw [hH]
      exact zero_le _
    · simpa using Prob.pr_le_one (H true) Ev
  have under : ∀ (s : PMF Bool) (H : Bool → PMF β) (c : ℝ≥0∞), (∀ a, pr (H a) Ev ≤ c) →
      pr (s.bind H) Ev ≤ c := by
    intro s H c hH
    rw [Prob.pr_bind]
    exact le_trans (Prob.expect_mono s hH) (le_of_eq (Prob.expect_const s c))
  have zero : ∀ (s : PMF Bool) (H : Bool → PMF β), (∀ a, pr (H a) Ev = 0) →
      pr (s.bind H) Ev = 0 := by
    intro s H hH
    exact le_antisymm (under s H 0 fun a => le_of_eq (hH a)) (zero_le _)
  refine ⟨?_, ?_, ?_⟩
  · refine one p _ (zero q _ fun b => zero r _ fun c => ?_)
    simpa using h0
  · refine under p _ _ fun a => one q _ (zero r _ fun c => ?_)
    simpa using h0
  · refine under p _ _ fun a => under q _ _ fun b => one r _ ?_
    simpa using h0

/-- A bound by a sum of three probabilities passes through a common first step. -/
theorem pr_bind_le_add3 {α β β₁ β₂ β₃ : Type} (f : Fam S) (c : Rom.OComp S α)
    {g : α → Rom.OComp S β} {g₁ : α → Rom.OComp S β₁} {g₂ : α → Rom.OComp S β₂}
    {g₃ : α → Rom.OComp S β₃}
    (E : Set β) (E₁ : Set β₁) (E₂ : Set β₂) (E₃ : Set β₃)
    (h : ∀ a, pr ((g a).runEager f) E ≤
      pr ((g₁ a).runEager f) E₁ + (pr ((g₂ a).runEager f) E₂ + pr ((g₃ a).runEager f) E₃)) :
    pr ((c.bind g).runEager f) E ≤ pr ((c.bind g₁).runEager f) E₁ +
      (pr ((c.bind g₂).runEager f) E₂ + pr ((c.bind g₃).runEager f) E₃) := by
  rw [runEager_bindO, runEager_bindO, runEager_bindO, runEager_bindO, Prob.pr_bind, Prob.pr_bind,
    Prob.pr_bind, Prob.pr_bind,
    ← Prob.expect_add, ← Prob.expect_add]
  exact Prob.expect_mono _ h

open MeasureTheory in
/-- A bound by a sum of three probabilities at every hash function passes to the random one. -/
theorem Pr_le_add3 {α β γ δ : Type} (a : Rom.OComp S α) (b : Rom.OComp S β) (c : Rom.OComp S γ)
    (d : Rom.OComp S δ) (A : Set α) (B : Set β) (C : Set γ) (D : Set δ)
    (h : ∀ f, pr (a.runEager f) A ≤
      pr (b.runEager f) B + (pr (c.runEager f) C + pr (d.runEager f) D)) :
    Rom.Pr a (fun _ => A) ≤
      Rom.Pr b (fun _ => B) + (Rom.Pr c (fun _ => C) + Rom.Pr d (fun _ => D)) := by
  show (∫⁻ f, Rom.PrCoins f a A ∂(Rom.U S)) ≤ (∫⁻ f, Rom.PrCoins f b B ∂(Rom.U S)) +
    ((∫⁻ f, Rom.PrCoins f c C ∂(Rom.U S)) + ∫⁻ f, Rom.PrCoins f d D ∂(Rom.U S))
  rw [← lintegral_add_left (Rom.measurable_PrCoins c C),
    ← lintegral_add_left (Rom.measurable_PrCoins b B)]
  exact lintegral_mono h

/-- A check's experiment behind the committer and the prover: where the promise fails, the bad event
is "the check accepts". -/
theorem pr_arm_of_not {Holds : IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop} (f : Fam S)
    (c : Rom.OComp S Bool) (k : IVK) (trC : Rom.Trace S) (x : X) (π : Pf) (trP : Rom.Trace S)
    (h : ¬ Holds k trC x π trP) :
    pr ((c.bind fun b =>
        (.pure ⟨b, k, trC, x, π, trP⟩ : Rom.OComp S (ArmOut S X IVK Pf))).runEager f)
      (armBad Holds) = pr (c.runEager f) {b | b = true} := by
  classical
  rw [runEager_bindO, Prob.pr_bind, Prob.pr_eq_expect (c.runEager f)]
  refine Prob.expect_congr _ fun b => ?_
  show pr (PMF.pure _) _ = _
  rw [Prob.pr_pure]
  simp [armBad, h]

/-- Index binding of the scheme whose verifier is the conjunction of three checks, from one bound
for each check and: where all three promises hold, the outcome is not bad, whatever the verifier's
bit. -/
theorem binds_of_arms {R : RelPair I X W PP} {A : Arg S I X W IVK ISK Pf}
    {E : Extractor S I X W IVK Pf} {vK vE vP : IVK → X → Pf → Rom.OComp S Bool}
    (hV : A.V = threeArms vK vE vP)
    {HK HE HP : IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop} {εK εE εP : ℕ → ℕ → ℝ≥0∞}
    (bK : ArmBound vK HK εK) (bE : ArmBound vE HE εE) (bP : ArmBound vP HP εP)
    (chain : ∀ k trC x π trP, HK k trC x π trP → HE k trC x π trP → HP k trC x π trP →
      x ∈ R.L (E.Ei k trC) ∧ R.no' (E.Ei k trC) x (E.Ew k trC x π trP)) :
    HasIndexBindingWith R A E fun tC tP => εK tC tP + (εE tC tP + εP tC tP) := by
  intro tC tP St Ct Pt hC hP
  refine le_trans (Pr_le_add3 _ (armExp vK Ct Pt) (armExp vE Ct Pt) (armExp vP Ct Pt) _
    (armBad HK) (armBad HE) (armBad HP) fun f => ?_)
    (add_le_add (bK tC tP St Ct Pt hC hP)
      (add_le_add (bE tC tP St Ct Pt hC hP) (bP tC tP St Ct Pt hC hP)))
  show pr ((Ct.withTrace.bind fun o => (Pt o.1.2).withTrace.bind fun o' =>
    (A.V o.1.1 o'.1.1 o'.1.2).bind fun c => (.pure ⟨c, E.Ei o.1.1 o.2, o'.1.1,
      E.Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ : Rom.OComp S (BindingOutcome I X W))).runEager f)
    (bindingBad R) ≤ _
  refine pr_bind_le_add3 f _ _ _ _ _ fun o => ?_
  refine pr_bind_le_add3 f _ _ _ _ _ fun o' => ?_
  rw [hV]
  have e : ∀ K : Bool → Rom.OComp S (BindingOutcome I X W),
      ((threeArms vK vE vP o.1.1 o'.1.1 o'.1.2).bind K).runEager f =
        ((vK o.1.1 o'.1.1 o'.1.2).runEager f).bind fun a =>
          ((vE o.1.1 o'.1.1 o'.1.2).runEager f).bind fun b =>
            ((vP o.1.1 o'.1.1 o'.1.2).runEager f).bind fun c => (K (a && b && c)).runEager f := by
    intro K
    unfold threeArms
    simp only [runEager_bindO, PMF.bind_bind]
    congr 1
    funext a
    congr 1
    funext b
    congr 1
    funext c
    show (PMF.pure _).bind _ = _
    rw [PMF.pure_bind]
  rw [e]
  have h0 : pr ((Rom.OComp.pure (⟨false, E.Ei o.1.1 o.2, o'.1.1,
      E.Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ : BindingOutcome I X W) : Rom.OComp S _).runEager f)
      (bindingBad R) = 0 := by
    show pr (PMF.pure _) _ = 0
    rw [Prob.pr_pure, if_neg]
    rintro ⟨ha, -⟩
    exact Bool.noConfusion ha
  obtain ⟨l1, l2, l3⟩ := pr_three_le ((vK o.1.1 o'.1.1 o'.1.2).runEager f)
    ((vE o.1.1 o'.1.1 o'.1.2).runEager f) ((vP o.1.1 o'.1.1 o'.1.2).runEager f)
    (fun b => (Rom.OComp.pure (⟨b, E.Ei o.1.1 o.2, o'.1.1,
      E.Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ : BindingOutcome I X W) : Rom.OComp S _).runEager f)
    (bindingBad R) h0
  by_cases h1 : HK o.1.1 o.2 o'.1.1 o'.1.2 o'.2
  · by_cases h2 : HE o.1.1 o.2 o'.1.1 o'.1.2 o'.2
    · by_cases h3 : HP o.1.1 o.2 o'.1.1 o'.1.2 o'.2
      · refine le_trans (le_of_eq ?_) (zero_le _)
        have hz : ∀ b : Bool, pr ((Rom.OComp.pure (⟨b, E.Ei o.1.1 o.2, o'.1.1,
            E.Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ : BindingOutcome I X W) : Rom.OComp S _).runEager f)
            (bindingBad R) = 0 := by
          intro b
          show pr (PMF.pure _) _ = 0
          rw [Prob.pr_pure, if_neg]
          rintro ⟨-, hb⟩
          obtain ⟨c1, c2⟩ := chain _ _ _ _ _ h1 h2 h3
          rcases hb with hb | hb
          · exact hb c1
          · exact hb c2
        rw [Prob.pr_bind]
        refine le_antisymm
          (le_trans (Prob.expect_mono _ fun a => ?_) (le_of_eq (Prob.expect_const _ 0)))
          (zero_le _)
        rw [Prob.pr_bind]
        refine le_trans (Prob.expect_mono _ fun b => ?_) (le_of_eq (Prob.expect_const _ 0))
        rw [Prob.pr_bind]
        exact le_trans (Prob.expect_mono _ fun c => le_of_eq (hz _))
          (le_of_eq (Prob.expect_const _ 0))
      · rw [pr_arm_of_not f _ _ _ _ _ _ h3]
        exact le_trans l3 (le_trans le_add_self le_add_self)
    · rw [pr_arm_of_not (Holds := HE) f _ _ _ _ _ _ h2]
      exact le_trans l2 (le_trans le_self_add le_add_self)
  · rw [pr_arm_of_not (Holds := HK) f _ _ _ _ _ _ h1]
    exact le_trans l1 le_self_add

end ZKCP.Gen

#print axioms ZKCP.Gen.ArmBound.mono
#print axioms ZKCP.Gen.binds_of_arms
