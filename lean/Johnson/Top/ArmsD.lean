-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsD.lean: Johnson/Top/Arms.lean where the promises and the extractor also read a value
that a public reading draws from the oracles.

What this file states. Motive (no Lean here says it): a verifier's public digests are answers of the
hash function at public strings. If the checks, their codings and the word under a root hang on such
a value d, then a promise and an extractor that see the key and the logs alone cannot be written: a
committer need not have asked the public strings. Here a reading `rd : key → computation of d` is
run in the experiment; the promises read d in addition to the key, the logs, the instance and the
proof; and the extractor of the index is the oracle algorithm "run the reading, then decode at d".
Over any family of oracles S:
  `ExtractorO`, `ExtractorO.Within`, `bindingExpO`, `HasIndexBindingWithO`: Johnson/Top/GameO.lean's
    four definitions in the terms of ZKCP/Gen.lean: the extractor of the index may query the
    oracles, at most q times, without coins; its queries enter nobody's log.
  `armExpD rd v Ct Pt`, `armBadD`, `ArmBoundD rd v Holds ε`: the check's experiment with the reading
    run behind the prover, its bad event, its bound.
  `extD rd ei ew`: the extractor "run the reading, then `ei` at its value".
  `binds_of_armsD`: three such bounds at one reading, and "where all three promises hold at d, the
    instance is in the language of the index extracted at d and the extractor's witness is one",
    give index binding with that extractor at the sum of the three bounds.
A reading without coins has one value at fixed oracles, wherever it runs: so that the extractor runs
it before the prover and the checks' experiments behind the prover makes no difference.

Under which hypotheses. `binds_of_armsD` takes the three bounds, the sentence in quotation marks in
its own entry above (`chain`), that the scheme's verifier is `threeArms vK vE vP` (hV), and that the
reading tosses no coin (hrd) and makes at most q queries (hq).

What it does not show. The three bounds are hypotheses here. One reading serves all three checks and
the extractor. The reading is handed the key alone. The number q counts the reading's queries, not
the strings at which it asks. These q queries stand in nobody's budget: each bound is taken at tC
and tP, so what the reading asks has to be carried inside each check's ε.

-/
import Rom.Cache
import Rom.Prefix
import Johnson.Top.Arms

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace ZKCP.Gen

open Rom (OSpec Fam)
open Prob (pr expect)

variable {S : OSpec} {I X W PP IVK ISK Pf D : Type}

/-- An extractor whose index is the output of an oracle algorithm. -/
structure ExtractorO (S : OSpec) (I X W IVK Pf : Type) where
  Ei : IVK → Rom.Trace S → Rom.OComp S (Option I)
  Ew : IVK → Rom.Trace S → X → Pf → Rom.Trace S → W

/-- The extractor of the index asks at most q queries and draws no coin, at every key and log. -/
def ExtractorO.Within (E : ExtractorO S I X W IVK Pf) (q : ℕ) : Prop :=
  ∀ k tr, (E.Ei k tr).QueryBound q ∧ (E.Ei k tr).NoCoin

/-- The experiment of index binding with such an extractor. Its queries enter no trace. -/
def bindingExpO {St : Type} (A : Arg S I X W IVK ISK Pf) (E : ExtractorO S I X W IVK Pf)
    (Ct : Rom.OComp S (IVK × St)) (Pt : St → Rom.OComp S (X × Pf)) :
    Rom.OComp S (BindingOutcome I X W) :=
  Ct.withTrace.bind fun o => (E.Ei o.1.1 o.2).bind fun iStar =>
    (Pt o.1.2).withTrace.bind fun o' => (A.V o.1.1 o'.1.1 o'.1.2).bind fun b =>
      .pure ⟨b, iStar, o'.1.1, E.Ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩

/-- The bound of index binding in that experiment, for an extractor with at most q queries and no
coin. -/
def HasIndexBindingWithO (R : RelPair I X W PP) (A : Arg S I X W IVK ISK Pf)
    (E : ExtractorO S I X W IVK Pf) (q : ℕ) (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  E.Within q ∧
    ∀ (tC tP : ℕ) (St : Type) (Ct : Rom.OComp S (IVK × St)) (Pt : St → Rom.OComp S (X × Pf)),
      Ct.QueryBound tC → (∀ st, (Pt st).QueryBound tP) →
        Rom.Pr (bindingExpO A E Ct Pt) (fun _ => bindingBad R) ≤ ε tC tP

/-- An extractor that reads the key and the log alone, as one that asks nothing. -/
def Extractor.toO (E : Extractor S I X W IVK Pf) : ExtractorO S I X W IVK Pf :=
  ⟨fun k tr => .pure (E.Ei k tr), E.Ew⟩

/-- For an extractor that asks nothing the bound is `HasIndexBindingWith`. -/
theorem hasIndexBindingWithO_toO_iff (R : RelPair I X W PP) (A : Arg S I X W IVK ISK Pf)
    (E : Extractor S I X W IVK Pf) (ε : ℕ → ℕ → ℝ≥0∞) :
    HasIndexBindingWithO R A E.toO 0 ε ↔ HasIndexBindingWith R A E ε :=
  ⟨fun h => h.2, fun h => ⟨fun _ _ => ⟨trivial, trivial⟩, h⟩⟩

/-- What a check's experiment with a reading produces. -/
structure ArmOutD (S : OSpec) (X IVK Pf D : Type) where
  bit : Bool
  key : IVK
  trC : Rom.Trace S
  x : X
  proof : Pf
  trP : Rom.Trace S
  d : D

/-- The committer, the prover, the reading at the key, then one check of the verifier. -/
def armExpD (rd : IVK → Rom.OComp S D) (v : IVK → X → Pf → Rom.OComp S Bool) {St : Type}
    (Ct : Rom.OComp S (IVK × St)) (Pt : St → Rom.OComp S (X × Pf)) :
    Rom.OComp S (ArmOutD S X IVK Pf D) :=
  Ct.withTrace.bind fun o => (Pt o.1.2).withTrace.bind fun o' => (rd o.1.1).bind fun d =>
    (v o.1.1 o'.1.1 o'.1.2).bind fun b => .pure ⟨b, o.1.1, o.2, o'.1.1, o'.1.2, o'.2, d⟩

/-- The check accepts, and what it promises at the reading's value fails. -/
def armBadD (Holds : D → IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop) :
    Set (ArmOutD S X IVK Pf D) :=
  {o | o.bit = true ∧ ¬ Holds o.d o.key o.trC o.x o.proof o.trP}

/-- For every committer with at most tC queries and every prover with at most tP queries: the check
accepts while what it promises at the reading's value fails with probability at most ε tC tP. -/
def ArmBoundD (rd : IVK → Rom.OComp S D) (v : IVK → X → Pf → Rom.OComp S Bool)
    (Holds : D → IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop) (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (tC tP : ℕ) (St : Type) (Ct : Rom.OComp S (IVK × St)) (Pt : St → Rom.OComp S (X × Pf)),
    Ct.QueryBound tC → (∀ st, (Pt st).QueryBound tP) →
      Rom.Pr (armExpD rd v Ct Pt) (fun _ => armBadD Holds) ≤ ε tC tP

/-- The extractor "run the reading, then `ei` at its value". -/
def extD (rd : IVK → Rom.OComp S D) (ei : D → IVK → Rom.Trace S → Option I)
    (ew : IVK → Rom.Trace S → X → Pf → Rom.Trace S → W) : ExtractorO S I X W IVK Pf :=
  ⟨fun k tr => (rd k).bind fun d => .pure (ei d k tr), ew⟩

/-- A bound by a sum of three probabilities passes through a common first step. -/
theorem pmf_bind_le_add3 {α β β₁ β₂ β₃ : Type} (p : PMF α) {g : α → PMF β} {g₁ : α → PMF β₁}
    {g₂ : α → PMF β₂} {g₃ : α → PMF β₃} (E : Set β) (E₁ : Set β₁) (E₂ : Set β₂) (E₃ : Set β₃)
    (h : ∀ a, pr (g a) E ≤ pr (g₁ a) E₁ + (pr (g₂ a) E₂ + pr (g₃ a) E₃)) :
    pr (p.bind g) E ≤ pr (p.bind g₁) E₁ + (pr (p.bind g₂) E₂ + pr (p.bind g₃) E₃) := by
  rw [Prob.pr_bind, Prob.pr_bind, Prob.pr_bind, Prob.pr_bind, ← Prob.expect_add,
    ← Prob.expect_add]
  exact Prob.expect_mono _ h

/-- At fixed oracles the check's experiment with a reading without coins, written out. -/
theorem runEager_armExpD {rd : IVK → Rom.OComp S D} (hrd : ∀ k, (rd k).NoCoin)
    (v : IVK → X → Pf → Rom.OComp S Bool) {St : Type} (Ct : Rom.OComp S (IVK × St))
    (Pt : St → Rom.OComp S (X × Pf)) (f : Fam S) :
    (armExpD rd v Ct Pt).runEager f =
      (Ct.withTrace.runEager f).bind fun o => ((Pt o.1.2).withTrace.runEager f).bind fun o' =>
        ((v o.1.1 o'.1.1 o'.1.2).runEager f).bind fun b =>
          PMF.pure ⟨b, o.1.1, o.2, o'.1.1, o'.1.2, o'.2, (rd o.1.1).det f⟩ := by
  have hr : ∀ k, (rd k).runEager f = PMF.pure ((rd k).det f) := fun k => (hrd k).runEager f
  unfold armExpD
  simp only [runEager_bindO, hr, PMF.pure_bind]
  rfl

/-- With a reading that reads nothing it is `ArmBound`. -/
theorem armBoundD_unit_iff (v : IVK → X → Pf → Rom.OComp S Bool)
    (Holds : IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop) (ε : ℕ → ℕ → ℝ≥0∞) :
    ArmBoundD (fun _ => (.pure () : Rom.OComp S Unit)) v (fun _ => Holds) ε ↔
      ArmBound v Holds ε := by
  have key : ∀ (St : Type) (Ct : Rom.OComp S (IVK × St)) (Pt : St → Rom.OComp S (X × Pf)),
      Rom.Pr (armExpD (fun _ => (.pure () : Rom.OComp S Unit)) v Ct Pt)
          (fun _ => armBadD fun _ => Holds) =
        Rom.Pr (armExp v Ct Pt) (fun _ => armBad Holds) := by
    intro St Ct Pt
    unfold Rom.Pr
    refine MeasureTheory.lintegral_congr fun f => ?_
    have hp : ∀ (γ : Type) (z : γ),
        Rom.OComp.runEager f (Rom.OComp.pure z : Rom.OComp S γ) = PMF.pure z := fun _ _ => rfl
    simp only [Rom.PrCoins]
    rw [runEager_armExpD (rd := fun _ => (.pure () : Rom.OComp S Unit)) (fun _ => trivial)]
    unfold armExp
    simp only [runEager_bindO, hp]
    rw [Prob.pr_bind, Prob.pr_bind]
    refine Prob.expect_congr _ fun o => ?_
    rw [Prob.pr_bind, Prob.pr_bind]
    refine Prob.expect_congr _ fun o' => ?_
    rw [Prob.pr_bind, Prob.pr_bind]
    refine Prob.expect_congr _ fun b => ?_
    rw [Prob.pr_pure, Prob.pr_pure]
    rfl
  constructor
  · intro h tC tP St Ct Pt hC hP
    rw [← key]
    exact h tC tP St Ct Pt hC hP
  · intro h tC tP St Ct Pt hC hP
    rw [key]
    exact h tC tP St Ct Pt hC hP

/-- Where the promise fails, the bad event of the last step is "the check accepts". -/
theorem pr_armD_of_not {Holds : D → IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop}
    (p : PMF Bool) (k : IVK) (trC : Rom.Trace S) (x : X) (π : Pf) (trP : Rom.Trace S) (d : D)
    (h : ¬ Holds d k trC x π trP) :
    pr (p.bind fun b => PMF.pure (⟨b, k, trC, x, π, trP, d⟩ : ArmOutD S X IVK Pf D))
      (armBadD Holds) = pr p {b | b = true} := by
  classical
  rw [Prob.pr_bind, Prob.pr_eq_expect p]
  refine Prob.expect_congr _ fun b => ?_
  rw [Prob.pr_pure]
  simp [armBadD, h]

/-- Index binding, with the extractor "run the reading, then decode at its value", of the scheme
whose verifier is the conjunction of three checks, from one bound for each check at that reading. -/
theorem binds_of_armsD {R : RelPair I X W PP} {A : Arg S I X W IVK ISK Pf}
    {rd : IVK → Rom.OComp S D} {ei : D → IVK → Rom.Trace S → Option I}
    {ew : IVK → Rom.Trace S → X → Pf → Rom.Trace S → W}
    {vK vE vP : IVK → X → Pf → Rom.OComp S Bool} (hV : A.V = threeArms vK vE vP) {q : ℕ}
    (hrd : ∀ k, (rd k).NoCoin) (hq : ∀ k, (rd k).QueryBound q)
    {HK HE HP : D → IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop} {εK εE εP : ℕ → ℕ → ℝ≥0∞}
    (bK : ArmBoundD rd vK HK εK) (bE : ArmBoundD rd vE HE εE) (bP : ArmBoundD rd vP HP εP)
    (chain : ∀ d k trC x π trP, HK d k trC x π trP → HE d k trC x π trP → HP d k trC x π trP →
      x ∈ R.L (ei d k trC) ∧ R.no' (ei d k trC) x (ew k trC x π trP)) :
    HasIndexBindingWithO R A (extD rd ei ew) q fun tC tP => εK tC tP + (εE tC tP + εP tC tP) := by
  refine ⟨fun k tr => ⟨?_, (hrd k).bind fun _ => trivial⟩, ?_⟩
  · have h : ((rd k).bind fun d => (.pure (ei d k tr) : Rom.OComp S (Option I))).QueryBound
        (q + 0) := (hq k).bind fun _ => trivial
    exact h
  intro tC tP St Ct Pt hC hP
  refine le_trans (Pr_le_add3 _ (armExpD rd vK Ct Pt) (armExpD rd vE Ct Pt) (armExpD rd vP Ct Pt) _
    (armBadD HK) (armBadD HE) (armBadD HP) fun f => ?_)
    (add_le_add (bK tC tP St Ct Pt hC hP)
      (add_le_add (bE tC tP St Ct Pt hC hP) (bP tC tP St Ct Pt hC hP)))
  have hr : ∀ k, (rd k).runEager f = PMF.pure ((rd k).det f) := fun k => (hrd k).runEager f
  have eL : (bindingExpO A (extD rd ei ew) Ct Pt).runEager f =
      (Ct.withTrace.runEager f).bind fun o => ((Pt o.1.2).withTrace.runEager f).bind fun o' =>
        ((vK o.1.1 o'.1.1 o'.1.2).runEager f).bind fun a =>
          ((vE o.1.1 o'.1.1 o'.1.2).runEager f).bind fun b =>
            ((vP o.1.1 o'.1.1 o'.1.2).runEager f).bind fun c =>
              PMF.pure (⟨a && b && c, ei ((rd o.1.1).det f) o.1.1 o.2, o'.1.1,
                ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ : BindingOutcome I X W) := by
    unfold bindingExpO extD
    rw [hV]
    unfold threeArms
    have hp : ∀ (γ : Type) (z : γ),
        Rom.OComp.runEager f (Rom.OComp.pure z : Rom.OComp S γ) = PMF.pure z := fun _ _ => rfl
    simp only [runEager_bindO, hr, hp, PMF.pure_bind, PMF.bind_bind]
  rw [eL, runEager_armExpD hrd, runEager_armExpD hrd, runEager_armExpD hrd]
  refine pmf_bind_le_add3 _ _ _ _ _ fun o => ?_
  refine pmf_bind_le_add3 _ _ _ _ _ fun o' => ?_
  have h0 : pr (PMF.pure (⟨false, ei ((rd o.1.1).det f) o.1.1 o.2, o'.1.1,
      ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ : BindingOutcome I X W)) (bindingBad R) = 0 := by
    rw [Prob.pr_pure, if_neg]
    rintro ⟨ha, -⟩
    exact Bool.noConfusion ha
  obtain ⟨l1, l2, l3⟩ := pr_three_le ((vK o.1.1 o'.1.1 o'.1.2).runEager f)
    ((vE o.1.1 o'.1.1 o'.1.2).runEager f) ((vP o.1.1 o'.1.1 o'.1.2).runEager f)
    (fun b => PMF.pure (⟨b, ei ((rd o.1.1).det f) o.1.1 o.2, o'.1.1,
      ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ : BindingOutcome I X W))
    (bindingBad R) h0
  by_cases h1 : HK ((rd o.1.1).det f) o.1.1 o.2 o'.1.1 o'.1.2 o'.2
  · by_cases h2 : HE ((rd o.1.1).det f) o.1.1 o.2 o'.1.1 o'.1.2 o'.2
    · by_cases h3 : HP ((rd o.1.1).det f) o.1.1 o.2 o'.1.1 o'.1.2 o'.2
      · refine le_trans (le_of_eq ?_) (zero_le _)
        have hz : ∀ b : Bool, pr (PMF.pure (⟨b, ei ((rd o.1.1).det f) o.1.1 o.2, o'.1.1,
            ew o.1.1 o.2 o'.1.1 o'.1.2 o'.2⟩ : BindingOutcome I X W)) (bindingBad R) = 0 := by
          intro b
          rw [Prob.pr_pure, if_neg]
          rintro ⟨-, hb⟩
          obtain ⟨c1, c2⟩ := chain _ _ _ _ _ _ h1 h2 h3
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
      · rw [pr_armD_of_not (Holds := HP) _ _ _ _ _ _ _ h3]
        exact le_trans l3 (le_trans le_add_self le_add_self)
    · rw [pr_armD_of_not (Holds := HE) _ _ _ _ _ _ _ h2]
      exact le_trans l2 (le_trans le_self_add le_add_self)
  · rw [pr_armD_of_not (Holds := HK) _ _ _ _ _ _ _ h1]
    exact le_trans l1 le_self_add

end ZKCP.Gen

#print axioms ZKCP.Gen.hasIndexBindingWithO_toO_iff
#print axioms ZKCP.Gen.armBoundD_unit_iff
#print axioms ZKCP.Gen.binds_of_armsD
