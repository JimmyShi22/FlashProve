-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsTold.lean: from an arm that reads a public value itself to the arm that is told it.

Johnson/Top/OnFilesArmsC.lean has the public data c in the typed key; each arm is meant to ask the
hash function at the public strings and to say no unless the answer is c. A committer names c after
its queries: so a bound at each fixed c gives no bound for such an arm. Here the bound comes from
the arm that reads the value itself, with the reading drawn in the experiment
(Johnson/Top/ArmsD.lean). Over any family of oracles S; Pub : a computation of a value d, without
coins; vf : a family of arms.
  `readArm Pub vf k x π`: run Pub, then the member at its value.
  `toldArm Pub vf (c, k) x π`: run Pub; say no unless its value is c; then the member at it.
  `ArmBoundD.told`: a bound of `readArm`, with the promise read at Pub's value, is a bound of
    `toldArm`, with the promise read at the key's c: the same ε. Pointwise in the oracles: the told
    arm accepts only where c is Pub's value, and there the two arms and the two promises are the
    same.
Limits: one direction. The premise is a hypothesis. Pub does not read the key.


-/
import Johnson.Top.ArmsD

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace ZKCP.Gen

open Rom (OSpec Fam)
open Prob (pr expect)

variable {S : OSpec} {X K Pf D : Type} [DecidableEq D]

/-- Run the public reading, then the member of the family at its value. -/
def readArm (Pub : Rom.OComp S D) (vf : D → K → X → Pf → Rom.OComp S Bool) (k : K) (x : X)
    (π : Pf) : Rom.OComp S Bool :=
  Pub.bind fun d => vf d k x π

/-- Run the public reading; say no unless its value is the key's c; then the member at it. -/
def toldArm (Pub : Rom.OComp S D) (vf : D → K → X → Pf → Rom.OComp S Bool) (ck : D × K) (x : X)
    (π : Pf) : Rom.OComp S Bool :=
  Pub.bind fun d => if d = ck.1 then vf d ck.2 x π else .pure false

/-- A bound of the arm that reads the public value itself is a bound of the arm that is told it. -/
theorem ArmBoundD.told {Pub : Rom.OComp S D} (hn : Pub.NoCoin)
    {vf : D → K → X → Pf → Rom.OComp S Bool}
    {Holds : D → K → Rom.Trace S → X → Pf → Rom.Trace S → Prop} {ε : ℕ → ℕ → ℝ≥0∞}
    (h : ArmBoundD (fun _ => Pub) (readArm Pub vf) Holds ε) :
    ArmBound (toldArm Pub vf) (fun ck trC x π trP => Holds ck.1 ck.2 trC x π trP) ε := by
  classical
  intro tC tP St Ct Pt hC hP
  have b := h tC tP (D × St) (mapO (fun o : (D × K) × St => (o.1.2, (o.1.1, o.2))) Ct)
    (fun s => Pt s.2) (queryBound_mapO _ Ct tC hC) fun s => hP s.2
  refine le_trans ?_ b
  unfold Rom.Pr
  refine MeasureTheory.lintegral_mono fun f => ?_
  have hr : Pub.runEager f = PMF.pure (Pub.det f) := hn.runEager f
  have hp : ∀ (γ : Type) (z : γ),
      Rom.OComp.runEager f (Rom.OComp.pure z : Rom.OComp S γ) = PMF.pure z := fun _ _ => rfl
  simp only [Rom.PrCoins]
  rw [runEager_armExpD (fun _ => hn)]
  unfold armExp toldArm readArm
  rw [withTrace_mapO]
  unfold mapO
  simp only [runEager_bindO, hr, hp, PMF.pure_bind, PMF.bind_bind]
  rw [Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o => ?_
  rw [Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o' => ?_
  by_cases hc : Pub.det f = o.1.1.1
  · rw [if_pos hc, Prob.pr_bind, Prob.pr_bind]
    refine Prob.expect_mono _ fun b => ?_
    rw [Prob.pr_pure, Prob.pr_pure]
    by_cases hb : (⟨b, o.1.1, o.2, o'.1.1, o'.1.2, o'.2⟩ : ArmOut S X (D × K) Pf) ∈
        armBad fun ck trC x π trP => Holds ck.1 ck.2 trC x π trP
    · rw [if_pos hb, if_pos]
      refine ⟨hb.1, ?_⟩
      show ¬ Holds (Pub.det f) o.1.1.2 o.2 o'.1.1 o'.1.2 o'.2
      rw [hc]
      exact hb.2
    · rw [if_neg hb]
      exact zero_le _
  · rw [if_neg hc, hp, PMF.pure_bind, Prob.pr_pure, if_neg]
    · exact zero_le _
    · rintro ⟨ha, -⟩
      exact Bool.noConfusion ha

end ZKCP.Gen

#print axioms ZKCP.Gen.ArmBoundD.told
