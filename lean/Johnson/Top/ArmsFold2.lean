-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsFold2.lean: a bound against a committer and a prover of typed parts, with a public
reading in front of the verdict and an event that reads the two logs apart, is a bound in the frame
of a committer of a key and a prover of an instance and a proof with a reading (`ArmBoundD`,
Johnson/Top/ArmsD.lean). At letters; over any family of oracles.

Main names.
  `foldExp2 Pub verd Ct Pv`: the committer, with its log; the prover, handed the state, with its
    log; the public reading; the verdict at its value. The outcome keeps both logs.
  `foldArm2 Pub verd packK packP`: the arm on a key and a proof: where `packP` makes nothing of the
    proof it says no; else the public reading, then the verdict at its value.
  `armBoundD_of_two`: from a bound of `foldExp2` for all such committers and provers: the bound
    `ArmBoundD` of `foldArm2`, at the same numbers of queries, for every promise whose failure,
    where `packP` makes something, is the bad event at the two logs.

Against Johnson/Top/ArmsFold.lean: there the two stages are folded into one maker and the event
reads one log; here they stay two, so a promise can read the key's word off the committer's log
alone.

What is not claimed. Nothing on any written arm or reading. Pub, verd, packK, packP, Bad, Holds, ε
are letters, fixed before the function: at a promise that always holds, or an ε of at least 1, it
says nothing. The reading is the same at every key. The reading's and the verdict's own queries
stand in no log and in no budget. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ArmsTold

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP.Gen

open Rom (OSpec Fam)
open Prob (pr expect)

variable {S : OSpec} {X K Pf D Ka Zb : Type}

/-- The committer, with its log; the prover, handed the committer's state, with its log; the public
reading; the verdict at the reading's value on what the two have put out. -/
def foldExp2 (Pub : Rom.OComp S D) (verd : D → Ka → Zb → Rom.OComp S Bool) {St : Type}
    (Ct : Rom.OComp S (Ka × St)) (Pv : St → Rom.OComp S Zb) :
    Rom.OComp S ((((Ka × St) × Rom.Trace S) × (Zb × Rom.Trace S)) × D × Bool) :=
  (Ct.withTrace.bind fun a => (Pv a.1.2).withTrace.bind fun b => .pure (a, b)).bind fun y =>
    (Pub.bind fun d => (verd d y.1.1.1 y.2.1).bind fun b => .pure (d, b)).bind fun v =>
      .pure (y, v)

/-- The arm on a key and a proof. -/
def foldArm2 (Pub : Rom.OComp S D) (verd : D → Ka → Zb → Rom.OComp S Bool) (packK : K → Ka)
    (packP : Pf → Option Zb) (k : K) (_ : X) (π : Pf) : Rom.OComp S Bool :=
  match packP π with
  | some z => Pub.bind fun d => verd d (packK k) z
  | none => .pure false

/-- **Two phases stay two.** -/
theorem armBoundD_of_two {Pub : Rom.OComp S D} (hn : Pub.NoCoin)
    {verd : D → Ka → Zb → Rom.OComp S Bool} (packK : K → Ka) (packP : Pf → Option Zb)
    {Bad : D → Ka → Rom.Trace S → Zb → Rom.Trace S → Prop} {ε : ℕ → ℕ → ℝ≥0∞}
    {Holds : D → K → Rom.Trace S → X → Pf → Rom.Trace S → Prop}
    (hH : ∀ d k trC x π trP z, packP π = some z → ¬ Holds d k trC x π trP →
      Bad d (packK k) trC z trP)
    (h : ∀ (St : Type) (Ct : Rom.OComp S (Ka × St)) (Pv : St → Rom.OComp S Zb) (tC tP : ℕ),
      Ct.QueryBound tC → (∀ st, (Pv st).QueryBound tP) →
      Rom.Pr (foldExp2 Pub verd Ct Pv)
        (fun _ => {x | x.2.2 = true ∧ Bad x.2.1 x.1.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2}) ≤ ε tC tP) :
    ArmBoundD (fun _ => Pub) (foldArm2 (X := X) Pub verd packK packP) Holds ε := by
  classical
  intro tC tP St Ct Pt hC hP
  have hp : ∀ (f : Fam S) (γ : Type) (z : γ),
      Rom.OComp.runEager f (Rom.OComp.pure z : Rom.OComp S γ) = PMF.pure z := fun _ _ _ => rfl
  rcases isEmpty_or_nonempty Zb with hE | ⟨⟨z₀⟩⟩
  · -- nothing can be made of a proof: the arm says no throughout
    refine le_trans ?_ (zero_le _)
    unfold Rom.Pr
    refine le_trans (MeasureTheory.lintegral_mono (g := fun _ => 0) fun f => ?_) (by simp)
    simp only [Rom.PrCoins]
    rw [runEager_armExpD (fun _ => hn), Prob.pr_bind]
    refine le_trans (Prob.expect_mono _ fun o => ?_) (le_of_eq (Prob.expect_const _ 0))
    rw [Prob.pr_bind]
    refine le_trans (Prob.expect_mono _ fun o' => ?_) (le_of_eq (Prob.expect_const _ 0))
    unfold foldArm2
    cases hk : packP o'.1.2 with
    | some z => exact (hE.false z).elim
    | none =>
      simp only [hp, PMF.pure_bind]
      rw [Prob.pr_pure, if_neg]
      rintro ⟨ha, -⟩
      exact Bool.noConfusion ha
  refine le_trans ?_ (h St (mapO (fun o : K × St => (packK o.1, o.2)) Ct)
    (fun st => mapO (fun o' : X × Pf => (packP o'.2).getD z₀) (Pt st)) tC tP
    (queryBound_mapO _ Ct tC hC) fun st => queryBound_mapO _ (Pt st) tP (hP st))
  unfold Rom.Pr
  refine MeasureTheory.lintegral_mono fun f => ?_
  have hr : Pub.runEager f = PMF.pure (Pub.det f) := hn.runEager f
  replace hp := hp f
  simp only [Rom.PrCoins]
  rw [runEager_armExpD (fun _ => hn)]
  unfold foldExp2
  simp only [withTrace_mapO]
  unfold mapO
  simp only [runEager_bindO, hr, hp, PMF.pure_bind, PMF.bind_bind]
  rw [Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o => ?_
  rw [Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o' => ?_
  unfold foldArm2
  cases hk : packP o'.1.2 with
  | none =>
    simp only [hp, PMF.pure_bind]
    rw [Prob.pr_pure, if_neg]
    · exact zero_le _
    · rintro ⟨ha, -⟩
      exact Bool.noConfusion ha
  | some z =>
    simp only [runEager_bindO, hr, PMF.pure_bind, Option.getD_some]
    rw [Prob.pr_bind, Prob.pr_bind]
    refine Prob.expect_mono _ fun b => ?_
    rw [Prob.pr_pure, Prob.pr_pure]
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd ⟨h1.1, hH _ _ _ _ _ _ z hk h1.2⟩ h2
    · exact zero_le _
    · exact le_rfl

end ZKCP.Gen
