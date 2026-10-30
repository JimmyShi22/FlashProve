-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsFold.lean: a bound against one maker, with a public reading in front of the verdict,
is a bound in the frame of a committer and a prover with a reading (`ArmBoundD`,
Johnson/Top/ArmsD.lean). At letters; over any family of oracles.

Main names.
  `foldExp Pub verd Mk`: the maker runs, with its log; the public reading; the verdict at its value.
  `foldArm Pub verd pack`: the arm on a key and a proof: where `pack` makes nothing of them it says
    no; else the public reading, then the verdict at its value on what `pack` has made.
  `armBoundD_of_maker`: from a bound of `foldExp` for every maker with at most t queries: the bound
    `ArmBoundD` of `foldArm`, at t := the committer's and the prover's queries together, for every
    promise whose failure, where `pack` makes something, is the maker's bad event on the committer's
    log followed by the prover's.

What is not claimed. Nothing on any written arm or reading. Pub, verd, pack, Bad, Holds, ε are
letters, fixed before the function: at a promise that always holds, or an ε of at least 1, it says
nothing. The reading is the same at every key. The fold forgets the seam between the two logs: a
promise that reads the key's part off the committer's log alone is not reached by it
(Johnson/Top/ArmsFold2.lean keeps the seam). The reading's and the verdict's own queries stand in no
log and in no budget. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ArmsD
import Rom.OverOneN

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP.Gen

open Rom (OSpec Fam)
open Prob (pr expect)

variable {S : OSpec} {X K Pf D Zt : Type}

/-- The maker runs, with its log; then the public reading; then the verdict at the reading's value
on what the maker has put out. -/
def foldExp (Pub : Rom.OComp S D) (verd : D → Zt → Rom.OComp S Bool) (Mk : Rom.OComp S Zt) :
    Rom.OComp S ((Zt × Rom.Trace S) × D × Bool) :=
  Mk.withTrace.bind fun o =>
    (Pub.bind fun d => (verd d o.1).bind fun b => .pure (d, b)).bind fun v => .pure (o, v)

/-- The arm on a key and a proof. -/
def foldArm (Pub : Rom.OComp S D) (verd : D → Zt → Rom.OComp S Bool) (pack : K → Pf → Option Zt)
    (k : K) (_ : X) (π : Pf) : Rom.OComp S Bool :=
  match pack k π with
  | some z => Pub.bind fun d => verd d z
  | none => .pure false

/-- **Two phases as one maker.** -/
theorem armBoundD_of_maker {Pub : Rom.OComp S D} (hn : Pub.NoCoin)
    {verd : D → Zt → Rom.OComp S Bool} (pack : K → Pf → Option Zt)
    {Bad : D → Zt → Rom.Trace S → Prop} {ε : ℕ → ℝ≥0∞}
    {Holds : D → K → Rom.Trace S → X → Pf → Rom.Trace S → Prop}
    (hH : ∀ d k trC x π trP z, pack k π = some z → ¬ Holds d k trC x π trP →
      Bad d z (trC ++ trP))
    (h : ∀ (Mk : Rom.OComp S Zt) (t : ℕ), Mk.QueryBound t →
      Rom.Pr (foldExp Pub verd Mk) (fun _ => {x | x.2.2 = true ∧ Bad x.2.1 x.1.1 x.1.2}) ≤ ε t) :
    ArmBoundD (fun _ => Pub) (foldArm (X := X) Pub verd pack) Holds fun tC tP => ε (tC + tP) := by
  classical
  intro tC tP St Ct Pt hC hP
  have hp : ∀ (f : Fam S) (γ : Type) (z : γ),
      Rom.OComp.runEager f (Rom.OComp.pure z : Rom.OComp S γ) = PMF.pure z := fun _ _ _ => rfl
  rcases isEmpty_or_nonempty Zt with hE | ⟨⟨z₀⟩⟩
  · -- nothing can be made: the arm says no throughout
    refine le_trans ?_ (zero_le _)
    unfold Rom.Pr
    refine le_trans (MeasureTheory.lintegral_mono (g := fun _ => 0) fun f => ?_) (by simp)
    simp only [Rom.PrCoins]
    rw [runEager_armExpD (fun _ => hn), Prob.pr_bind]
    refine le_trans (Prob.expect_mono _ fun o => ?_) (le_of_eq (Prob.expect_const _ 0))
    rw [Prob.pr_bind]
    refine le_trans (Prob.expect_mono _ fun o' => ?_) (le_of_eq (Prob.expect_const _ 0))
    unfold foldArm
    cases hk : pack o.1.1 o'.1.2 with
    | some z => exact (hE.false z).elim
    | none =>
      simp only [hp, PMF.pure_bind]
      rw [Prob.pr_pure, if_neg]
      rintro ⟨ha, -⟩
      exact Bool.noConfusion ha
  have hq : (Ct.bind fun o => (Pt o.2).bind fun o' =>
      (.pure ((pack o.1 o'.2).getD z₀) : Rom.OComp S Zt)).QueryBound (tC + tP) :=
    Rom.OComp.QueryBound.bind hC fun o =>
      Rom.OComp.QueryBound.bind (t := 0) (hP o.2) fun _ => trivial
  refine le_trans ?_ (h _ _ hq)
  unfold Rom.Pr
  refine MeasureTheory.lintegral_mono fun f => ?_
  have hr : Pub.runEager f = PMF.pure (Pub.det f) := hn.runEager f
  replace hp := hp f
  simp only [Rom.PrCoins]
  rw [runEager_armExpD (fun _ => hn)]
  unfold foldExp
  rw [Rom.withTrace_bind]
  simp only [Rom.withTrace_bind, runEager_bindO, hr, hp, PMF.pure_bind, PMF.bind_bind]
  rw [Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o => ?_
  rw [Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o' => ?_
  have hw : ∀ z : Zt, (Rom.OComp.pure z : Rom.OComp S Zt).withTrace = .pure (z, []) := fun _ => rfl
  simp only [hw, hp, PMF.pure_bind]
  unfold foldArm
  cases hk : pack o.1.1 o'.1.2 with
  | none =>
    simp only [hp, PMF.pure_bind]
    rw [Prob.pr_pure, if_neg]
    · exact zero_le _
    · rintro ⟨ha, -⟩
      exact Bool.noConfusion ha
  | some z =>
    simp only [runEager_bindO, hr, PMF.pure_bind, Option.getD_some, List.append_nil]
    rw [Prob.pr_bind, Prob.pr_bind]
    refine Prob.expect_mono _ fun b => ?_
    rw [Prob.pr_pure, Prob.pr_pure]
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd ⟨h1.1, hH _ _ _ _ _ _ z hk h1.2⟩ h2
    · exact zero_le _
    · exact le_rfl

end ZKCP.Gen
