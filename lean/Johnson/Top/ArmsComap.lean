-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsComap.lean: a bound on a check with a public reading (a computation that queries the
hash function; `ArmBoundD`, Johnson/Top/ArmsD.lean) passes along a map of keys and a map, total or
partial, of instance and proof, at the same error. The only hypotheses are the given bound and that
the reading tosses no coin.

What this file states. `ArmBoundD.comap`: from `ArmBoundD rd v Holds ε`, a map p of keys and a map q
of instance and proof: the bound, at the same ε, of the reading, the check and the promise that
first apply p to the key and q to instance and proof. `armVia v p q`: the check behind a map p of
keys and a partial map q of instance and proof: where q gives nothing it says no.
`ArmBoundD.comapOpt`: the bound of `armVia v p q`, at the same ε, for the promise "at what q gives,
the old promise holds". The use: a bound is proved of a check at the types at which its proof is
easy: a key that holds a root and a record alone; a proof that carries the instance with it. The
record of hypotheses that joins three checks requires the three bounds at one type of keys, one of
instances and one of proofs. Where its check is the proved check behind two plain maps, it has the
proved check's bound.

Under which hypotheses. h: the bound `ArmBoundD rd v Holds ε`; hrd: the reading rd tosses no coin at
any key.

What it does not show. Nothing on any concrete check, reading or promise. p and q are plain
functions, fixed before the function is drawn: they ask no oracle and draw no coin; a parser that
hashes is not of this form. The map of keys is total. The reading draws no coin. The error and the
two budgets do not turn. The two logs are not mapped. Where q gives nothing the new promise holds
vacuously: it claims nothing there, and the check says no there. `comapOpt` and `armVia` have no
caller in this library. `ArmBoundD.reread` (Johnson/Top/ArmsReread.lean) changes reading, check and
promise at ONE type of keys, instances and proofs; `comap` changes these three types: neither is a
case of the other. For arbitrary parameters; over any family of oracles. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ArmsD
import Rom.OverOneN

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP.Gen

open Rom (OSpec Fam)
open Prob (pr expect)

variable {S : OSpec} {X IVK Pf D X' IVK' Pf' : Type}

/-- **A check's bound passes along a map of keys and a map of instance and proof.** A committer of a
key of the new type, followed by p, is a committer of a key of the old type with the same log; so
for a prover and q. -/
theorem ArmBoundD.comap {rd : IVK → Rom.OComp S D} (hrd : ∀ k, (rd k).NoCoin)
    {v : IVK → X → Pf → Rom.OComp S Bool}
    {Holds : D → IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop} {ε : ℕ → ℕ → ℝ≥0∞}
    (h : ArmBoundD rd v Holds ε) (p : IVK' → IVK) (q : X' → Pf' → X × Pf) :
    ArmBoundD (fun k => rd (p k)) (fun k x π => v (p k) (q x π).1 (q x π).2)
      (fun d k trC x π trP => Holds d (p k) trC (q x π).1 (q x π).2 trP) ε := by
  classical
  intro tC tP St Ct Pt hC hP
  have hC' : (Ct.bind fun o => (.pure (p o.1, o.2) : Rom.OComp S (IVK × St))).QueryBound tC :=
    Rom.OComp.QueryBound.bind (t := 0) hC fun _ => trivial
  have hP' : ∀ st,
      ((Pt st).bind fun o => (.pure (q o.1 o.2) : Rom.OComp S (X × Pf))).QueryBound tP :=
    fun st => Rom.OComp.QueryBound.bind (t := 0) (hP st) fun _ => trivial
  refine le_trans ?_ (h tC tP St _ _ hC' hP')
  unfold Rom.Pr
  refine MeasureTheory.lintegral_mono fun f => ?_
  have hp : ∀ (γ : Type) (z : γ),
      Rom.OComp.runEager f (Rom.OComp.pure z : Rom.OComp S γ) = PMF.pure z := fun _ _ => rfl
  have hw : ∀ (γ : Type) (z : γ),
      (Rom.OComp.pure z : Rom.OComp S γ).withTrace = .pure (z, []) := fun _ _ => rfl
  simp only [Rom.PrCoins]
  rw [runEager_armExpD (rd := fun k => rd (p k)) (fun k => hrd (p k)), runEager_armExpD hrd]
  simp only [Rom.withTrace_bind, hw, runEager_bindO, hp, PMF.pure_bind, PMF.bind_bind,
    List.append_nil]
  rw [Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o => ?_
  rw [Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o' => ?_
  rw [Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun b => ?_
  rw [Prob.pr_pure, Prob.pr_pure]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h1.2⟩ h2
  · exact zero_le _
  · exact le_rfl

/-- The check behind a map of keys and a partial map of instance and proof: where q gives nothing it
says no. -/
def armVia (v : IVK → X → Pf → Rom.OComp S Bool) (p : IVK' → IVK) (q : X' → Pf' → Option (X × Pf))
    (k : IVK') (x : X') (π : Pf') : Rom.OComp S Bool :=
  match q x π with
  | some y => v (p k) y.1 y.2
  | none => .pure false

/-- **A check's bound passes along a partial map of instance and proof.** -/
theorem ArmBoundD.comapOpt {rd : IVK → Rom.OComp S D} (hrd : ∀ k, (rd k).NoCoin)
    {v : IVK → X → Pf → Rom.OComp S Bool}
    {Holds : D → IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop} {ε : ℕ → ℕ → ℝ≥0∞}
    (h : ArmBoundD rd v Holds ε) (p : IVK' → IVK) (q : X' → Pf' → Option (X × Pf)) :
    ArmBoundD (fun k => rd (p k)) (armVia v p q)
      (fun d k trC x π trP => ∀ y, q x π = some y → Holds d (p k) trC y.1 y.2 trP) ε := by
  classical
  intro tC tP St Ct Pt hC hP
  have hp : ∀ (f : Fam S) (γ : Type) (z : γ),
      Rom.OComp.runEager f (Rom.OComp.pure z : Rom.OComp S γ) = PMF.pure z := fun _ _ _ => rfl
  have hw : ∀ (γ : Type) (z : γ),
      (Rom.OComp.pure z : Rom.OComp S γ).withTrace = .pure (z, []) := fun _ _ => rfl
  rcases isEmpty_or_nonempty (X × Pf) with hE | ⟨⟨y₀⟩⟩
  · -- q gives nothing anywhere: the arm says no throughout
    refine le_trans ?_ (zero_le _)
    unfold Rom.Pr
    refine le_trans (MeasureTheory.lintegral_mono (g := fun _ => 0) fun f => ?_) (by simp)
    simp only [Rom.PrCoins]
    rw [runEager_armExpD (rd := fun k => rd (p k)) (fun k => hrd (p k)), Prob.pr_bind]
    refine le_trans (Prob.expect_mono _ fun o => ?_) (le_of_eq (Prob.expect_const _ 0))
    rw [Prob.pr_bind]
    refine le_trans (Prob.expect_mono _ fun o' => ?_) (le_of_eq (Prob.expect_const _ 0))
    unfold armVia
    cases hk : q o'.1.1 o'.1.2 with
    | some y => exact (hE.false y).elim
    | none =>
      simp only [hp, PMF.pure_bind]
      rw [Prob.pr_pure, if_neg]
      rintro ⟨ha, -⟩
      exact Bool.noConfusion ha
  have hC' : (Ct.bind fun o => (.pure (p o.1, o.2) : Rom.OComp S (IVK × St))).QueryBound tC :=
    Rom.OComp.QueryBound.bind (t := 0) hC fun _ => trivial
  have hP' : ∀ st, ((Pt st).bind fun o =>
      (.pure ((q o.1 o.2).getD y₀) : Rom.OComp S (X × Pf))).QueryBound tP :=
    fun st => Rom.OComp.QueryBound.bind (t := 0) (hP st) fun _ => trivial
  refine le_trans ?_ (h tC tP St _ _ hC' hP')
  unfold Rom.Pr
  refine MeasureTheory.lintegral_mono fun f => ?_
  simp only [Rom.PrCoins]
  rw [runEager_armExpD (rd := fun k => rd (p k)) (fun k => hrd (p k)), runEager_armExpD hrd]
  simp only [Rom.withTrace_bind, hw, runEager_bindO, hp, PMF.pure_bind, PMF.bind_bind,
    List.append_nil]
  rw [Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o => ?_
  rw [Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o' => ?_
  unfold armVia
  cases hk : q o'.1.1 o'.1.2 with
  | none =>
    simp only [hp, PMF.pure_bind]
    rw [Prob.pr_pure, if_neg]
    · exact zero_le _
    · rintro ⟨ha, -⟩
      exact Bool.noConfusion ha
  | some y =>
    simp only [Option.getD_some]
    rw [Prob.pr_bind, Prob.pr_bind]
    refine Prob.expect_mono _ fun b => ?_
    rw [Prob.pr_pure, Prob.pr_pure]
    split_ifs with h1 h2
    · exact le_rfl
    · refine absurd ⟨h1.1, fun hh => h1.2 fun y' hy' => ?_⟩ h2
      obtain rfl : y = y' := Option.some.inj (hk.symm.trans hy')
      exact hh
    · exact zero_le _
    · exact le_rfl

end ZKCP.Gen

#print axioms ZKCP.Gen.ArmBoundD.comap
#print axioms ZKCP.Gen.ArmBoundD.comapOpt
