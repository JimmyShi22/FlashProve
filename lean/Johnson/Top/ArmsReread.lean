-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsReread.lean: a check's bound with a public reading (`ZKCP.Gen.ArmBoundD`,
Johnson/Top/ArmsD.lean; the reading rd is a parameter: a computation that queries the hash function)
carried along a change of the reading, of the check and of the promise, at one key; and so the three
checks' bounds, each had at its own reading and word, brought to one.

What this file states. `CoreArmsCD b` (Johnson/Top/OnFilesArmsCD.lean) requires the three checks'
bounds at ONE reading `b.rd`, one type of its values and one word under a root `b.wordOf`. The
intended checks read different lists of public digests: the entry file's two, the other two files'
more. A bound is had most easily at the reading that its own check runs.
  `ZKCP.Gen.ArmBoundD.reread`: under the hypotheses below, a bound of v with Holds at rd is a bound
    of v' with Holds' at rd', at the same ε.
  `coreArmsCD_of_three`: under the hypotheses below, the three checks' bounds at three records of
    remaining data bK, bE, bP (`BesideArmsCD r`), each with `SameWord` to b, give `CoreArmsCD b`, at
    b's three errors.

Under which hypotheses.
  `ZKCP.Gen.ArmBoundD.reread`: readings rd, rd' and checks v, v' that toss no coin. hy: at every f,
    where v' says yes, v says yes. hv: at every f, where v' says yes, the promise Holds at rd's
    value gives the promise Holds' at rd' 's value.
  `SameWord a b`: at every f and key, a's word at its reading's value is b's word at b's.
  `coreArmsCD_of_three` takes in addition: `reading` (b's reading tosses no coin and makes at most
    `b.q₀` queries), `noCoin` (`HoleArmsC.noCoin r`), rK, rE, rP (the readings of bK, bE, bP toss no
    coin) and hR (`IsTrueArmsCD bP i x` gives `IsTrueArmsCD b i x`).

What it does not show. All is for arbitrary parameters; every premise is a hypothesis; no bound,
reading or word is given. `SameWord` is a law on the codings through which the words are read: it
requires that what the one reading gives beyond the other does not turn the word. It is shown of no
coding here, and it can be false. The experiment of a bound runs the reading behind committer and
prover, and its queries are counted for nobody: so a change of the reading costs nothing in ε; b's
own reading must still meet its budget (`reading`). The step is pointwise in f: it uses that
readings and checks have one value at fixed f. Soundness alone. For proofs only; the program does
not import this file.


-/
import Johnson.Top.OnFilesArmsCD

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace ZKCP.Gen

open Rom (OSpec Fam)
open Prob (pr expect)

variable {S : OSpec} {X IVK Pf D D' : Type}

/-- A bound passes along a change of reading, check and promise, at one key and the same ε. -/
theorem ArmBoundD.reread {rd : IVK → Rom.OComp S D} {rd' : IVK → Rom.OComp S D'}
    (hrd : ∀ k, (rd k).NoCoin) (hrd' : ∀ k, (rd' k).NoCoin)
    {v v' : IVK → X → Pf → Rom.OComp S Bool} (hn : ∀ k x π, (v k x π).NoCoin)
    (hn' : ∀ k x π, (v' k x π).NoCoin)
    {Holds : D → IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop}
    {Holds' : D' → IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop} {ε : ℕ → ℕ → ℝ≥0∞}
    (hy : ∀ (f : Fam S) k x π, (v' k x π).det f = true → (v k x π).det f = true)
    (hv : ∀ (f : Fam S) k x π, (v' k x π).det f = true → ∀ trC trP,
      Holds ((rd k).det f) k trC x π trP → Holds' ((rd' k).det f) k trC x π trP)
    (h : ArmBoundD rd v Holds ε) : ArmBoundD rd' v' Holds' ε := by
  classical
  intro tC tP St Ct Pt hC hP
  refine le_trans ?_ (h tC tP St Ct Pt hC hP)
  unfold Rom.Pr
  refine MeasureTheory.lintegral_mono fun f => ?_
  have hr : ∀ k x π, (v k x π).runEager f = PMF.pure ((v k x π).det f) :=
    fun k x π => (hn k x π).runEager f
  have hr' : ∀ k x π, (v' k x π).runEager f = PMF.pure ((v' k x π).det f) :=
    fun k x π => (hn' k x π).runEager f
  simp only [Rom.PrCoins]
  rw [runEager_armExpD hrd', runEager_armExpD hrd]
  simp only [hr, hr', PMF.pure_bind]
  rw [Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o => ?_
  rw [Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o' => ?_
  rw [Prob.pr_pure, Prob.pr_pure]
  by_cases hb : (⟨(v' o.1.1 o'.1.1 o'.1.2).det f, o.1.1, o.2, o'.1.1, o'.1.2, o'.2,
      (rd' o.1.1).det f⟩ : ArmOutD S X IVK Pf D') ∈ armBadD Holds'
  · rw [if_pos hb, if_pos]
    exact ⟨hy f _ _ _ hb.1, fun hH => hb.2 (hv f _ _ _ hb.1 _ _ hH)⟩
  · rw [if_neg hb]
    exact zero_le _

end ZKCP.Gen

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {r : InputArmsC}

/-- At every f and key: a's word at its reading's value is b's word at b's reading's value. -/
def SameWord (a b : BesideArmsCD r) : Prop :=
  ∀ (f : Fam (rom 256)) k tr cm,
    a.wordOf ((a.rd k).det f) tr cm = b.wordOf ((b.rd k).det f) tr cm

/-- **The three checks' bounds, each at its own reading and word, give the five named hypotheses at
one.** -/
theorem coreArmsCD_of_three {b bK bE bP : BesideArmsCD r}
    (reading : ∀ k, (b.rd k).NoCoin ∧ (b.rd k).QueryBound b.q₀) (noCoin : HoleArmsC.noCoin r)
    (rK : ∀ k, (bK.rd k).NoCoin) (rE : ∀ k, (bE.rd k).NoCoin) (rP : ∀ k, (bP.rd k).NoCoin)
    (wK : SameWord bK b) (wE : SameWord bE b) (wP : SameWord bP b)
    (hR : ∀ i x, IsTrueArmsCD bP i x → IsTrueArmsCD b i x)
    (keyArm : ZKCP.Gen.ArmBoundD bK.rd (liftKC r) (KeyHoldsCD bK) b.εK)
    (entryArm : ZKCP.Gen.ArmBoundD bE.rd (liftEC r) (EntryHoldsCD bE) b.εE)
    (proofArm : ZKCP.Gen.ArmBoundD bP.rd (liftPC r) (ProofHoldsCD bP) b.εP) : CoreArmsCD b := by
  obtain ⟨a1, a2, a3⟩ := noCoin
  have c1 : ∀ k x π, (liftKC r k x π).NoCoin := fun k x π => by
    unfold liftKC
    split
    · exact a1 _ _ _ _
    · trivial
  have c2 : ∀ k x π, (liftEC r k x π).NoCoin := fun k x π => by
    unfold liftEC
    split
    · exact a2 _ _ _ _ _ _
    · trivial
  have c3 : ∀ k x π, (liftPC r k x π).NoCoin := fun k x π => by
    unfold liftPC
    split
    · exact a3 _ _ _ _ _ _
    · trivial
  refine ⟨?_, ?_, ?_, reading, a1, a2, a3⟩
  · refine ZKCP.Gen.ArmBoundD.reread rK (fun k => (reading k).1) c1 c1 (fun _ _ _ _ h => h)
      (fun f k x π _ trC trP hH => ?_) keyArm
    unfold KeyHoldsCD at hH ⊢
    simp only [wK f k] at hH
    exact hH
  · refine ZKCP.Gen.ArmBoundD.reread rE (fun k => (reading k).1) c2 c2 (fun _ _ _ _ h => h)
      (fun f k x π _ trC trP hH => ?_) entryArm
    unfold EntryHoldsCD at hH ⊢
    simp only [wE f k] at hH
    exact hH
  · refine ZKCP.Gen.ArmBoundD.reread rP (fun k => (reading k).1) c3 c3 (fun _ _ _ _ h => h)
      (fun f k x π _ trC trP hH => ?_) proofArm
    unfold ProofHoldsCD at hH ⊢
    simp only [wP f k] at hH
    rcases hH with h | h | ⟨i, hi, ht⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨i, hi, hR i x ht⟩)

end VerifiableInference.OnPublicFiles

#print axioms ZKCP.Gen.ArmBoundD.reread
#print axioms VerifiableInference.OnPublicFiles.coreArmsCD_of_three
