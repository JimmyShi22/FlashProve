-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/DryEndsWell.lean: a dry pass of the compiled prover's chain ends in a value, except with
probability at most `capFail`; so does the first pass of the scheme's simulator.

Summary. A dry pass can end in three ways: in a value, in "no format", or with a search that has run
out. E2E/DryRunsOut.lean bounds the third. Here the second is proved to have probability 0, and the
two are joined. The results hold for any rounds with a formatted annotation, any wiring that meets
its conditions, any strategy, coins and search limits, and any mark that selects the Fiat-Shamir
queries with the run's tag (m (.fb t) = true; see E2E/DryRunsOut.lean).

Main results.
  `chain_ends`: the outcome is not a value with probability at most `capFail s A W cap i`.
  `pass1_ends`: the simulator's first pass (`pass1`, Johnson/WholeKey/Wrap.lean) yields no verifier
    messages with probability at most `capFail Q.loc.shape Q.ann wq.sh cap 0`.

Terms: E2E/HidingTerms.lean.

Limits. One slot, one chain. An upper bound. Nothing about the second pass or about any experiment.
No security property is stated.

Definitions and helper lemmas.
  `EvNF`, `tail_nf`, `chain_nf`: with a formatted annotation a dry pass ends in "no format" with
    probability 0. The induction follows `chain_format` (OnBytes/Prover/Returns.lean), under fresh
    answers.


-/
import E2E.DryRunsOut
import OnBytes.Prover.Returns
import Johnson.WholeKey.Wrap

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Shown
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob OnBytes.Prover OnBytes.Dry
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

variable (m : ON₂ → Bool)

local notation "dv" => OComp.dryVal (S := typedOracleFamily lam K L) (fun o _ => m o)

/-! ## 1. With a formatted annotation a dry pass never ends in "no format" -/

/-- The event at the chain: a round has no format. -/
def EvNF (s : Shape) : Set (Res (OutP lam L s)) := {r | r = .noFormat}

theorem tail_nf {r : Round} {s : Shape} (c : r.Chal)
    (kp : r.Msg × List (TreeK lam L) × List (TreeK lam L)) (rq : Option (Dig lam))
    (prog : TypedOracleComputation lam K L (Res (OutP lam L s))) (h : pr (dv prog) (EvNF s) ≤ 0) :
    pr (dv (prog.bind fun u => .pure (u.map (consP c kp rq)))) (EvNF (r :: s)) ≤ 0 := by
  rw [OComp.pr_dryVal_bind_pure]
  exact (pr_mono _ fun u hu => Res.map_eq_noFormat hu).trans h

section Chain
variable (t : Tag) (cms : List (Dig lam)) (x : Option X) (co : Coins lam L) (cap : ℕ → ℕ)

theorem chain_nf : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : Phase lam) (σ : Strat s Unit), RoundSplits.FmtFrom s A (fph ph) →
    pr (dv (chainO t cms x co cap s A W embS embP i ph σ)) (EvNF s) ≤ 0
  | [], A, W, _, _, _, ph, _, _ => le_of_eq (pr_dv_pure m _ _ fun h => by cases h)
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m₁, k), hF => by
    simp only [chainO]
    cases e : actOf cms (x.map L.early) co.salt a.kind ph with
    | none =>
      obtain ⟨hk, hp | hp⟩ := act_none e <;> simp only [RoundSplits.FmtFrom, hk, hp] at hF
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          obtain ⟨hk, hn, -⟩ := act_own e
          simp only [RoundSplits.FmtFrom, hk] at hF
          refine OComp.pr_dryVal_bind_le _ _ _ _ fun TJ => ?_
          refine OComp.pr_dryVal_bind_le _ _ _ _ fun o => ?_
          cases o with
          | none => exact le_of_eq (pr_dv_pure m _ _ fun h => by cases h)
          | some q =>
            exact tail_nf m _ _ _ _ (chain_nf s A W _ _ (i + 1) _ _ (by rw [hn]; exact hF.2))
        | false =>
          obtain ⟨hk, hp, hn, -, -⟩ := act_shared e
          simp only [RoundSplits.FmtFrom, hk, hp] at hF
          refine OComp.pr_dryVal_bind_le _ _ _ _ fun T0 => ?_
          refine OComp.pr_dryVal_bind_le _ _ _ _ fun o => ?_
          cases o with
          | none => exact le_of_eq (pr_dv_pure m _ _ fun h => by cases h)
          | some q =>
            exact tail_nf m _ _ _ _ (chain_nf s A W _ _ (i + 1) _ _ (by rw [hn]; exact hF.2))
      | join ρ₀ =>
        obtain ⟨hk, rfl⟩ := act_join e
        simp only [RoundSplits.FmtFrom, hk, fph] at hF
        refine OComp.pr_dryVal_bind_le _ _ _ _ fun TJ => ?_
        refine OComp.pr_dryVal_bind_le _ _ _ _ fun T0 => ?_
        refine OComp.pr_dryVal_bind_le _ _ _ _ fun c => ?_
        refine OComp.pr_dryVal_bind_le _ _ _ _ fun d => ?_
        refine OComp.pr_dryVal_bind_le _ _ _ _ fun rq => ?_
        refine OComp.pr_dryVal_bind_le _ _ _ _ fun o => ?_
        cases o with
        | none => exact le_of_eq (pr_dv_pure m _ _ fun h => by cases h)
        | some q => exact tail_nf m _ _ _ _ (chain_nf s A W _ _ (i + 1) (.shr _ _) _ hF)

variable (hfb : m (.fb t) = true)
include hfb

/-- **A dry pass of the chain ends in a value, except with probability at most `capFail`.** -/
theorem chain_ends (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : Phase lam) (σ : Strat s Unit) (hW : RoundsQueryLayout.OKG s A W) (hF : RoundSplits.FmtFrom s A (fph ph)) :
    pr (dv (chainO t cms x co cap s A W embS embP i ph σ)) {r | r.toOption = none} ≤
      capFail s A W cap i := by
  refine (pr_mono _ (F := EvOut s ∪ EvNF s) fun r hr => ?_).trans ((pr_union_le _ _ _).trans ?_)
  · cases r with
    | ok z => cases hr
    | noFormat => exact Or.inr rfl
    | ranOut j => exact Or.inl ⟨j, rfl⟩
  · calc _ ≤ capFail s A W cap i + 0 :=
          add_le_add (chain_out m t hfb cms x co cap s A W embS embP i ph σ hW)
            (chain_nf m t cms x co cap s A W embS embP i ph σ hF)
      _ = _ := add_zero _

end Chain

/-! ## 2. The simulator's first pass -/

section Pass
variable (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms : List (Dig lam)) (x : Y) (cap : ℕ → ℕ) (co : Coins lam L)

/-- **The first pass of a simulated compiled run (`pass1`, Johnson/WholeKey/Wrap.lean) yields
verifier messages, except with probability at most `capFail`.** -/
theorem pass1_ends (hW : RoundsQueryLayout.OKG Q.loc.shape Q.ann wq.sh) (hF : Q.ann.Fmt) :
    pr (OnBytes.WholeKey.pass1 t Q wq embS embP xin cms x cap co) {a | a.1.toOption = none} ≤
      capFail Q.loc.shape Q.ann wq.sh cap 0 := by
  unfold OnBytes.WholeKey.pass1
  rw [OComp.record_bind_pure, pr_map]
  refine (pr_mono _ fun z hz => ?_).trans ((le_of_eq (OComp.pr_record (S := typedOracleFamily lam K L)
    OnBytes.WholeKey.mkRun (OnBytes.WholeKey.chainX t Q wq embS embP xin cms x cap
      (Strat.dflt _ ()) co) {r | r.toOption = none})).trans
    (chain_ends OnBytes.WholeKey.lateRun t cms (xin x) co cap rfl Q.loc.shape Q.ann wq.sh embS embP
      0 .first (Strat.dflt _ ()) hW hF))
  obtain ⟨u, R⟩ := z
  cases u with
  | ok w => cases hz
  | noFormat => rfl
  | ranOut j => rfl

end Pass

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.tail_nf
#print axioms AtPublicFiles.Shown.chain_nf
#print axioms AtPublicFiles.Shown.chain_ends
#print axioms AtPublicFiles.Shown.pass1_ends
