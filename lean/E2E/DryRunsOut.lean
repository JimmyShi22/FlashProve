-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/DryRunsOut.lean: in a dry pass of the compiled prover's chain, a proof-of-work search runs out
with probability at most `capFail`.

Summary. A dry pass runs the chain (`chainO`, OnBytes/Prover/Defs.lean) without a table of answers
(`OComp.record`, Rom/Handle/Defs.lean): a mark m selects the deferred oracle queries, which get
fresh uniform samples, and every other query gets an arbitrary fixed value. The results assume that
the mark selects the Fiat-Shamir queries with the run's tag: m (.fb t) = true. It is the first pass
of the scheme's simulator (Johnson/WholeKey/Sim.lean): where its search runs out, the simulator
produces no proof. `capFail` (Johnson/Prover/Law/Defs.lean) is the sum, over the rounds with a test,
of (1 - 2 ^ -b) ^ (cap i + 1). OnBytes/Dry/ChainLaw.lean bounds the event "no search runs out and
the verifier messages lie in B", and notes that nothing there proves that a run ends well. The
result holds for any rounds, any wiring that meets its conditions, and any strategy, coins and
search limits.

Main results.
  `chain_out`: the bound, for every (remaining rounds, number of the first, phase).
  `rhoO_out`: the same for the first pass's program with the answers that it has kept (`rhoO`,
    OnBytes/Dry/Spec.lean).

How. The induction follows that of OnBytes/Dry/ChainLaw.lean, with the other event. In a dry pass a
Fiat-Shamir query gets a fresh uniform answer whatever its point is (`dv_ask`), so no premise is
needed on a table of answers, on the numbers that a search tries, or on how plain parts are written
into queries. The average over "sample until the test is passed" is `mean_le`
(Johnson/Prover/Law/Round.lean).

Terms: E2E/HidingTerms.lean.

Limits. One slot, one chain. An upper bound. "No format" is another outcome, and nothing is proved
about it here. Nothing about the simulator as a whole: no second pass and no experiment. No security
property is stated.

Definitions and helper lemmas.
  `EvOut s`: the event that a search has run out.
  `search_out_le`, `fs_out_le`, `tail_out_le`: the steps of the induction.


-/
import OnBytes.Dry.ChainLaw
import Johnson.Prover.Law.Defs

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Shown
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob OnBytes.Prover OnBytes.Dry
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Batch.LoopLazy (obind_assoc)
open scoped ENNReal

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

variable (m : ON₂ → Bool)

local notation "dv" => OComp.dryVal (S := typedOracleFamily lam K L) (fun o _ => m o)

/-! ## 1. The search, and a Fiat-Shamir query, with what follows -/

section Fs
variable {C P γ : Type} (chal : (Fin K → Dig lam) → C) (t : Tag) (hfb : m (.fb t) = true)
  (qf : P → FbIn lam L t) (α : P) (k : Option (P × FsAns lam K) → TypedOracleComputation lam K L γ) (E : Set γ)
include hfb

/-- The search, with what follows it: where it runs out the bound is 1. -/
theorem search_out_le (gr : GrW C P) (φ : FsAns lam K → ℝ≥0∞)
    (hk : ∀ n ans, gr.ok (chal ans.1) = true → pr (dv (k (some (gr.put n α, ans)))) E ≤ φ ans) :
    ∀ n j : ℕ,
      pr (dv ((searchO gr chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qf β)) α (n + 1) j).bind
          k)) E ≤
        expect (retry (fun a : FsAns lam K => gr.ok (chal a.1)) n) fun a =>
          if gr.ok (chal a.1) then φ a else 1
  | 0, j => by
    rw [searchO, obind_assoc]
    refine (pr_dv_ask m t hfb _ _ E).trans_le ?_
    refine expect_mono _ fun ans => ?_
    by_cases ho : gr.ok (chal ans.1) = true
    · rw [if_pos ho, if_pos ho]
      exact hk j ans ho
    · rw [if_neg ho, if_neg ho]
      exact pr_le_one _ _
  | n + 1, j => by
    rw [searchO, obind_assoc, retry, expect_bind]
    refine (pr_dv_ask m t hfb _ _ E).trans_le ?_
    refine expect_mono _ fun ans => ?_
    by_cases ho : gr.ok (chal ans.1) = true
    · rw [if_pos ho, if_pos ho, expect_pure, if_pos ho]
      exact hk j ans ho
    · rw [if_neg ho, if_neg ho]
      exact search_out_le gr φ hk n (j + 1)

/-- **A Fiat-Shamir query, with what follows it.** -/
theorem fs_out_le [Fintype C] [Nonempty C] (gr : Option (GrW C P)) (cap : ℕ) (ε : ℝ≥0∞)
    (hgr : ∀ g, gr = some g → g.OK) (hc : (unif (Fin K → Dig lam)).map chal = unif C)
    (hk : ∀ β ans, pr (dv (k (some (β, ans)))) E ≤ ε) :
    pr (dv ((fsO gr cap chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qf β)) α).bind k)) E ≤
      ε + grFailAt cap gr := by
  cases gr with
  | none =>
    show pr (dv (((askTypedOracle (L := L) (K := K) (OracleName.fb t) (qf α)).bind fun a =>
      OComp.pure (some (α, a))).bind k)) E ≤ ε + 0
    rw [obind_assoc, add_zero]
    refine (pr_dv_ask m t hfb _ _ E).trans_le ?_
    exact expect_le_of_forall_le _ fun ans _ => hk α ans
  | some g =>
    refine (search_out_le m chal t hfb qf α k E g (fun _ => ε) (fun n ans _ => hk _ ans) cap
      0).trans ((mean_le g chal (hgr g rfl) hc (fun _ => ε) cap).trans ?_)
    exact add_le_add (expect_le_of_forall_le _ fun _ _ => le_rfl) le_rfl

end Fs

/-! ## 2. The chain -/

/-- The event at the chain: a search has run out. -/
def EvOut (s : Shape) : Set (Res (OutP lam L s)) := {r | ∃ j, r = .ranOut j}

theorem tail_out_le {r : Round} {s : Shape} (c : r.Chal)
    (kp : r.Msg × List (TreeK lam L) × List (TreeK lam L)) (rq : Option (Dig lam))
    (prog : TypedOracleComputation lam K L (Res (OutP lam L s))) {ε : ℝ≥0∞} (h : pr (dv prog) (EvOut s) ≤ ε) :
    pr (dv (prog.bind fun u => .pure (u.map (consP c kp rq)))) (EvOut (r :: s)) ≤ ε := by
  rw [OComp.pr_dryVal_bind_pure]
  refine (pr_mono _ fun u hu => ?_).trans h
  obtain ⟨j, e⟩ := hu
  cases u with
  | ok z => cases e
  | noFormat => cases e
  | ranOut j' => exact ⟨j', rfl⟩

section Chain
variable (t : Tag) (hfb : m (.fb t) = true) (cms : List (Dig lam)) (x : Option X)
  (co : Coins lam L) (cap : ℕ → ℕ)
include hfb

/-- **In a dry pass of the chain a search runs out with probability at most `capFail`.** -/
theorem chain_out : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : Phase lam) (σ : Strat s Unit), RoundsQueryLayout.OKG s A W →
    pr (dv (chainO t cms x co cap s A W embS embP i ph σ)) (EvOut s) ≤ capFail s A W cap i
  | [], A, W, _, _, _, ph, _, _ =>
    le_of_eq_of_le (pr_dv_pure m _ _ fun h => by
      obtain ⟨j, e⟩ := h
      cases e) (zero_le _)
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m₁, k), hW => by
    simp only [chainO]
    cases e : actOf cms (x.map L.early) co.salt a.kind ph with
    | none =>
      exact le_of_eq_of_le (pr_dv_pure m _ _ fun h => by
        obtain ⟨j, e'⟩ := h
        cases e') (zero_le _)
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          have hk := (act_own e).1
          refine OComp.pr_dryVal_bind_le _ _ _ _ fun TJ => ?_
          refine (fs_out_le m w.chal t hfb
            (fun β => (⟨i, h.withLate (lateInstancePart L i x), TJ.map TreeK.root, embP (.inl (.inr β))⟩ :
              FbIn lam L t)) (a.plain m₁.2).2 _ (EvOut (r :: s)) w.grJ (cap i)
            (capFail s A W cap (i + 1)) hW.1.grJ_ok hW.1.chal_unif fun β ans => ?_).trans ?_
          · exact tail_out_le m _ _ _ _ (chain_out s A W _ _ (i + 1) _ _ hW.2)
          · show _ ≤ (match a.kind with
              | .lo => grFailAt (cap i) w.grJ
              | .sh => grFailAt (cap i) w.gr0) + capFail s A W cap (i + 1)
            rw [hk, add_comm]
        | false =>
          have hk := (act_shared e).1
          refine OComp.pr_dryVal_bind_le _ _ _ _ fun T0 => ?_
          refine (fs_out_le m w.chal t hfb
            (fun β => (⟨i, h, T0.map TreeK.root, embP (.inl (.inl β))⟩ : FbIn lam L t))
            (a.plain m₁.2).1 _ (EvOut (r :: s)) w.gr0 (cap i)
            (capFail s A W cap (i + 1)) hW.1.gr0_ok hW.1.chal_unif fun β ans => ?_).trans ?_
          · exact tail_out_le m _ _ _ _ (chain_out s A W _ _ (i + 1) _ _ hW.2)
          · show _ ≤ (match a.kind with
              | .lo => grFailAt (cap i) w.grJ
              | .sh => grFailAt (cap i) w.gr0) + capFail s A W cap (i + 1)
            rw [hk, add_comm]
      | join ρ₀ =>
        have hk := (act_join e).1
        refine OComp.pr_dryVal_bind_le _ _ _ _ fun TJ => ?_
        refine OComp.pr_dryVal_bind_le _ _ _ _ fun T0 => ?_
        refine OComp.pr_dryVal_bind_le _ _ _ _ fun c => ?_
        refine OComp.pr_dryVal_bind_le _ _ _ _ fun d => ?_
        refine OComp.pr_dryVal_bind_le _ _ _ _ fun rq => ?_
        refine (fs_out_le m w.chal t hfb
          (fun β => (⟨i, .f4 cms (List.ofFn rq), T0.map TreeK.root, embP (.inl (.inl β))⟩ :
            FbIn lam L t)) (a.plain m₁.2).1 _ (EvOut (r :: s)) w.gr0 (cap i)
          (capFail s A W cap (i + 1)) hW.1.gr0_ok hW.1.chal_unif fun β ans => ?_).trans ?_
        · exact tail_out_le m _ _ _ _ (chain_out s A W _ _ (i + 1) _ _ hW.2)
        · show _ ≤ (match a.kind with
            | .lo => grFailAt (cap i) w.grJ
            | .sh => grFailAt (cap i) w.gr0) + capFail s A W cap (i + 1)
          rw [hk, add_comm]

/-- **The same for the first pass's program with the answers that it has kept** (`rhoO`,
OnBytes/Dry/Spec.lean). -/
theorem rhoO_out (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : Phase lam) (σ : Strat s Unit) (hW : RoundsQueryLayout.OKG s A W) :
    pr ((rhoO t cms x co cap s A W embS embP i ph σ).record (S := typedOracleFamily lam K L) fun o _ => m o)
        {z | ∃ j, z.1 = .ranOut j} ≤ capFail s A W cap i := by
  unfold rhoO
  rw [OComp.record_bind_pure, pr_map]
  refine (pr_mono _ fun z hz => ?_).trans ((le_of_eq (OComp.pr_record (S := typedOracleFamily lam K L)
    (fun o _ => m o) (chainO t cms x co cap s A W embS embP i ph σ) (EvOut s))).trans
    (chain_out m t hfb cms x co cap s A W embS embP i ph σ hW))
  obtain ⟨j, e⟩ := hz
  obtain ⟨u, R⟩ := z
  cases u with
  | ok w => cases e
  | noFormat => cases e
  | ranOut j' => exact ⟨j', rfl⟩

end Chain

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.search_out_le
#print axioms AtPublicFiles.Shown.fs_out_le
#print axioms AtPublicFiles.Shown.tail_out_le
#print axioms AtPublicFiles.Shown.chain_out
#print axioms AtPublicFiles.Shown.rhoO_out
