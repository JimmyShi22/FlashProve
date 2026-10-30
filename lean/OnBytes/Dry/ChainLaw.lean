-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Dry/ChainLaw.lean: THE LAW OF THE VERIFIER MESSAGES OF A DRY PASS of the chain of the
compiled prover of one slot (chainO, OnBytes/Prover/Defs.lean): no search for a nonce runs out AND
the verifier messages lie in a set B with probability at most the uniform measure of B, the test
bits set to 0. It proves Spec.chainLawDry (OnBytes/Dry/Spec.lean).

General lemmas. This file states no goal of the release.

How. It follows the pattern of the law of the prover's outcome under lazily sampled oracles
(Johnson/Prover/Law/Search.lean, Round.lean, Chain.lean: search_le, mean_le, fs_le, tail_le,
chain_law), and calls that pattern's lemmas on a test under a uniform answer (chalA, ok_ind,
set_of_ok, zeroOf, zero_lo, zero_sh) and on sampling again (Prob/Retry.lean). What differs: in a dry
pass a Fiat-Shamir query gets a fresh uniform answer whatever its point is, so nothing is asked of a
table, of the numbers that a search tries, or of how plain parts are written into queries; and the
event leaves out the runs in which a search runs out, so no term for a failed search stands in the
bound.

Round by round (chain_dry). What a round asks before its Fiat-Shamir query (trees; at the joining
round g and the request tree) is passed over: the bound holds after every outcome of it. The search
is "sample until the test is passed"; the verifier message with its test bits set to 0 is
independent of the test, so over the runs in which the search ends well it is at most uniform. The
mean over the round's verifier message is one step of Fubini.

Main names.
  EvOk   the event at the chain: a value, whose verifier messages lie in B.
  dv_ask, pr_dv_pure, pr_dv_ask, not_evOk_ranOut, not_evOk_noFormat, search_dry_le, mean_dry_le,
         fs_dry_le, tail_dry_le, slice_eq   the steps.
  chain_dry      the law at every (rounds that are left, number of the first, phase).
  chainLawDry    THE STATEMENT: Spec.chainLawDry.
  chainLawDry_rhoO   the same for the first pass's program (rhoO, OnBytes/Dry/Spec.lean).

Limits. One slot, one chain. B is a letter: nothing says that any B is small. The law is a bound
from above, with the constant 1, on the runs that end well; it is no equation and no law under a
condition, and nothing here says that any run ends well: the left side may be 0.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Dry.Spec
import Rom.Dry.Val
import Johnson.Prover.Law.Chain

set_option autoImplicit false

noncomputable section

namespace OnBytes.Dry
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Batch.LoopLazy (obind_assoc)
open scoped ENNReal

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The names of the typed oracles. -/
local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

variable (m : ON₂ → Bool)

/-- the law of the output of a dry run over the typed oracles, "deferred" by the oracle's name -/
local notation "dv" => OComp.dryVal (S := typedOracleFamily lam K L) (fun o _ => m o)

/-! ## Steps along a program -/

theorem pr_dv_pure {α : Type} (a : α) (E : Set α) (h : a ∉ E) :
    pr (dv (OComp.pure a)) E = 0 := by
  classical
  rw [OComp.dryVal_pure, pr_pure, if_neg h]

/-- A Fiat-Shamir query is answered by a fresh uniform draw, whatever its point is. -/
theorem dv_ask {γ : Type} (t : Tag) (hfb : m (.fb t) = true) (q : FbIn lam L t)
    (k : FsAns lam K → TypedOracleComputation lam K L γ) :
    dv ((askTypedOracle (L := L) (K := K) (OracleName.fb t) q).bind k) =
      (unif (FsAns lam K)).bind fun a => dv (k a) :=
  OComp.dryVal_query_mark (S := typedOracleFamily lam K L) (fun o _ => m o) (o := OracleName.fb t) (q := q) hfb k

theorem pr_dv_ask {γ : Type} (t : Tag) (hfb : m (.fb t) = true) (q : FbIn lam L t)
    (k : FsAns lam K → TypedOracleComputation lam K L γ) (E : Set γ) :
    pr (dv ((askTypedOracle (L := L) (K := K) (OracleName.fb t) q).bind k)) E =
      expect (unif (FsAns lam K)) fun a => pr (dv (k a)) E :=
  (congrArg (fun p => pr p E) (dv_ask m t hfb q k)).trans (pr_bind _ _ _)

/-! ## The search, and a Fiat-Shamir query, with what follows -/

section Fs
variable {C P γ : Type} (chal : (Fin K → Dig lam) → C) (t : Tag) (hfb : m (.fb t) = true)
  (qf : P → FbIn lam L t) (α : P) (k : Option (P × FsAns lam K) → TypedOracleComputation lam K L γ) (E : Set γ)
include hfb

/-- **The search, with what follows it.** h0: after a search that has run out the event does not
happen. hk: after a passed try it has probability at most φ of the answer. -/
theorem search_dry_le (gr : GrW C P) (φ : FsAns lam K → ℝ≥0∞) (h0 : pr (dv (k none)) E = 0)
    (hk : ∀ n ans, gr.ok (chal ans.1) = true → pr (dv (k (some (gr.put n α, ans)))) E ≤ φ ans) :
    ∀ n j : ℕ,
      pr (dv ((searchO gr chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qf β)) α (n + 1) j).bind
          k)) E ≤
        expect (retry (fun a : FsAns lam K => gr.ok (chal a.1)) n) fun a =>
          if gr.ok (chal a.1) then φ a else 0
  | 0, j => by
    rw [searchO, obind_assoc]
    refine (pr_dv_ask m t hfb _ _ E).trans_le ?_
    refine expect_mono _ fun ans => ?_
    by_cases ho : gr.ok (chal ans.1) = true
    · rw [if_pos ho, if_pos ho]
      exact hk j ans ho
    · rw [if_neg ho, if_neg ho]
      exact le_of_eq h0
  | n + 1, j => by
    rw [searchO, obind_assoc, retry, expect_bind]
    refine (pr_dv_ask m t hfb _ _ E).trans_le ?_
    refine expect_mono _ fun ans => ?_
    by_cases ho : gr.ok (chal ans.1) = true
    · rw [if_pos ho, if_pos ho, expect_pure, if_pos ho]
      exact hk j ans ho
    · rw [if_neg ho, if_neg ho]
      exact search_dry_le gr φ h0 hk n (j + 1)

omit hfb in
/-- **The mean over "sample until the test is passed", over the runs that end well.** -/
theorem mean_dry_le [Fintype C] [Nonempty C] (g : GrW C P) (hg : g.OK)
    (hc : (unif (Fin K → Dig lam)).map chal = unif C) (ψ : C → ℝ≥0∞) (n : ℕ) :
    (expect (retry (fun a : FsAns lam K => g.ok (chal a.1)) n) fun a =>
        if g.ok (chal a.1) then ψ (chal a.1) else 0) ≤
      expect (unif C) fun c => ψ (g.set (fun _ => false) c) := by
  have h2 := map_retry (fun a : FsAns lam K => g.ok (chal a.1))
    (fun a : FsAns lam K => g.set (fun _ => false) (chal a.1)) (ok_ind g chal hg hc) n
  have hA : (expect (unif C) fun c => ψ (g.set (fun _ => false) c)) =
      expect (retry (fun a : FsAns lam K => g.ok (chal a.1)) n) fun a =>
        ψ (g.set (fun _ => false) (chal a.1)) := by
    rw [← expect_map (retry (fun a : FsAns lam K => g.ok (chal a.1)) n)
        (fun a : FsAns lam K => g.set (fun _ => false) (chal a.1)) ψ, h2,
      show (fun a : FsAns lam K => g.set (fun _ => false) (chal a.1)) =
        (g.set fun _ => false) ∘ fun a : FsAns lam K => chal a.1 from rfl,
      ← PMF.map_comp, chalA chal hc, expect_map]
  rw [hA]
  refine expect_mono _ fun a => ?_
  by_cases ho : g.ok (chal a.1) = true
  · exact le_of_eq (by rw [if_pos ho, set_of_ok g hg ho])
  · rw [if_neg ho]
    exact zero_le _

/-- **A Fiat-Shamir query, with what follows it.** -/
theorem fs_dry_le [Fintype C] [Nonempty C] (gr : Option (GrW C P)) (cap : ℕ) (ψ : C → ℝ≥0∞)
    (hgr : ∀ g, gr = some g → g.OK) (hc : (unif (Fin K → Dig lam)).map chal = unif C)
    (h0 : pr (dv (k none)) E = 0)
    (hk : ∀ β ans, pr (dv (k (some (β, ans)))) E ≤ ψ (chal ans.1)) :
    pr (dv ((fsO gr cap chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qf β)) α).bind k)) E ≤
      expect (unif C) fun c => ψ (zeroOf gr c) := by
  cases gr with
  | none =>
    show pr (dv (((askTypedOracle (L := L) (K := K) (OracleName.fb t) (qf α)).bind fun a =>
      OComp.pure (some (α, a))).bind k)) E ≤ _
    rw [obind_assoc]
    refine (pr_dv_ask m t hfb _ _ E).trans_le ?_
    show _ ≤ expect (unif C) fun c => ψ c
    rw [← chalA chal hc, expect_map]
    exact expect_mono _ fun ans => hk α ans
  | some g =>
    exact (search_dry_le m chal t hfb qf α k E g (fun a => ψ (chal a.1)) h0
      (fun n ans _ => hk _ ans) cap 0).trans (mean_dry_le chal g (hgr g rfl) hc ψ cap)

end Fs

/-! ## The chain -/

/-- The event at the chain: a value, whose verifier messages lie in B. -/
def EvOk (s : Shape) (B : Set (Rho s)) : Set (Res (OutP lam L s)) :=
  {r | ∃ z, r = .ok z ∧ z.1 ∈ B}

/-- what follows a round's Fiat-Shamir query: the rest of the chain, at the slice of B -/
theorem tail_dry_le {r : Round} {s : Shape} (B : Set (Rho (r :: s))) (c : r.Chal)
    (kp : r.Msg × List (TreeK lam L) × List (TreeK lam L)) (rq : Option (Dig lam))
    (prog : TypedOracleComputation lam K L (Res (OutP lam L s))) {ε : ℝ≥0∞}
    (h : pr (dv prog) (EvOk s {ρ | ((c, ρ) : Rho (r :: s)) ∈ B}) ≤ ε) :
    pr (dv (prog.bind fun u => .pure (u.map (consP c kp rq)))) (EvOk (r :: s) B) ≤ ε := by
  rw [OComp.pr_dryVal_bind_pure]
  refine (pr_mono _ fun u hu => ?_).trans h
  cases u with
  | ok z =>
    obtain ⟨z', e, hz⟩ := hu
    obtain rfl : consP c kp rq z = z' := Res.ok.inj e
    exact ⟨z, rfl, hz⟩
  | noFormat =>
    obtain ⟨z', e, -⟩ := hu
    cases e
  | ranOut j =>
    obtain ⟨z', e, -⟩ := hu
    cases e

/-- one step of Fubini -/
theorem slice_eq {r : Round} {s : Shape} (B : Set (Rho (r :: s))) (f : r.Chal → r.Chal)
    (F : Rho s → Rho s) :
    (expect (unif r.Chal) fun c =>
        pr (unif (Rho s)) {ρ | F ρ ∈ {ρ' | ((f c, ρ') : Rho (r :: s)) ∈ B}}) =
      pr (unif (Rho (r :: s))) {ρ : Rho (r :: s) | ((f ρ.1, F ρ.2) : Rho (r :: s)) ∈ B} := by
  symm
  show pr (unif (r.Chal × Rho s)) _ = _
  rw [unif_prod, pr_prod]
  rfl

theorem not_evOk_ranOut (s : Shape) (B : Set (Rho s)) (i : ℕ) :
    (Res.ranOut i : Res (OutP lam L s)) ∉ EvOk s B := fun h => by
  obtain ⟨z, e, -⟩ := h
  cases e

theorem not_evOk_noFormat (s : Shape) (B : Set (Rho s)) :
    (Res.noFormat : Res (OutP lam L s)) ∉ EvOk s B := fun h => by
  obtain ⟨z, e, -⟩ := h
  cases e

section Chain
variable (t : Tag) (hfb : m (.fb t) = true) (cms : List (Dig lam)) (x : Option X)
  (co : Coins lam L) (cap : ℕ → ℕ)
include hfb

/-- **The law at the chain.** -/
theorem chain_dry : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : Phase lam) (σ : Strat s Unit), RoundsQueryLayout.OKG s A W → ∀ B : Set (Rho s),
    pr (dv (chainO t cms x co cap s A W embS embP i ph σ)) (EvOk s B) ≤
      pr (unif (Rho s)) {ρ | RoundsQueryLayout.zero s A W ρ ∈ B}
  | [], A, W, _, _, _, ph, _, _, B => by
    by_cases hB : (() : Rho []) ∈ B
    · refine (pr_le_one _ _).trans (le_of_eq ?_)
      have : {ρ : Rho [] | TypedOracleCompiler.Iop.RoundsQueryLayout.zero [] A W ρ ∈ B} = Set.univ :=
        Set.eq_univ_of_forall fun _ => hB
      rw [this]
      exact ((PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)).symm
    · refine le_of_eq_of_le (pr_dv_pure m _ _ fun h => ?_) (zero_le _)
      obtain ⟨z, e, hz⟩ := h
      obtain rfl := Res.ok.inj e
      exact hB hz
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m₁, k), hW, B => by
    simp only [chainO]
    cases e : actOf cms (x.map L.early) co.salt a.kind ph with
    | none => exact le_of_eq_of_le (pr_dv_pure m _ _ (not_evOk_noFormat _ _)) (zero_le _)
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          have hk := (act_own e).1
          refine OComp.pr_dryVal_bind_le _ _ _ _ fun TJ => ?_
          refine (fs_dry_le m w.chal t hfb
            (fun β => (⟨i, h.withLate (lateInstancePart L i x), TJ.map TreeK.root, embP (.inl (.inr β))⟩ :
              FbIn lam L t)) (a.plain m₁.2).2 _ (EvOk (r :: s) B) w.grJ (cap i)
            (fun c => pr (unif (Rho s))
              {ρ | RoundsQueryLayout.zero s A W ρ ∈ {ρ' | ((c, ρ') : Rho (r :: s)) ∈ B}})
            hW.1.grJ_ok hW.1.chal_unif ?_ fun β ans => ?_).trans ?_
          · exact pr_dv_pure m _ _ (not_evOk_ranOut _ _ _)
          · exact tail_dry_le m B _ _ _ _ (chain_dry s A W _ _ (i + 1) _ _ hW.2 _)
          · rw [slice_eq B (zeroOf w.grJ) (RoundsQueryLayout.zero s A W)]
            refine le_of_eq (congrArg (pr _) (Set.ext fun ρ => ?_))
            show ((zeroOf w.grJ ρ.1, RoundsQueryLayout.zero s A W ρ.2) : Rho (r :: s)) ∈ B ↔
              ((w.zero ρ.1, RoundsQueryLayout.zero s A W ρ.2) : Rho (r :: s)) ∈ B
            rw [zero_lo w hk]
        | false =>
          have hk := (act_shared e).1
          refine OComp.pr_dryVal_bind_le _ _ _ _ fun T0 => ?_
          refine (fs_dry_le m w.chal t hfb
            (fun β => (⟨i, h, T0.map TreeK.root, embP (.inl (.inl β))⟩ : FbIn lam L t))
            (a.plain m₁.2).1 _ (EvOk (r :: s) B) w.gr0 (cap i)
            (fun c => pr (unif (Rho s))
              {ρ | RoundsQueryLayout.zero s A W ρ ∈ {ρ' | ((c, ρ') : Rho (r :: s)) ∈ B}})
            hW.1.gr0_ok hW.1.chal_unif ?_ fun β ans => ?_).trans ?_
          · exact pr_dv_pure m _ _ (not_evOk_ranOut _ _ _)
          · exact tail_dry_le m B _ _ _ _ (chain_dry s A W _ _ (i + 1) _ _ hW.2 _)
          · rw [slice_eq B (zeroOf w.gr0) (RoundsQueryLayout.zero s A W)]
            refine le_of_eq (congrArg (pr _) (Set.ext fun ρ => ?_))
            show ((zeroOf w.gr0 ρ.1, RoundsQueryLayout.zero s A W ρ.2) : Rho (r :: s)) ∈ B ↔
              ((w.zero ρ.1, RoundsQueryLayout.zero s A W ρ.2) : Rho (r :: s)) ∈ B
            rw [zero_sh w hk]
      | join ρ₀ =>
        have hk := (act_join e).1
        refine OComp.pr_dryVal_bind_le _ _ _ _ fun TJ => ?_
        refine OComp.pr_dryVal_bind_le _ _ _ _ fun T0 => ?_
        refine OComp.pr_dryVal_bind_le _ _ _ _ fun c => ?_
        refine OComp.pr_dryVal_bind_le _ _ _ _ fun d => ?_
        refine OComp.pr_dryVal_bind_le _ _ _ _ fun rq => ?_
        refine (fs_dry_le m w.chal t hfb
          (fun β => (⟨i, .f4 cms (List.ofFn rq), T0.map TreeK.root, embP (.inl (.inl β))⟩ :
            FbIn lam L t)) (a.plain m₁.2).1 _ (EvOk (r :: s) B) w.gr0 (cap i)
          (fun c => pr (unif (Rho s))
            {ρ | RoundsQueryLayout.zero s A W ρ ∈ {ρ' | ((c, ρ') : Rho (r :: s)) ∈ B}})
          hW.1.gr0_ok hW.1.chal_unif ?_ fun β ans => ?_).trans ?_
        · exact pr_dv_pure m _ _ (not_evOk_ranOut _ _ _)
        · exact tail_dry_le m B _ _ _ _ (chain_dry s A W _ _ (i + 1) _ _ hW.2 _)
        · rw [slice_eq B (zeroOf w.gr0) (RoundsQueryLayout.zero s A W)]
          refine le_of_eq (congrArg (pr _) (Set.ext fun ρ => ?_))
          show ((zeroOf w.gr0 ρ.1, RoundsQueryLayout.zero s A W ρ.2) : Rho (r :: s)) ∈ B ↔
            ((w.zero ρ.1, RoundsQueryLayout.zero s A W ρ.2) : Rho (r :: s)) ∈ B
          rw [zero_sh w hk]

end Chain

/-- **THE STATEMENT.** -/
theorem chainLawDry : Spec.chainLawDry := by
  intro I X lam K L m t hfb cms x co cap s A W embS embP i ph σ hW B
  exact (le_of_eq (OComp.pr_record (S := typedOracleFamily lam K L) (fun o _ => m o)
    (chainO t cms x co cap s A W embS embP i ph σ) (EvOk s B))).trans
    (chain_dry m t hfb cms x co cap s A W embS embP i ph σ hW B)

/-- **The same for the first pass's program**, whose output is the verifier messages alone. -/
theorem chainLawDry_rhoO (t : Tag) (hfb : m (.fb t) = true) (cms : List (Dig lam)) (x : Option X)
    (co : Coins lam L) (cap : ℕ → ℕ) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : Phase lam) (σ : Strat s Unit) (hW : RoundsQueryLayout.OKG s A W) (B : Set (Rho s)) :
    pr ((rhoO t cms x co cap s A W embS embP i ph σ).record (S := typedOracleFamily lam K L) fun o _ => m o)
        {z | ∃ ρ, z.1 = .ok ρ ∧ ρ ∈ B} ≤
      pr (unif (Rho s)) {ρ | RoundsQueryLayout.zero s A W ρ ∈ B} := by
  unfold rhoO
  rw [OComp.record_bind_pure, pr_map]
  refine (pr_mono _ fun z hz => ?_).trans
    (chainLawDry m t hfb cms x co cap s A W embS embP i ph σ hW B)
  obtain ⟨ρ, e, hρ⟩ := hz
  obtain ⟨u, R⟩ := z
  cases u with
  | ok w =>
    have e' : w.1 = ρ := Res.ok.inj e
    exact ⟨w, rfl, by rw [e']; exact hρ⟩
  | noFormat => cases e
  | ranOut j => cases e

end OnBytes.Dry

#print axioms OnBytes.Dry.chainLawDry
#print axioms OnBytes.Dry.chainLawDry_rhoO
