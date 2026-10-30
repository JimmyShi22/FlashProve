-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/WholeTrueProof.lean: honest-verifier zero knowledge of the whole object for the true,
uncensored view. Proofs of the statements of Hiop/WholeTrue.lean.

At a ρ that is not withheld the output of a run is its true view, so a run with the true view and
the completed simulator's run differ only where ρ is withheld or the simulator is not exact
(`tv_sessTrue_le`, `tv_bsessTrue_le`). So the uncensored real side is near the completed simulators
(`near_true`, from `BatchProtocol.Wired` and `GoodTrue`), and the theorem of Hiop/WholeProof.lean for any
such real side applies (`tv_view_le`).

Terms: lean/GLOSSARY.md.
-/
import Hiop.WholeTrue
import Hiop.WholeProof
import Iop.BatchUnif

set_option autoImplicit false

noncomputable section

namespace Hiop
open Prob Iop Compile.Lifetime Compile.BatchLife
open scoped ENNReal

section Runs
variable {Y X : Type} {E : ExtSpec} {Wt : Type}

theorem tv_sessTrue_le {Q : InteractiveOracleProof Y E} (H : Honest Q Wt) (Sim : SimOf Q)
    (d : Y → Rho Q.shape → DView Q) (w : Wt) (y : Y) {u : ℝ≥0∞}
    (h : prRho {ρ | ρ ∈ H.withheld w y ∨ H.output w y ρ ≠ Sim y ρ (Q.extAns y ρ (H.ext w))} ≤ u) :
    tv (sessTrue H w y) (simSess Q (fillSim Sim d) y (H.ext w)) ≤ u := by
  refine (tv_bind_right_le_pr_ne _ _ _).trans (le_trans (pr_mono _ ?_) h)
  intro ρ hρ
  by_contra hn
  have hn1 : ρ ∉ H.withheld w y := fun hh => hn (Or.inl hh)
  have hn2 : H.output w y ρ = Sim y ρ (Q.extAns y ρ (H.ext w)) := by
    by_contra hh
    exact hn (Or.inr hh)
  refine hρ ?_
  unfold fillSim trueView
  rw [← hn2]
  unfold Honest.output
  rw [if_neg hn1]
  simp only [PMF.map_comp]
  rfl

theorem tv_bsessTrue_le {Q : BatchInteractiveOracleProof X E} {N : ℕ} (H : BatchHonestProver Q Wt) (Sim : BSimOf Q N)
    (d : X → Rho Q.loc.shape → DView Q.loc) (w : Wt) (x : Fin N → Option X) (J : Finset (Fin N))
    (xs : J → X) (hxs : ∀ j : J, x j = some (xs j)) {u : ℝ≥0∞}
    (h : prBRho {ρ | (∃ j : J, ρ.slot j.1 ∈ H.one.withheld w (xs j)) ∨
          H.output w x ρ J ≠
            Sim J xs (fun j => ρ.slot j.1) (Q.extAnsJ J xs (fun j => ρ.slot j.1) (H.ext w))} ≤ u) :
    tv (bsessTrue H w x J) (simBsess Q (fillBSim Sim d) J xs (H.ext w)) ≤ u := by
  refine (tv_bind_right_le_pr_ne _ _ _).trans (le_trans (pr_mono _ ?_) h)
  intro ρ hρ
  by_contra hn
  have hn1 : ∀ j : J, ρ.slot j.1 ∉ H.one.withheld w (xs j) := fun j hh => hn (Or.inl ⟨j, hh⟩)
  have hn2 : H.output w x ρ J =
      Sim J xs (fun j => ρ.slot j.1) (Q.extAnsJ J xs (fun j => ρ.slot j.1) (H.ext w)) := by
    by_contra hh
    exact hn (Or.inr hh)
  refine hρ ?_
  unfold fillBSim btrueView
  rw [← hn2]
  unfold BatchHonestProver.output
  simp only [PMF.map_comp]
  refine congrArg (fun f => (unif (H.Coin0 × (Fin N → H.Coin))).map f) (funext fun c => ?_)
  refine Prod.ext rfl (funext fun j => ?_)
  simp only [Function.comp_def, hxs j, if_neg (hn1 j), Option.map_some, Option.getD_some]

end Runs

variable {I X : Type} {L : BatchProtocol I X}

def trueLaws (L : BatchProtocol I X) (i : I) : Laws L where
  T := fun r => sessTrue L.honestOfflineProver (i, r) ()
  Lk := fun r r' => sessTrue L.honestLinkProver (i, r, r') ()
  B := fun r J xs rest => bsessTrue L.honestOnlineBatchProver (i, r) (vec J xs rest) J
  y := fun r p => L.encodeIndex i r p

theorem trueHost_eq (i : I) : trueHost L i = (trueLaws L i).host := rfl

theorem near_true {Ryes : I → X → Prop} {uT uL uO : ℝ≥0∞} (hW : L.Wired) {Sm : Sims L}
    (hS : GoodTrue Sm Ryes uT uL uO) (d : Fill L) (i : I) :
    (trueLaws L i).Near (fillSims Sm d) i (Ryes i) uT uL uO where
  y := fun _ _ => rfl
  T := fun r => by
    have h1 := tv_sessTrue_le L.honestOfflineProver Sm.T d.T (i, r) () (hS.goodT (i, r) ())
    rw [hW.extT] at h1
    exact h1
  Lk := fun r r' => by
    have h1 := tv_sessTrue_le L.honestLinkProver Sm.Lk d.Lk (i, r, r') () (hS.goodL (i, r, r') ())
    rw [hW.extL] at h1
    exact h1
  B := fun r J xs rest h1 h2 => by
    have h3 := tv_bsessTrue_le L.honestOnlineBatchProver Sm.B d.B (i, r) (vec J xs rest) J xs (vec_of_mem J xs rest)
      (hS.goodB (i, r) (vec J xs rest) (valid_vec J xs rest h1 h2) J xs (vec_of_mem J xs rest))
    rw [hW.extB] at h3
    exact h3

theorem hvzk_whole_true_of :
    Spec.hvzk_whole_true_of := fun _ _ _ _ _ _ _ _ _ _ _ _ hW hR _ hS d _ hB i₀ i _ E hE =>
  tv_view_le hR (near_true hW hS d i) hB i₀ E hE

/-- Some slot of J is withheld: at most |J| times the probability for one slot. (not all hypotheses
are named here: see the statement below) -/
theorem prBRho_exists_withheld_le {Ryes : I → X → Prop} {pT pL pO : ℝ≥0∞}
    (hH : Held L Ryes pT pL pO) (w : I × L.EncodingRandomness) (J : Finset (Fin L.maxBatchSize))
    (xs : J → X) (hv : ∀ j, Ryes w.1 (xs j)) :
    prBRho {ρ : BRho L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann | ∃ j : J,
          ρ.slot j.1 ∈ L.honestOnlineBatchProver.one.withheld w (xs j)} ≤
      J.card * pO := by
  have h := pr_exists_le_mul (unif (BRho L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann))
    (fun (j : J) ρ => ρ.slot j.1 ∈ L.honestOnlineBatchProver.one.withheld w (xs j)) pO fun j =>
      (le_of_eq (prBRho_slot j.1 (L.honestOnlineBatchProver.one.withheld w (xs j)))).trans (hH.prB w (xs j) (hv j))
  rwa [Fintype.card_coe] at h

theorem goodTrue_of_good : Spec.goodTrue_of_good := by
  intro I X L Ryes zT zL zO pT pL pO Sm hS hH
  refine ⟨fun w x => ?_, fun w x => ?_, fun w x hv J xs hxs => ?_⟩
  · rw [add_comm]
    exact (pr_union_le _ _ _).trans (add_le_add (hH.prT w x) (hS.goodT w x))
  · rw [add_comm]
    exact (pr_union_le _ _ _).trans (add_le_add (hH.prL w x) (hS.goodL w x))
  · rw [mul_add, add_comm]
    exact (pr_union_le _ _ _).trans
      (add_le_add (prBRho_exists_withheld_le hH w J xs fun j => hv j.1 _ (hxs j))
        (hS.goodB w x hv J xs hxs))

theorem goodTrue_of_exact : Spec.goodTrue_of_exact := by
  intro I X L Ryes pT pL pO Sm hS hH
  refine ⟨fun w x => ?_, fun w x => ?_, fun w x hv J xs hxs => ?_⟩
  · refine (pr_mono _ fun ρ hρ => ?_).trans (hH.prT w x)
    by_contra hn
    exact hρ.elim hn fun h => h (hS.exT w x ρ hn)
  · refine (pr_mono _ fun ρ hρ => ?_).trans (hH.prL w x)
    by_contra hn
    exact hρ.elim hn fun h => h (hS.exL w x ρ hn)
  · refine (pr_mono _ fun ρ hρ => ?_).trans
      (prBRho_exists_withheld_le hH w J xs fun j => hv j.1 _ (hxs j))
    by_contra hn
    exact hρ.elim hn fun h => h (hS.exB w x hv J xs hxs ρ fun j hj => hn ⟨j, hj⟩)

theorem hvzk_whole_true :
    Spec.hvzk_whole_true := fun I X L Ryes b qT qpar qch qon zT zL zO pT pL pO hW hR Sm hS hH d B hB i₀ =>
  hvzk_whole_true_of I X L Ryes b qT qpar qch qon _ _ _ hW hR Sm
    (goodTrue_of_good I X L Ryes zT zL zO pT pL pO Sm hS hH) d B hB i₀

end Hiop
