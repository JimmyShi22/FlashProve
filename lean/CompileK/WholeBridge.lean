-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/WholeBridge.lean: from the true, uncensored view of the whole object to the view with the
notice.

Statement and proof. Generic: any interface, any simulator.
Hiop/WholeTrue.lean defines honest-verifier zero knowledge of the whole object for the view of the
honest runs as they are (HVZKWholeTrue); the compiler takes the view in which a run whose verifier
randomness is withheld is replaced by a notice (`HVZKWhole`, Hiop/Whole.lean). Neither view is a
function of the other that an environment could compute (whether ρ is withheld depends on the
prover's secret input).

Main names:
  `hvzk_of_true : Spec.hvzk_of_true`: Held L Ryes pT pL pO (the probabilities of the three withheld
    sets) and HVZKWholeTrue L Ryes B S u ⇒ HVZKWhole L Ryes B S (B.err pT pL pO + u). Same bounds,
    same simulator S : Hiop.Simulator L, whatever it is.
  `tv_view_laws`, `tv_run_laws`: each under the hypotheses of its statement, two hosts whose runs
    are near each other, run by run, have near views: one term for each run that the bounds allow
    (a hybrid along the environment's tree; no budget, no hiding property).
  `tv_sess_sessTrue`, `tv_bsess_bsessTrue`: each under the hypotheses of its statement, a run with
    the notice and the true run differ only where ρ is withheld (the first:
    `tv (sess H w y) (sessTrue H w y) ≤ prRho (H.withheld w y)`).

Limits: what it costs is B.err pT pL pO = pT + nenc · pL + (Σ_j sess j) · shown · pO: the
probability of the withheld set, once more for every run that the bounds allow. Where u already
holds these probabilities they are paid twice. This file says nothing on a
converse, and nothing on how small u can be.

Terms: lean/GLOSSARY.md.
-/
import Hiop.WholeTrueProof

set_option autoImplicit false

noncomputable section

namespace Hiop.Bridge
open Prob Iop Compile.Lifetime Compile.BatchLife
open scoped ENNReal

variable {I X : Type} {L : BatchProtocol I X} {α : Type}

/-! ## Part 1. Two hosts whose runs are near each other -/

section Near
variable {B : Bounds} {ok : X → Prop} {zT zL zO : ℝ≥0∞}

theorem tv_run_laws (W V : Laws L) (hy : ∀ r p, W.y r p = V.y r p)
    (hL : ∀ r r', tv (W.Lk r r') (V.Lk r r') ≤ zL)
    (hB : ∀ r J xs rest, (∀ j, ok (xs j)) → (∀ j x, rest j = some x → ok x) →
      tv (W.B r J xs rest) (V.B r J xs rest) ≤ J.card * zO) :
    ∀ (t : Env L α) (c : ℕ) (us ur : ℕ → ℕ) (s : ℕ × (ℕ → L.EncodingRandomness)), t.Adm B ok c us ur → c ≤ B.nenc →
      tv (t.run W.host s) (t.run V.host s) ≤
        ((B.nenc - c : ℕ) : ℝ≥0∞) * zL + (left B us : ℕ) * (B.shown * zO) := by
  intro t
  induction t with
  | stop a => intro c us ur s _ _; rw [run_stop, run_stop, tv_self]; exact zero_le _
  | fresh k ih =>
    rintro c us ur ⟨c', f⟩ h hc
    rw [run_fresh, run_fresh]
    refine tv_bind_right_le_of_forall _ _ _ fun r _ => ?_
    refine (tv_bind_le_of_forall _ _ _ _ fun a => ih a (c + 1) us ur _ (h.2 a) h.1).trans ?_
    have e : ((B.nenc - c : ℕ) : ℝ≥0∞) = ((B.nenc - (c + 1) : ℕ) : ℝ≥0∞) + 1 := by
      have := h.1
      rw [show B.nenc - c = B.nenc - (c + 1) + 1 by omega]
      push_cast
      rfl
    rw [e, add_mul, one_mul]
    calc
      tv (W.Lk (f 0) r) (V.Lk (f 0) r) +
            (((B.nenc - (c + 1) : ℕ) : ℝ≥0∞) * zL + (left B us : ℕ) * (B.shown * zO)) ≤
          zL + (((B.nenc - (c + 1) : ℕ) : ℝ≥0∞) * zL + (left B us : ℕ) * (B.shown * zO)) :=
        add_le_add_left (hL _ _) _
      _ = ((B.nenc - (c + 1) : ℕ) : ℝ≥0∞) * zL + zL + (left B us : ℕ) * (B.shown * zO) := by ring
  | session e J xs rest k ih =>
    intro c us ur s h hc
    rw [run_session, run_session]
    refine (tv_bind_le_of_forall _ _ _ _ fun a => ih a c _ ur s (h.2.2.2.2.2 a) hc).trans ?_
    rw [left_step (h.1.trans hc) h.2.1]
    have hJ : tv (W.B (s.2 e) J xs rest) (V.B (s.2 e) J xs rest) ≤ B.shown * zO :=
      (hB _ J xs rest h.2.2.2.1 h.2.2.2.2.1).trans (mul_le_mul_left (Nat.cast_le.2 h.2.2.1) _)
    rw [Nat.cast_succ, add_mul, one_mul]
    calc
      tv (W.B (s.2 e) J xs rest) (V.B (s.2 e) J xs rest) +
            (((B.nenc - c : ℕ) : ℝ≥0∞) * zL +
              (left B (Function.update us e (us e + 1)) : ℕ) * (B.shown * zO)) ≤
          B.shown * zO +
            (((B.nenc - c : ℕ) : ℝ≥0∞) * zL +
              (left B (Function.update us e (us e + 1)) : ℕ) * (B.shown * zO)) :=
        add_le_add_left hJ _
      _ = ((B.nenc - c : ℕ) : ℝ≥0∞) * zL +
            ((left B (Function.update us e (us e + 1)) : ℕ) * (B.shown * zO) + B.shown * zO) := by
        ring
  | read e p k ih =>
    intro c us ur s h hc
    rw [run_read, run_read, hy]
    exact ih _ c us _ s (h.2.2 _) hc
  | draw β d k ih =>
    intro c us ur s h hc
    rw [run_draw, run_draw]
    exact tv_bind_right_le_of_forall _ _ _ fun y _ => ih y c us ur s (h y) hc

/-- Under the hypotheses below, two hosts whose runs are near each other, run by run, have near
views: one term for each run that the bounds allow. -/
theorem tv_view_laws (W V : Laws L) (hy : ∀ r p, W.y r p = V.y r p)
    (hT : ∀ r, tv (W.T r) (V.T r) ≤ zT) (hL : ∀ r r', tv (W.Lk r r') (V.Lk r r') ≤ zL)
    (hB : ∀ r J xs rest, (∀ j, ok (xs j)) → (∀ j x, rest j = some x → ok x) →
      tv (W.B r J xs rest) (V.B r J xs rest) ≤ J.card * zO)
    (E : Sess L.offline → Env L α) (hE : ∀ a, (E a).Adm B ok 0 (fun _ => 0) fun _ => 0) :
    tv (W.host.view E) (V.host.view E) ≤ B.err zT zL zO := by
  rw [view_host, view_host]
  refine tv_bind_right_le_of_forall _ _ _ fun r _ => ?_
  refine (tv_bind_le_of_forall _ _ _ _ fun a =>
    tv_run_laws W V hy hL hB (E a) 0 _ _ _ (hE a) (Nat.zero_le _)).trans ?_
  have e : left B (fun _ => 0) = B.total := by
    unfold left Bounds.total
    simp
  rw [e, Nat.sub_zero]
  unfold Bounds.err
  rw [add_assoc]
  exact add_le_add_left (hT r) _

end Near

/-! ## Part 2. The view with the notice and the true view -/

section Runs
variable {Y : Type} {E : ExtSpec} {Wt : Type}

theorem tv_sess_sessTrue {Q : InteractiveOracleProof Y E} (H : Honest Q Wt) (w : Wt) (y : Y) :
    tv (sess H w y) (sessTrue H w y) ≤ prRho (H.withheld w y) := by
  refine (tv_bind_right_le_pr_ne _ _ _).trans (pr_mono _ ?_)
  intro ρ hρ
  by_contra hn
  refine hρ ?_
  unfold trueView Honest.output
  rw [if_neg hn]
  simp only [PMF.map_comp]
  rfl

theorem tv_bsess_bsessTrue {X : Type} {Q : BatchInteractiveOracleProof X E} {N : ℕ} (H : BatchHonestProver Q Wt) (w : Wt)
    (x : Fin N → Option X) (J : Finset (Fin N)) (xs : J → X) (hxs : ∀ j : J, x j = some (xs j)) :
    tv (bsess H w x J) (bsessTrue H w x J) ≤
      prBRho {ρ : BRho N Q.loc.shape Q.ann | ∃ j : J, ρ.slot j.1 ∈ H.one.withheld w (xs j)} := by
  refine (tv_bind_right_le_pr_ne _ _ _).trans (pr_mono _ ?_)
  intro ρ hρ
  by_contra hn
  have hn1 : ∀ j : J, ρ.slot j.1 ∉ H.one.withheld w (xs j) := fun j hh => hn ⟨j, hh⟩
  refine hρ ?_
  unfold btrueView BatchHonestProver.output
  simp only [PMF.map_comp]
  refine congrArg (fun f => (unif (H.Coin0 × (Fin N → H.Coin))).map f) (funext fun c => ?_)
  refine Prod.ext rfl (funext fun j => ?_)
  simp only [Function.comp_def, hxs j, if_neg (hn1 j), Option.map_some]

end Runs

namespace Spec

/-- From the true view to the view with the notice, for any simulator: the two real views differ
only where the verifier's randomness of some run is withheld. (not all hypotheses are named here:
see the statement below) -/
def hvzk_of_true : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (Ryes : I → X → Prop) (pT pL pO : ℝ≥0∞), Held L Ryes pT pL pO →
    ∀ (B : Bounds) (S : Simulator L) (u : ℝ≥0∞),
      HVZKWholeTrue L Ryes B S u → HVZKWhole L Ryes B S (B.err pT pL pO + u)

end Spec

theorem hvzk_of_true : Spec.hvzk_of_true := by
  intro I X L Ryes pT pL pO hH B S u h i α E hE
  refine (tv_triangle _ ((trueHost L i).view E) _).trans (add_le_add ?_ (h i α E hE))
  have hT : ∀ r, tv ((realLaws L i).T r) ((trueLaws L i).T r) ≤ pT := fun r =>
    (tv_sess_sessTrue L.honestOfflineProver (i, r) ()).trans (hH.prT _ _)
  have hL : ∀ r r', tv ((realLaws L i).Lk r r') ((trueLaws L i).Lk r r') ≤ pL := fun r r' =>
    (tv_sess_sessTrue L.honestLinkProver (i, r, r') ()).trans (hH.prL _ _)
  have hB : ∀ r J xs rest, (∀ j, Ryes i (xs j)) → (∀ j x, rest j = some x → Ryes i x) →
      tv ((realLaws L i).B r J xs rest) ((trueLaws L i).B r J xs rest) ≤ J.card * pO :=
    fun r J xs rest h1 _ =>
      (tv_bsess_bsessTrue L.honestOnlineBatchProver (i, r) (vec J xs rest) J xs fun j => dif_pos j.2).trans
        (prBRho_exists_withheld_le hH (i, r) J xs h1)
  exact tv_view_laws (realLaws L i) (trueLaws L i) (fun _ _ => rfl) hT hL hB E hE

end Hiop.Bridge
