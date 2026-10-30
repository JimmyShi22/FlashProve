-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRngProofs.lean: the statements of Cb/Ld/LdRng.lean, proved.

The main one is `ldRng_goodT` (all three rounds): see its statement in Cb/Ld/LdRng.lean.
The mathematics is Cb/Ld/LdRngAlgProofs.lean's, and for the window event Cb/Gen/RngAlgProofs.lean's;
round 1 is lifted over a signature by Cb/Ld/LdSigLiftProofs.lean; the sending is
Cb/Ld/LdSigSumProofs.lean's; the two are joined by the rule for chains (Ior/KnowCollGood.lean).
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRng
import Cb.Ld.LdRngAlgProofs
import Cb.Ld.LdSigLiftProofs
import Cb.Ld.LdSigSumProofs
import Iop.ViewKit

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk IOR
open scoped ENNReal

theorem ldRng_err : Spec.ldRng_err := by
  intro p
  have h4 : Fintype.card Coef = 4 := by decide
  have hc : Fintype.card p.Chal = (4 ^ Fintype.card p.C) ^ Fintype.card p.U := by
    rw [Fintype.card_fun, Fintype.card_fun, h4]
  unfold RngPar.err
  refine Nat.div_mul_cancel ?_
  rw [hc]
  exact pow_dvd_pow_of_dvd (dvd_pow (by norm_num) Fintype.card_ne_zero) _

theorem ldRng_work : Spec.ldRng_work := by
  intro p w
  rw [pow_add, ← mul_assoc, ldRng_err p]

namespace RngPk

/-- The probability of an event that speaks of the one verifier message of a shape of one round. -/
theorem prRho_draw (r : Round) (Q : r.Chal → Prop) :
    prRho (s := [r]) {ρ | Q (show r.Chal × Rho [] from ρ).1} = pr (unif r.Chal) {c | Q c} := by
  have h1 : pr (unif (r.Chal × Rho [])) (Prod.fst ⁻¹' {c | Q c}) = pr (unif r.Chal) {c | Q c} := by
    rw [← pr_map, map_fst_unif]
  exact h1

theorem pr_event (p : RngPar) (h : p.OK) (Y : p.Cells) (hY : ∀ r c, |Y r c| < p.B) :
    pr (unif p.Chal) {Θ | Event p.D Y Θ} ≤ p.pWin := by
  unfold RngPar.pWin
  have hD0 : 0 < p.D := by
    have h1 := h.B1
    have h2 := h.BD
    omega
  split_ifs with hB
  · have hB1 : p.B = 1 := le_antisymm hB h.B1
    refine le_of_eq (pr_eq_zero_of_forall_not_mem _ fun Θ _ => ?_)
    exact event_empty _ _ _ p.D Y hD0 (fun r c => hB1 ▸ hY r c) Θ
  · exact pr_event_le p.Row p.C p.U p.B p.D Y (by omega) hD0.le hY

end RngPk

theorem ldRng_pWin : Spec.ldRng_pWin := by
  intro p Y h
  have h1 := prRho_draw (IOR.drawRound p.Chal) fun Θ => (∀ r c, |Y r c| < p.B) ∧ Event p.D Y Θ
  refine le_trans (le_of_eq h1) ?_
  by_cases hY : ∀ r c, |Y r c| < p.B
  · exact le_trans (pr_mono _ fun Θ hΘ => hΘ.2) (pr_event p h Y hY)
  · exact le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ fun Θ _ hΘ => hY hΘ.1)) (zero_le _)

theorem ldRng_sub : Spec.ldRng_sub := fun E _ _ _ _ _ _ p r _ h hA x y w hw =>
  ⟨⟨_, rngPk_mono E p.Rp p.Rd p.C p.P (2 * p.D) p.B p.rdx (r.W x) _ _ _ h.BD hw.1⟩, hA x y w hw.2⟩

theorem ldRng_at : Spec.ldRng_at := by
  classical
  intro E St M Kc Wp _ E₀ p r A₀ h
  refine ⟨⟨((Blocks.plainPoint Unit p.Chal (), ()) : (drawRound p.Chal).IsPoint × Unit)⟩,
    ⟨fun x y y' τ τ' hρ _ _ _ => ?_,
      fun y y' τ τ' q _ _ hE _ => hE q (Finset.mem_singleton_self q)⟩,
    fun x y w c ρ hR hρ => ⟨rfl, ?_, hR.2⟩,
    ?_, fun w x c ρ => rfl,
    prRho_empty _ fun _ h => h,
    fun _ _ => le_refl _,
    fun k => ldRng_pWin p _ h,
    fun w x c ρ => rfl, ?_⟩
  · have e : drawn τ = drawn τ' :=
      congrArg (fun r : Rho [drawRound p.Chal] => (show p.Chal × Unit from r).1) hρ
    show some (x, drawn τ) = some (x, drawn τ')
    rw [e]
  · exact rngPk_honest E p.Rp p.Rd p.C p.U p.P p.B p.D p.rdx p.q p.H (r.W x)
      (r.yz (A₀.core w)) (show p.Chal × Unit from ρ).1 (r.pk w.1) (r.rd w.1)
      h.q0 h.qH hR.1 (fun hE => hρ (Or.inr ⟨hR.1.1.1, hE⟩))
  · intro a τ b ha hb
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    have e : b = ((a.1, drawn τ), a.2) := Prod.ext (Option.some.inj h1).symm h2
    rw [e]
    exact ha
  · intro m a ha μ
    have hcnt : cnt (fun Θ : p.Chal =>
          ¬ Rng (2 * p.D) p.rdx (r.W a.1) (r.pk m) (r.rd m) ∧
            ∃ d, Out p.D p.rdx p.q p.H (r.W a.1) Θ (r.pk m) (r.rd m) d) ≤ p.err := by
      by_cases hs : Rng (2 * p.D) p.rdx (r.W a.1) (r.pk m) (r.rd m)
      · rw [cnt_false fun Θ hΘ => hΘ.1 hs]
        exact Nat.zero_le _
      · refine (Nat.le_div_iff_mul_le (by positivity)).2 ?_
        exact le_trans (Nat.mul_le_mul_right _ (cnt_mono fun Θ hΘ => hΘ.2))
          (rngPk_cnt_out E p.Rp p.Rd p.C p.U p.P p.D p.rdx p.q p.H (r.W a.1)
            (r.pk m) (r.rd m) h.qH hs)
    refine le_trans (cnt_mono fun β hβ => ?_) hcnt
    by_contra hn
    refine hβ fun b w hb hw => ?_
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    have e : b = ((a.1, β), a.2) := Prod.ext (Option.some.inj h1).symm h2
    rw [e] at hw
    exact ⟨by_contra fun hR => hn ⟨hR, w.2, hw.1⟩, hw.2⟩

theorem ldRng_exact : Spec.ldRng_exact := by
  classical
  intro E St M Kc Wp _ E₀ p r A₀ Ri
  refine ⟨fun _ ρ T _ =>
      PMF.pure (some
          ((rngDraw p St E₀).view T
            ((((), ()), (show p.Chal × Unit from ρ).1, ()) : Tr [drawRound p.Chal]))),
    fun x y w _ ρ hρ T _ => ?_⟩
  rw [(rngDrawH p r A₀).output_of_not_mem T (fun h => h.elim (fun e => e) hρ)]
  exact PMF.map_const (unif Unit)
    (some ((rngDraw p St E₀).view
        T ((((), ()), (show p.Chal × Unit from ρ).1, ()) : Tr [drawRound p.Chal])))

theorem ldRng_draw : Spec.ldRng_draw := fun E St Kc Wp _ E₀ p S r A₀ h =>
  sigLift_goodT E S Kc St (St × p.Chal) Wp (Wp × p.Dg E) E₀ E₀ (rngDraw p St E₀) (rngDrawH p r A₀)
    (rngIn p r A₀) (rngOut p r A₀) (fun _ _ _ w => w.1) (rngDrawN p r)
    (ldRng_at E St S.Msg Kc Wp E₀ p r A₀ h)
    (ldRng_exact E St S.Msg Kc Wp E₀ p r A₀ (rngIn p r A₀).rel)

theorem ldRng_goodT : Spec.ldRng_goodT := by
  intro E St Kc Wp _ E₀ p S N r A₀ get Sd Dn L t h hC hF hL hE hD hB hZ
  have g₁ := goodT_cf _ _ _ _ _ _ _ _ _ _ _ _ _ (ldRng_draw E St Kc Wp E₀ p S r A₀ h)
  have g₂ := ldSendSig_chain E S N Sd Kc (St × p.Chal) (Wp × p.Dg E) Wp E₀ (rngOut p r A₀)
    (rngBk p N get) Dn L t hC hF hL hE hD hB hZ
  exact goodT_seq_ext Kc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g₁ g₂ (fun a τ₁ τ₂ b w hb => rfl)

theorem ldRng_rounds : Spec.ldRng_rounds := fun _ _ _ _ _ _ _ _ => rfl

theorem ldRng_placed : Spec.ldRng_placed := by
  intro I J E _ _ _ _ at' a v
  unfold placed
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [ite_mul]

theorem ldRng_rows : Spec.ldRng_rows := by
  intro E St J _ _ _ p W l st Θ v
  have hp : ∀ {I : Type} [Fintype I] (at' : I → J) (a : I → E),
      ∑ n, placed at' a n * v n = ∑ x, a x * v (at' x) :=
    fun {I} _ at' a => ldRng_placed I J E at' a v
  have hL : ∀ i u, ∑ n, rngRow p W l (.inl i, u) (st, Θ) n * v n =
      ∑ c, (((Θ u c).val : ℤ) : E) * v (l.pk i c) -
        ∑ k : Fin p.P, (p.rdx : E) ^ (k : ℕ) * v (l.lo (i, k) u) -
        (p.q : E) * ∑ k : Fin p.P, (p.rdx : E) ^ (k : ℕ) * v (l.hi (i, k) u) := by
    intro i u
    show ∑ n, (placed (l.pk i) (fun c => (((Θ u c).val : ℤ) : E)) n -
          placed (fun k : Fin p.P => l.lo (i, k) u) (fun k => (p.rdx : E) ^ (k : ℕ)) n -
          (p.q : E) *
            placed (fun k : Fin p.P => l.hi (i, k) u) (fun k => (p.rdx : E) ^ (k : ℕ)) n) * v n = _
    simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum, hp]
  have hR : ∀ k u, ∑ n, rngRow p W l (.inr k, u) (st, Θ) n * v n =
      ∑ c, (((Θ u c).val : ℤ) : E) * v (l.rd k c) - ∑ r, W st k r * v (l.lo r u) -
        (p.q : E) * ∑ r, W st k r * v (l.hi r u) := by
    intro k u
    show ∑ n, (placed (l.rd k) (fun c => (((Θ u c).val : ℤ) : E)) n -
          placed (fun r => l.lo r u) (W st k) n -
          (p.q : E) * placed (fun r => l.hi r u) (W st k) n) * v n = _
    simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum, hp]
  have hP : ∀ i u, pack p.rdx (fun r => psi p.D p.q (l.dgOf p v) r u) i =
      ∑ k : Fin p.P, (p.rdx : E) ^ (k : ℕ) * v (l.lo (i, k) u) +
        (p.q : E) * ∑ k : Fin p.P, (p.rdx : E) ^ (k : ℕ) * v (l.hi (i, k) u) -
        (p.D : E) * ∑ k : Fin p.P, (p.rdx : E) ^ (k : ℕ) := by
    intro i u
    unfold pack psi RngAt.dgOf
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hQ : ∀ k u, ∑ r, W st k r * psi p.D p.q (l.dgOf p v) r u =
      ∑ r, W st k r * v (l.lo r u) + (p.q : E) * ∑ r, W st k r * v (l.hi r u) -
        (p.D : E) * ∑ r, W st k r := by
    intro k u
    unfold psi RngAt.dgOf
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  constructor
  · rintro ⟨h1, h2⟩ ⟨i | k, u⟩
    · show ∑ n, rngRow p W l (.inl i, u) (st, Θ) n * v n =
        - (p.D : E) * ∑ k : Fin p.P, (p.rdx : E) ^ (k : ℕ)
      have h := h1 i u
      rw [hP] at h
      rw [hL]
      unfold RngAt.pkOf at h
      linear_combination h
    · show ∑ n, rngRow p W l (.inr k, u) (st, Θ) n * v n = - (p.D : E) * ∑ r, W st k r
      have h := h2 k u
      rw [hQ] at h
      rw [hR]
      unfold RngAt.rdOf at h
      linear_combination h
  · intro h
    refine ⟨fun i u => ?_, fun k u => ?_⟩
    · have h1 : ∑ n, rngRow p W l (.inl i, u) (st, Θ) n * v n =
          - (p.D : E) * ∑ k : Fin p.P, (p.rdx : E) ^ (k : ℕ) := h (.inl i, u)
      rw [hL] at h1
      rw [hP]
      unfold RngAt.pkOf
      linear_combination h1
    · have h1 : ∑ n, rngRow p W l (.inr k, u) (st, Θ) n * v n = - (p.D : E) * ∑ r, W st k r :=
        h (.inr k, u)
      rw [hR] at h1
      rw [hQ]
      unfold RngAt.rdOf
      linear_combination h1

theorem ldRng_rows_card : Spec.ldRng_rows_card :=
  fun p => by rw [Fintype.card_prod, Fintype.card_sum]

theorem ldRng_end : Spec.ldRng_end := by
  intro E St Kc Wp _ E₀ p S N l r get A₀ hl a w
  obtain ⟨e1, e2, e3⟩ := hl ((S.sum N).msgs w.1)
  have key := ldRng_rows E St _ p r.W l a.1.1.1 a.1.1.2 ((S.sum N).ents ((S.sum N).msgs w.1))
  constructor
  · intro hw
    have hT : InTabs p.q p.H (get (S.right N (T := OMsg.Msg) ((S.sum N).msgs w.1))) := hw.2.1.1
    have hR : Rows p.D p.rdx p.q (r.W a.1.1.1) a.1.1.2
        (r.pk (S.left N (T := OMsg.Msg) ((S.sum N).msgs w.1)))
        (r.rd (S.left N (T := OMsg.Msg) ((S.sum N).msgs w.1)))
        (get (S.right N (T := OMsg.Msg) ((S.sum N).msgs w.1))) := hw.2.1.2
    rw [e3] at hT
    rw [e1, e2, e3] at hR
    exact ⟨hw.1, hT, key.1 hR, hw.2.2⟩
  · rintro ⟨hd, hT, hR, hA⟩
    have hR' := key.2 hR
    rw [← e3] at hT
    rw [← e1, ← e2, ← e3] at hR'
    exact ⟨hd, ⟨hT, hR'⟩, hA⟩

end Cb
