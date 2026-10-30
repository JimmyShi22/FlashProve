-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRng2Proofs.lean: the statements of Cb/Ld/LdRng2.lean, proved: as in Cb/Ld/LdRngProofs.lean,
with `rng2_cnt_out` and `rng2_honest` (Cb/Ld/LdRng2AlgProofs.lean) in the place of `rngPk_cnt_out`
and `rngPk_honest` (Cb/Ld/LdRngAlgProofs.lean); `ldRng2_one` is proved outright.

The main one is `ldRng2_draw` (round 1 over a signature): see its statement in Cb/Ld/LdRng2.lean.
-/
import Cb.Ld.LdRng2
import Cb.Ld.LdRng2AlgProofs
import Cb.Ld.LdRngProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk IOR
open scoped ENNReal

theorem ldRng2_one : Spec.ldRng2_one := by
  intro p h
  refine ⟨h.B1, h.BD, by positivity, ?_⟩
  have hn : 1 ≤ p.nd := by
    by_contra hc
    have h0 : p.nd = 0 := by omega
    have h2 := h.D2
    rw [h0] at h2
    simp at h2
    omega
  have e : p.wd + p.wd * (p.nd - 1) = p.wd * p.nd := by
    obtain ⟨k, hk⟩ : ∃ k, p.nd = k + 1 := ⟨p.nd - 1, by omega⟩
    rw [hk]
    simp
    ring
  show ((2 ^ p.wd : ℕ) : ℤ) * ((2 ^ (p.wd * (p.nd - 1)) : ℕ) : ℤ) = 2 * p.D
  rw [h.D2, ← Nat.cast_mul, ← pow_add, e]

theorem ldRng2_at : Spec.ldRng2_at := by
  classical
  intro E St M Kc Wp _ E₀ p r A₀ h
  refine ⟨⟨((Blocks.plainPoint Unit p.one.Chal (), ()) : (drawRound p.one.Chal).IsPoint × Unit)⟩,
    ⟨fun x y y' τ τ' hρ _ _ _ => ?_,
      fun y y' τ τ' q _ _ hE _ => hE q (Finset.mem_singleton_self q)⟩,
    fun x y w c ρ hR hρ => ⟨rfl, ?_, hR.2⟩,
    ?_, fun w x c ρ => rfl,
    prRho_empty _ fun _ h => h,
    fun _ _ => le_refl _,
    fun k => ldRng_pWin p.one _ (ldRng2_one p h),
    fun w x c ρ => rfl, ?_⟩
  · have e : drawn τ = drawn τ' :=
      congrArg (fun r : Rho [drawRound p.one.Chal] => (show p.one.Chal × Unit from r).1) hρ
    show some (x, drawn τ) = some (x, drawn τ')
    rw [e]
  · exact rng2_honest E p.Rp p.Rd p.C p.U p.P p.nd p.B p.D p.rdx p.wd (r.W x)
      (r.yz (A₀.core w)) (show p.one.Chal × Unit from ρ).1 (r.pk w.1) (r.rd w.1)
      h.D2 hR.1 (fun hE => hρ (Or.inr ⟨hR.1.1.1, hE⟩))
  · intro a τ b ha hb
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    have e : b = ((a.1, drawn τ), a.2) := Prod.ext (Option.some.inj h1).symm h2
    rw [e]
    exact ha
  · intro m a ha μ
    have hcnt : cnt (fun Θ : p.one.Chal =>
          ¬ Rng (2 * p.D) p.rdx (r.W a.1) (r.pk m) (r.rd m) ∧
            ∃ d : p.Dg E, Out2 p.D p.rdx p.wd (r.W a.1) Θ (r.pk m) (r.rd m) d) ≤ p.one.err := by
      by_cases hs : Rng (2 * p.D) p.rdx (r.W a.1) (r.pk m) (r.rd m)
      · rw [cnt_false fun Θ hΘ => hΘ.1 hs]
        exact Nat.zero_le _
      · refine (Nat.le_div_iff_mul_le (by positivity)).2 ?_
        exact le_trans (Nat.mul_le_mul_right _ (cnt_mono fun Θ hΘ => hΘ.2))
          (rng2_cnt_out E p.Rp p.Rd p.C p.U p.P p.nd p.D p.rdx p.wd (r.W a.1)
            (r.pk m) (r.rd m) h.D2 hs)
    refine le_trans (cnt_mono fun β hβ => ?_) hcnt
    by_contra hn
    refine hβ fun b w hb hw => ?_
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    have e : b = ((a.1, β), a.2) := Prod.ext (Option.some.inj h1).symm h2
    rw [e] at hw
    exact ⟨by_contra fun hR => hn ⟨hR, w.2, hw.1⟩, hw.2⟩

theorem ldRng2_exact : Spec.ldRng2_exact := by
  classical
  intro E St M Kc Wp _ E₀ p r A₀ Ri
  refine ⟨fun _ ρ T _ =>
      PMF.pure (some
          ((rngDraw p.one St E₀).view
            T ((((), ()), (show p.one.Chal × Unit from ρ).1, ()) : Tr [drawRound p.one.Chal]))),
    fun x y w _ ρ hρ T _ => ?_⟩
  rw [(rngDrawH2 p r A₀).output_of_not_mem T (fun h => h.elim (fun e => e) hρ)]
  exact PMF.map_const (unif Unit)
    (some ((rngDraw p.one St E₀).view
        T ((((), ()), (show p.one.Chal × Unit from ρ).1, ()) : Tr [drawRound p.one.Chal])))

theorem ldRng2_draw : Spec.ldRng2_draw := fun E St Kc Wp _ E₀ p S r A₀ h =>
  sigLift_goodT E S Kc St (St × p.one.Chal) Wp (Wp × p.Dg E) E₀ E₀ (rngDraw p.one St E₀)
    (rngDrawH2 p r A₀) (rngIn p.one r A₀) (rngOut2 p r A₀) (fun _ _ _ w => w.1) (rngDrawN p.one r)
    (ldRng2_at E St S.Msg Kc Wp E₀ p r A₀ h)
    (ldRng2_exact E St S.Msg Kc Wp E₀ p r A₀ (rngIn p.one r A₀).rel)

theorem ldRng2_goodT : Spec.ldRng2_goodT := by
  intro E St Kc Wp _ E₀ p S N r A₀ get Sd Dn L t h hC hF hL hE hD hB hZ
  have g₁ := goodT_cf _ _ _ _ _ _ _ _ _ _ _ _ _ (ldRng2_draw E St Kc Wp E₀ p S r A₀ h)
  have g₂ := ldSendSig_chain E S N Sd Kc (St × p.one.Chal) (Wp × p.Dg E) Wp E₀ (rngOut2 p r A₀)
    (rngBk2 p N get) Dn L t hC hF hL hE hD hB hZ
  exact goodT_seq_ext Kc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g₁ g₂ (fun a τ₁ τ₂ b w hb => rfl)

theorem ldRng2_rows : Spec.ldRng2_rows := by
  intro E St J _ _ _ p W l st Θ v
  have hp : ∀ {I : Type} [Fintype I] (at' : I → J) (a : I → E),
      ∑ n, placed at' a n * v n = ∑ x, a x * v (at' x) :=
    fun {I} _ at' a => ldRng_placed I J E at' a v
  have hL : ∀ i u, ∑ n, rngRow2 p W l (.inl i, u) (st, Θ) n * v n =
      ∑ c, (((Θ u c).val : ℤ) : E) * v (l.pk i c) -
        ∑ x : Fin p.P × Fin p.nd, (p.rdx : E) ^ (x.1 : ℕ) *
          ((2 ^ (p.wd * (x.2 : ℕ)) : ℕ) : E) * v (l.dg (i, x.1) u x.2) := by
    intro i u
    show ∑ n, (placed (l.pk i) (fun c => (((Θ u c).val : ℤ) : E)) n -
          placed (fun x : Fin p.P × Fin p.nd => l.dg (i, x.1) u x.2)
            (fun x => (p.rdx : E) ^ (x.1 : ℕ) * ((2 ^ (p.wd * (x.2 : ℕ)) : ℕ) : E)) n) * v n = _
    simp only [sub_mul, Finset.sum_sub_distrib, hp]
  have hR : ∀ k u, ∑ n, rngRow2 p W l (.inr k, u) (st, Θ) n * v n =
      ∑ c, (((Θ u c).val : ℤ) : E) * v (l.rd k c) -
        ∑ x : p.one.Row × Fin p.nd,
          W st k x.1 * ((2 ^ (p.wd * (x.2 : ℕ)) : ℕ) : E) * v (l.dg x.1 u x.2) := by
    intro k u
    show ∑ n, (placed (l.rd k) (fun c => (((Θ u c).val : ℤ) : E)) n -
          placed (fun x : p.one.Row × Fin p.nd => l.dg x.1 u x.2)
            (fun x => W st k x.1 * ((2 ^ (p.wd * (x.2 : ℕ)) : ℕ) : E)) n) * v n = _
    simp only [sub_mul, Finset.sum_sub_distrib, hp]
  have hP : ∀ i u, pack p.rdx (fun r => psi2 p.D p.wd (l.dgOf p v) r u) i =
      ∑ x : Fin p.P × Fin p.nd,
          (p.rdx : E) ^ (x.1 : ℕ) * ((2 ^ (p.wd * (x.2 : ℕ)) : ℕ) : E) * v (l.dg (i, x.1) u x.2) -
        (p.D : E) * ∑ k : Fin p.P, (p.rdx : E) ^ (k : ℕ) := by
    intro i u
    unfold pack psi2 RngAt2.dgOf
    rw [Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · ring
  have hQ : ∀ k u, ∑ r, W st k r * psi2 p.D p.wd (l.dgOf p v) r u =
      ∑ x : p.one.Row × Fin p.nd,
          W st k x.1 * ((2 ^ (p.wd * (x.2 : ℕ)) : ℕ) : E) * v (l.dg x.1 u x.2) -
        (p.D : E) * ∑ r, W st k r := by
    intro k u
    have e : ∑ x : p.one.Row × Fin p.nd,
          W st k x.1 * ((2 ^ (p.wd * (x.2 : ℕ)) : ℕ) : E) * v (l.dg x.1 u x.2) =
        ∑ r : p.one.Row,
          ∑ j : Fin p.nd, W st k r * ((2 ^ (p.wd * (j : ℕ)) : ℕ) : E) * v (l.dg r u j) :=
      Fintype.sum_prod_type _
    unfold psi2 RngAt2.dgOf
    rw [e, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · ring
  constructor
  · rintro ⟨h1, h2⟩ ⟨i | k, u⟩
    · show ∑ n, rngRow2 p W l (.inl i, u) (st, Θ) n * v n =
        - (p.D : E) * ∑ k : Fin p.P, (p.rdx : E) ^ (k : ℕ)
      have h := h1 i u
      rw [hP] at h
      rw [hL]
      unfold RngAt2.pkOf at h
      linear_combination h
    · show ∑ n, rngRow2 p W l (.inr k, u) (st, Θ) n * v n = - (p.D : E) * ∑ r, W st k r
      have h := h2 k u
      rw [hQ] at h
      rw [hR]
      unfold RngAt2.rdOf at h
      linear_combination h
  · intro h
    refine ⟨fun i u => ?_, fun k u => ?_⟩
    · have h1 : ∑ n, rngRow2 p W l (.inl i, u) (st, Θ) n * v n =
          - (p.D : E) * ∑ k : Fin p.P, (p.rdx : E) ^ (k : ℕ) := h (.inl i, u)
      rw [hL] at h1
      rw [hP]
      unfold RngAt2.pkOf
      linear_combination h1
    · have h1 : ∑ n, rngRow2 p W l (.inr k, u) (st, Θ) n * v n = - (p.D : E) * ∑ r, W st k r :=
        h (.inr k, u)
      rw [hR] at h1
      rw [hQ]
      unfold RngAt2.rdOf
      linear_combination h1

theorem ldRng2_end : Spec.ldRng2_end := by
  intro E St Kc Wp _ E₀ p S N l r get A₀ hl a w
  obtain ⟨e1, e2, e3⟩ := hl ((S.sum N).msgs w.1)
  have key := ldRng2_rows E St _ p r.W l a.1.1.1 a.1.1.2 ((S.sum N).ents ((S.sum N).msgs w.1))
  constructor
  · intro hw
    have hT : InTabs2 p.wd (get (S.right N (T := OMsg.Msg) ((S.sum N).msgs w.1))) := hw.2.1.1
    have hR : Rows2 p.D p.rdx p.wd (r.W a.1.1.1) a.1.1.2
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
