-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRng2AlgProofs.lean: the statements of Cb/Ld/LdRng2Alg.lean, proved.

The main one, `rng2_cnt_out`: for 2 D = 2^(wd · nd), if the predicate `Rng` fails at the bound 2 D,
digits with `Out2` exist for at most the fraction 2^(-|U|) of the challenges (`Rng`:
Cb/Ld/LdRngAlg.lean; nd digits of width wd; |U| combinations).
The two facts on digits (`rng2_lt`, `rng2_digits`) go by induction on their number; the rest as in
Cb/Ld/LdRngAlgProofs.lean, whose count of passing challenges (`rngPk_cnt_pass`) is used unchanged.
-/
import Cb.Ld.LdRng2Alg
import Cb.Ld.LdRngAlgProofs

set_option autoImplicit false

namespace Cb
open Prob Finset Cb.Rng Cb.RngPk

theorem rng2_lt : Spec.rng2_lt := by
  intro wd nd
  induction nd with
  | zero => intro a _; simp
  | succ n ih =>
      intro a ha
      rw [Fin.sum_univ_castSucc]
      have h1 := ih (fun i => a i.castSucc) fun i => ha _
      have h2 : a (Fin.last n) + 1 ≤ 2 ^ wd := ha _
      have h3 : 2 ^ (wd * n) * (a (Fin.last n) + 1) ≤ 2 ^ (wd * n) * 2 ^ wd :=
        Nat.mul_le_mul_left _ h2
      have e : 2 ^ (wd * (n + 1)) = 2 ^ (wd * n) * 2 ^ wd := by rw [Nat.mul_succ, pow_add]
      rw [e]
      simp only [Fin.val_castSucc, Fin.val_last]
      have h1' : ∑ i : Fin n, 2 ^ (wd * (i : ℕ)) * a i.castSucc < 2 ^ (wd * n) := h1
      nlinarith

theorem rng2_digits : Spec.rng2_digits := by
  intro wd nd n hn
  refine ⟨?_, fun i => Nat.mod_lt _ (by positivity)⟩
  -- the first k digits give n mod 2^(wd k)
  have key : ∀ k : ℕ, ∑ i : Fin k, 2 ^ (wd * (i : ℕ)) * dig2 wd i n = n % 2 ^ (wd * k) := by
    intro k
    induction k with
    | zero => simp [Nat.mod_one]
    | succ k ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [ih]
        unfold dig2
        have e : 2 ^ (wd * (k + 1)) = 2 ^ (wd * k) * 2 ^ wd := by rw [Nat.mul_succ, pow_add]
        rw [e, Nat.mod_mul]
  rw [key nd, Nat.mod_eq_of_lt hn]

theorem rng2_pass_of_out : Spec.rng2_pass_of_out := by
  intro E _ Rp Rd C U _ _ P nd D ϱ wd W Θ mpk mrd d hD hO u
  obtain ⟨ht, hp, hr⟩ := hO
  choose a ha using fun r i => ht r u i
  have hψ : ∀ r,
      psi2 D wd d r u = ((((∑ i : Fin nd, 2 ^ (wd * (i : ℕ)) * a r i : ℕ) : ℤ) - D : ℤ) : E) := by
    intro r
    unfold psi2
    push_cast
    congr 1
    exact sum_congr rfl fun i _ => by rw [(ha r i).2]
  refine ⟨fun r => ((∑ i : Fin nd, 2 ^ (wd * (i : ℕ)) * a r i : ℕ) : ℤ) - D,
    fun r => ⟨?_, ?_⟩, fun i => ?_, fun k => ?_⟩
  · have : (0 : ℤ) ≤ ((∑ i : Fin nd, 2 ^ (wd * (i : ℕ)) * a r i : ℕ) : ℤ) := Int.natCast_nonneg _
    linarith
  · have h1 : ((∑ i : Fin nd, 2 ^ (wd * (i : ℕ)) * a r i : ℕ) : ℤ) < ((2 ^ (wd * nd) : ℕ) : ℤ) := by
      exact_mod_cast rng2_lt wd nd (a r) fun i => (ha r i).1
    linarith
  · show ∑ c, (((Θ u c).val : ℤ) : E) * mpk i c =
      pack ϱ (fun r => ((((∑ i : Fin nd, 2 ^ (wd * (i : ℕ)) * a r i : ℕ) : ℤ) - D : ℤ) : E)) i
    rw [hp i u]
    congr 1
    funext r
    exact hψ r
  · show ∑ c, (((Θ u c).val : ℤ) : E) * mrd k c =
      ∑ r, W k r * ((((∑ i : Fin nd, 2 ^ (wd * (i : ℕ)) * a r i : ℕ) : ℤ) - D : ℤ) : E)
    rw [hr k u]
    exact sum_congr rfl fun r _ => by rw [hψ r]

theorem rng2_cnt_out : Spec.rng2_cnt_out := by
  intro E _ Rp Rd C U _ _ _ _ _ P nd D ϱ wd W mpk mrd hD hbad
  refine le_trans (Nat.mul_le_mul_right _ (cnt_mono fun Θ hΘ => ?_))
    (rngPk_cnt_pass E Rp Rd C U P D ϱ W mpk mrd hbad)
  obtain ⟨d, hd⟩ := hΘ
  exact rng2_pass_of_out E Rp Rd C U P nd D ϱ wd W Θ mpk mrd d hD hd

theorem rng2_honest : Spec.rng2_honest := by
  intro E _ Rp Rd C U _ _ P nd b D ϱ wd W Y Θ mpk mrd hD hY hE
  have hw : ∀ r u, -D ≤ comb (Y r) (Θ u) ∧ comb (Y r) (Θ u) < D := by
    intro r u
    by_contra hn
    exact hE ⟨(r, u), hn⟩
  have hn : ∀ r u, (comb (Y r) (Θ u) + D).toNat < 2 ^ (wd * nd) := by
    intro r u
    have h0 : 0 ≤ comb (Y r) (Θ u) + D := by linarith [(hw r u).1]
    have h1 : ((comb (Y r) (Θ u) + D).toNat : ℤ) < ((2 ^ (wd * nd) : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg h0, ← hD]
      linarith [(hw r u).2]
    exact_mod_cast h1
  have hψ : ∀ r u, psi2 D wd (hdig2 (E := E) (nd := nd) D wd Y Θ) r u =
      ∑ c, (((Θ u c).val : ℤ) : E) * ((Y r c : ℤ) : E) := by
    intro r u
    have h0 : 0 ≤ comb (Y r) (Θ u) + D := by linarith [(hw r u).1]
    have e1 : (∑ i : Fin nd,
          ((2 ^ (wd * (i : ℕ)) : ℕ) : E) * ((dig2 wd i (comb (Y r) (Θ u) + D).toNat : ℕ) : E)) =
        (((comb (Y r) (Θ u) + D).toNat : ℕ) : E) := by
      rw [← (rng2_digits wd nd _ (hn r u)).1]
      push_cast
      rw [(rng2_digits wd nd _ (hn r u)).1]
    have e2 : (((comb (Y r) (Θ u) + D).toNat : ℕ) : E) = ((comb (Y r) (Θ u) + D : ℤ) : E) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
    unfold psi2 hdig2
    rw [e1, e2]
    unfold comb
    push_cast
    ring_nf
  refine ⟨fun r u i => ⟨_, (rng2_digits wd nd _ (hn r u)).2 i, rfl⟩, fun i u => ?_, fun k u => ?_⟩
  · have e1 : (fun r => psi2 D wd (hdig2 (E := E) (nd := nd) D wd Y Θ) r u) =
        fun r => ∑ c, (((Θ u c).val : ℤ) : E) * ((Y r c : ℤ) : E) :=
      funext fun r => hψ r u
    rw [e1, pack_sum]
    refine sum_congr rfl fun c _ => ?_
    rw [pack_mul_left, hY.1.2 i c]
  · have e1 : ∀ r, W k r * psi2 D wd (hdig2 (E := E) (nd := nd) D wd Y Θ) r u =
        ∑ c, (((Θ u c).val : ℤ) : E) * (W k r * ((Y r c : ℤ) : E)) := by
      intro r
      rw [hψ r u, mul_sum]
      exact sum_congr rfl fun c _ => mul_left_comm _ _ _
    rw [sum_congr rfl fun r _ => e1 r, sum_comm]
    refine sum_congr rfl fun c _ => ?_
    rw [hY.2 k c, mul_sum]

end Cb
