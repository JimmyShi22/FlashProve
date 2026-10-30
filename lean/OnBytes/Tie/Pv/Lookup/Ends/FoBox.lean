-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoBox.lean.
The entries of a lookup's public record: inside the bounds different places are different entries;
the bounds as numbers of a list of matrices; where the bits of the counts lie.

OnBytes/Tie/Pv/Lookup/Ends/FoLookPubA.lean and OnBytes/Tie/Pv/Lookup/Ends/FoLookPubH.lean have the
entries as cells in boxes and slots below a bound, and lay an index beyond a bound at the bound.
This file says what that costs and what it does not.

Main names:
  `upTo_inj`: up to the bound the laying is one to one.
  `cellJ_inj`, `maskJ_inj`, `cellJ_ne_maskJ`: so are the cells and the slots of JA; a cell is no
    slot.
  `cellH_inj`, `wH_inj`, `maskH_inj`, `cellH_ne_wH`, `cellH_ne_maskH`, `wH_ne_maskH`: the like for
    JH.
  `boxR mats`, `boxC mats`: the largest number of rows, of columns, over a list of matrices;
    `le_boxR`, `le_boxC`.
  `cellRC_lt`: for 5 ≤ lm ≤ h.kT + 5, a row t below 2^kT, a call c below NC and a bit j below 32:
    the cell FoNums.cellRC h lm (t, c, j) has its row below 2^lm and its column below
    NC * 2^(kT + 5 - lm), the number that Forest.planeCols returns.
One to one is said inside the bounds alone: beyond a bound all indices are laid at the bound. One
box serves all matrices, so it holds entries that nothing names. No clause of Fo.Pub2.LookPubOK
reads them; whether a statement that sums or counts over all entries minds them is not looked into
here.
No caller occurs here.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubH

set_option autoImplicit false

namespace Fo.Pub2
open Cb Cb.Fo OnBytes OnBytes.Model

/-! ### one to one -/

theorem upTo_inj {n i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) (e : upTo n i = upTo n j) : i = j := by
  have e' : min i n = min j n := congrArg Fin.val e
  rwa [Nat.min_eq_left hi, Nat.min_eq_left hj] at e'

section
variable {nM nR nC nS : ℕ}

theorem cellJ_inj {M r c M' r' c' : ℕ} (h1 : M ≤ nM) (h2 : r ≤ nR) (h3 : c ≤ nC) (k1 : M' ≤ nM)
    (k2 : r' ≤ nR) (k3 : c' ≤ nC)
    (e : (cellJ M r c : JA nM nR nC nS) = cellJ M' r' c') : M = M' ∧ r = r' ∧ c = c' := by
  have e1 := Sum.inl.inj e
  obtain ⟨a, b⟩ := Prod.mk.inj e1
  obtain ⟨b, d⟩ := Prod.mk.inj b
  exact ⟨upTo_inj h1 k1 a, upTo_inj h2 k2 b, upTo_inj h3 k3 d⟩

theorem maskJ_inj {j j' : ℕ} (h : j ≤ nS) (k : j' ≤ nS)
    (e : (maskJ j : JA nM nR nC nS) = maskJ j') : j = j' :=
  upTo_inj h k (Sum.inr.inj e)

theorem cellJ_ne_maskJ (M r c j : ℕ) : (cellJ M r c : JA nM nR nC nS) ≠ maskJ j :=
  Sum.inl_ne_inr

end

section
variable {nM nR nC wR wC nS : ℕ}

theorem cellH_inj {M r c M' r' c' : ℕ} (h1 : M ≤ nM) (h2 : r ≤ nR) (h3 : c ≤ nC) (k1 : M' ≤ nM)
    (k2 : r' ≤ nR) (k3 : c' ≤ nC)
    (e : (cellH M r c : JH nM nR nC wR wC nS) = cellH M' r' c') : M = M' ∧ r = r' ∧ c = c' := by
  have e1 := Sum.inl.inj e
  obtain ⟨a, b⟩ := Prod.mk.inj e1
  obtain ⟨b, d⟩ := Prod.mk.inj b
  exact ⟨upTo_inj h1 k1 a, upTo_inj h2 k2 b, upTo_inj h3 k3 d⟩

theorem wH_inj {r c r' c' : ℕ} (h2 : r ≤ wR) (h3 : c ≤ wC) (k2 : r' ≤ wR) (k3 : c' ≤ wC)
    (e : (wH r c : JH nM nR nC wR wC nS) = wH r' c') : r = r' ∧ c = c' := by
  obtain ⟨a, b⟩ := Prod.mk.inj (Sum.inl.inj (Sum.inr.inj e))
  exact ⟨upTo_inj h2 k2 a, upTo_inj h3 k3 b⟩

theorem maskH_inj {j j' : ℕ} (h : j ≤ nS) (k : j' ≤ nS)
    (e : (maskH j : JH nM nR nC wR wC nS) = maskH j') : j = j' :=
  upTo_inj h k (Sum.inr.inj (Sum.inr.inj e))

theorem cellH_ne_wH (M r c r' c' : ℕ) : (cellH M r c : JH nM nR nC wR wC nS) ≠ wH r' c' :=
  Sum.inl_ne_inr

theorem cellH_ne_maskH (M r c j : ℕ) : (cellH M r c : JH nM nR nC wR wC nS) ≠ maskH j :=
  Sum.inl_ne_inr

theorem wH_ne_maskH (r c j : ℕ) : (wH r c : JH nM nR nC wR wC nS) ≠ maskH j :=
  fun e => Sum.inl_ne_inr (Sum.inr.inj e)

end

/-! ### the bounds -/

/-- The largest number of rows over a list of matrices. -/
def boxR (mats : Array TMat) : ℕ := mats.foldl (fun a M => max a M.m) 0

/-- The largest number of columns over a list of matrices. -/
def boxC (mats : Array TMat) : ℕ := mats.foldl (fun a M => max a M.k) 0

theorem le_foldl_maxF (f : TMat → ℕ) : ∀ (l : List TMat) (a : ℕ),
    a ≤ l.foldl (fun a M => max a (f M)) a ∧ ∀ M ∈ l, f M ≤ l.foldl (fun a M => max a (f M)) a
  | [], a => ⟨le_refl a, fun _ h => absurd h List.not_mem_nil⟩
  | N :: l, a => by
    obtain ⟨h1, h2⟩ := le_foldl_maxF f l (max a (f N))
    refine ⟨le_trans (le_max_left _ _) h1, fun M hM => ?_⟩
    rcases List.mem_cons.1 hM with rfl | hM
    · exact le_trans (le_max_right _ _) h1
    · exact h2 M hM

theorem le_boxR {mats : Array TMat} {M : TMat} (h : M ∈ mats.toList) : M.m ≤ boxR mats := by
  unfold boxR
  rw [← Array.foldl_toList]
  exact (le_foldl_maxF (·.m) mats.toList 0).2 M h

theorem le_boxC {mats : Array TMat} {M : TMat} (h : M ∈ mats.toList) : M.k ≤ boxC mats := by
  unfold boxC
  rw [← Array.foldl_toList]
  exact (le_foldl_maxF (·.k) mats.toList 0).2 M h

/-! ### where the bits of the counts lie -/

theorem cellRC_lt (h : FoNums.Sh) {lm t c j : ℕ} (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5)
    (ht : t < 2 ^ h.kT) (hc : c < h.NC) (hj : j < 32) :
    (FoNums.cellRC h lm (t, c, j)).1 < 2 ^ lm ∧
      (FoNums.cellRC h lm (t, c, j)).2 < h.NC * 2 ^ (h.kT + 5 - lm) := by
  obtain ⟨a, rfl⟩ : ∃ a, lm = 5 + a := ⟨lm - 5, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, h.kT = a + b := ⟨h.kT - a, by omega⟩
  have e1 : 5 + a - FoNums.w = a := by show 5 + a - 5 = a; omega
  have e2 : h.kT + FoNums.w - (5 + a) = b := by show h.kT + 5 - (5 + a) = b; omega
  have e3 : h.kT + 5 - (5 + a) = b := by omega
  show t % 2 ^ (5 + a - FoNums.w) * FoNums.planes + j < 2 ^ (5 + a) ∧
    c * 2 ^ (h.kT + FoNums.w - (5 + a)) + t / 2 ^ (5 + a - FoNums.w) <
      h.NC * 2 ^ (h.kT + 5 - (5 + a))
  rw [e1, e2, e3]
  constructor
  · have hm : t % 2 ^ a < 2 ^ a := Nat.mod_lt _ (Nat.two_pow_pos a)
    have hp : (2 : ℕ) ^ (5 + a) = 2 ^ a * 32 := by rw [Nat.pow_add, Nat.mul_comm]
    rw [hp]
    show t % 2 ^ a * 32 + j < 2 ^ a * 32
    have : (t % 2 ^ a + 1) * 32 ≤ 2 ^ a * 32 := Nat.mul_le_mul_right _ hm
    omega
  · have hd : t / 2 ^ a < 2 ^ b := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos a), ← Nat.pow_add, Nat.add_comm, ← hb]
      exact ht
    have : (c + 1) * 2 ^ b ≤ h.NC * 2 ^ b := Nat.mul_le_mul_right _ hc
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

end Fo.Pub2
