-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/TensorsDense.lean: a structured vector cut below a length, for vectors that may
have a written-out factor.

Johnson/Desc/K14/Law/Tensors.lean shows the law of tensorBelow for vectors without a written-out
factor. Here it is shown for all: the whole, the two short cuts, the sum over the bits of the length
(no variable of the stretch is written out), and the one summand with a zeroed copy of the slice
(all variables of the stretch are written out).
Main names: entry_zeroG, entry_cutG, nodup_of_distinctNats, denseIndex_form, denseIndex_lt,
denseNumber_pick, sum_bits_nat, pick_eq, tensorBelow_valG, tensorBelow_memG.

What is not claimed. In the last arm the written-out variables must be named once each
(distinctNats): a premise. Every equation is between readings, not between the program's words.

-/
import Johnson.Desc.K14.Law.Tensors

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes
open OnBytes.Model (Reading)

variable {K : Type} [Field K] (ρ : Reading K)

/-- An entry with a factor 0 reads as 0. -/
theorem entry_zeroG (v : Tensor) (j i : Nat) (hi : i < v.pairs.length)
    (h : factor ρ v.pairs j i = 0) : ρ.val (v.entry j) = 0 := by
  rw [Tensor.entry_val, pairsVal_prod, Finset.prod_eq_zero (Finset.mem_range.2 hi) h, mul_zero,
    zero_mul]

open Classical in
/-- An entry of summand number q of the cut. -/
theorem entry_cutG (v : Tensor) (start count len q j : Nat) (hq : q < count)
    (hn : start + count ≤ v.pairs.length) :
    ρ.val (({ v with pairs := v.pairs.mapIdx (cutPair start count len q) } : Tensor).entry j) =
      (if Below (j / 2 ^ start) len count q then 1 else 0) * ρ.val (v.entry j) := by
  have hd : Tensor.denseVal ρ
      ({ v with pairs := v.pairs.mapIdx (cutPair start count len q) } : Tensor) j =
      Tensor.denseVal ρ v j := rfl
  rw [Tensor.entry_val, Tensor.entry_val, hd, pairsVal_prod, pairsVal_prod, List.length_mapIdx,
    Finset.prod_congr rfl fun i hi => factor_cut ρ v.pairs start count len q j i
      (Finset.mem_range.1 hi), Finset.prod_mul_distrib, Finset.prod_boole]
  by_cases hB : Below (j / 2 ^ start) len count q
  · rw [if_pos hB, if_pos ((keeps_all start count len q j _ hq hn).2 hB)]; ring
  · rw [if_neg hB, if_neg fun h => hB ((keeps_all start count len q j _ hq hn).1 h)]; ring

/-! ## The index within the slice -/

/-- Numbers of which none occurs twice. -/
theorem nodup_of_distinctNats : ∀ l : List Nat, distinctNats l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [distinctNats, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at h
    exact List.nodup_cons.2 ⟨h.1, nodup_of_distinctNats l h.2⟩

/-- The index within the slice is a multiple of 2 ^ i, below 2 ^ (i + the number of variables). -/
theorem denseIndex_form : ∀ (ds : List Nat) (i j : Nat),
    ∃ x, denseIndex ds i j = 2 ^ i * x ∧ x < 2 ^ ds.length
  | [], i, j => ⟨0, by simp [denseIndex], by simp⟩
  | d :: ds, i, j => by
    obtain ⟨x, hx, hlt⟩ := denseIndex_form ds (i + 1) j
    refine ⟨j / 2 ^ d % 2 + 2 * x, ?_, ?_⟩
    · rw [denseIndex, hx, Nat.pow_succ]; ring
    · have := Nat.mod_lt (j / 2 ^ d) (by decide : 0 < 2)
      rw [List.length_cons, Nat.pow_succ]
      omega

/-- The index within the slice is within the slice. -/
theorem denseIndex_lt (ds : List Nat) (j : Nat) : denseIndex ds 0 j < 2 ^ ds.length := by
  obtain ⟨x, hx, hlt⟩ := denseIndex_form ds 0 j
  rw [hx]; simpa using hlt

/-- What the written-out variables of the stretch pick of the index j, as a number. -/
def pick (start count j : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs =>
    (if start ≤ x && x < start + count then (j / 2 ^ x % 2) * 2 ^ (x - start) else 0) +
      pick start count j xs

/-- The number that the slice's index of j gives on the stretch is what j's own bits give there. -/
theorem denseNumber_pick (start count j : Nat) : ∀ (ds : List Nat) (i y : Nat), y < 2 ^ i →
    denseNumber ds i start count (y + denseIndex ds i j) = pick start count j ds
  | [], _, _, _ => rfl
  | d :: ds, i, y, hy => by
    obtain ⟨x, hx, _⟩ := denseIndex_form ds (i + 1) j
    have hb := Nat.mod_lt (j / 2 ^ d) (by decide : 0 < 2)
    have e1 : (y + denseIndex (d :: ds) i j) / 2 ^ i % 2 = j / 2 ^ d % 2 := by
      rw [denseIndex, hx, Nat.pow_succ]
      have : y + (j / 2 ^ d % 2 * 2 ^ i + 2 ^ i * 2 * x) =
          y + 2 ^ i * (j / 2 ^ d % 2 + 2 * x) := by ring
      rw [this, Nat.add_mul_div_left _ _ (Nat.two_pow_pos i), Nat.div_eq_of_lt hy]
      omega
    have e2 : y + denseIndex (d :: ds) i j =
        (y + j / 2 ^ d % 2 * 2 ^ i) + denseIndex ds (i + 1) j := by
      rw [denseIndex]; ring
    have hy' : y + j / 2 ^ d % 2 * 2 ^ i < 2 ^ (i + 1) := by
      rw [Nat.pow_succ]
      have : j / 2 ^ d % 2 * 2 ^ i ≤ 1 * 2 ^ i := Nat.mul_le_mul_right _ (by omega)
      omega
    rw [denseNumber, e1, e2, denseNumber_pick start count j ds (i + 1) _ hy', pick]

/-- The low bits of a number add up to it. -/
theorem sum_bits_nat (m : Nat) : ∀ c : Nat,
    ∑ t ∈ Finset.range c, (m / 2 ^ t % 2) * 2 ^ t = m % 2 ^ c
  | 0 => by simp [Nat.mod_one]
  | c + 1 => by
    rw [Finset.sum_range_succ, sum_bits_nat m c, Nat.mod_pow_succ]
    ring

/-- Written-out variables that are named once each and are all the variables of the stretch pick the
index's number on the stretch. -/
theorem pick_eq (start count j : Nat) (ds : List Nat) (hn : ds.Nodup)
    (hc : (ds.filter fun d => start ≤ d && d < start + count).length = count) :
    pick start count j ds = j / 2 ^ start % 2 ^ count := by
  have h1 : pick start count j ds =
      ((ds.filter fun d => start ≤ d && d < start + count).map fun x =>
        (j / 2 ^ x % 2) * 2 ^ (x - start)).sum := by
    clear hn hc
    induction ds with
    | nil => rfl
    | cons x xs ih =>
      rw [pick, ih, List.filter_cons]
      by_cases hx : (start ≤ x && x < start + count) = true
      · rw [if_pos hx, if_pos hx, List.map_cons, List.sum_cons]
      · rw [if_neg hx, if_neg hx, Nat.zero_add]
  have hnf : (ds.filter fun d => start ≤ d && d < start + count).Nodup := hn.filter _
  have hset : (ds.filter fun d => start ≤ d && d < start + count).toFinset =
      Finset.Ico start (start + count) := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · rw [List.mem_toFinset, List.mem_filter] at hx
      have := hx.2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact Finset.mem_Ico.2 this
    · rw [List.toFinset_card_of_nodup hnf, hc, Nat.card_Ico]
      omega
  rw [h1, ← List.sum_toFinset _ hnf, hset, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left,
    ← sum_bits_nat (j / 2 ^ start) count]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Nat.add_sub_cancel_left, Nat.div_div_eq_div_mul, ← Nat.pow_add]

/-! ## A vector cut below a length -/

/-- **A vector cut below a length**, with or without a written-out factor: the summands add up to
the vector where the index's number on the variables start, .., start + count - 1 is below len, and
to 0 elsewhere. -/
theorem tensorBelow_valG (v : Tensor) (hdist : distinctNats v.denseVars = true)
    (start count len : Nat) (l : List Tensor) (h : tensorBelow v start count len = some l)
    (j : Nat) :
    (l.map fun t => ρ.val (t.entry j)).sum =
      if j / 2 ^ start % 2 ^ count < len then ρ.val (v.entry j) else 0 := by
  classical
  have hb : ∀ t, j / 2 ^ start / 2 ^ t = j / 2 ^ (start + t) := fun t => by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  unfold tensorBelow at h
  dsimp only at h
  split at h
  · cases h
  · rename_i h1
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at h1
    have hn : start + count ≤ v.pairs.length := h1.1
    split at h
    · rename_i h2
      simp only [Option.some.injEq] at h
      subst h
      have h2' : len = 2 ^ count := by simpa using h2
      rw [if_pos (by rw [h2']; exact Nat.mod_lt _ (Nat.two_pow_pos count))]
      simp
    · rename_i h2
      have h2' : len ≠ 2 ^ count := by simpa using h2
      split at h
      · rename_i h3
        simp only [Option.some.injEq] at h
        subst h
        by_cases hlt : j / 2 ^ start % 2 ^ count < len
        · rw [if_pos hlt]; simp
        · rw [if_neg hlt]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          by_contra hne
          refine hlt (lt_of_le_of_lt (le_marked _ _ _ fun t ht hbit => ?_) h3)
          cases hz : isZeroE (v.pairs.getD (start + t) (zeroE, zeroE)).2 with
          | false => simp
          | true =>
            refine absurd (entry_zeroG ρ v j (start + t) (by omega) ?_) hne
            rw [hb] at hbit
            have hc : (j / 2 ^ (start + t) % 2 == 1) = true := by simp [hbit]
            unfold factor
            rw [if_pos hc]
            exact val_of_isZeroE ρ _ hz
      · split at h
        · rename_i h3 h4
          simp only [Option.some.injEq] at h
          subst h
          by_cases hlt : j / 2 ^ start % 2 ^ count < len
          · rw [if_pos hlt]
            simp only [List.map_nil, List.sum_nil]
            by_contra hne
            refine absurd (lt_of_lt_of_le hlt (le_trans h4
              (marked_le _ _ _ fun t ht hm => ?_))) (lt_irrefl _)
            by_contra hbit
            have hz : isZeroE (v.pairs.getD (start + t) (zeroE, zeroE)).1 = true := by
              simp only [Bool.and_eq_true] at hm
              exact hm.2
            refine hne (entry_zeroG ρ v j (start + t) (by omega) ?_).symm
            rw [hb] at hbit
            have hc : ¬ (j / 2 ^ (start + t) % 2 == 1) = true := by simp [hbit]
            unfold factor
            rw [if_neg hc]
            exact val_of_isZeroE ρ _ hz
          · rw [if_neg hlt]; simp
        · rename_i h3 h4
          split at h
          · simp only [Option.some.injEq] at h
            subst h
            have hcut : ∀ q ∈ (List.range count).filter fun q => len.testBit q,
                ((fun t : Tensor => ρ.val (t.entry j)) ∘ fun q =>
                  ({ v with pairs := v.pairs.mapIdx (cutPair start count len q) } : Tensor)) q =
                (if Below (j / 2 ^ start) len count q then 1 else 0) * ρ.val (v.entry j) :=
              fun q hq => entry_cutG ρ v start count len q j
                (List.mem_range.1 (List.mem_filter.1 hq).1) hn
            have hlen : len % 2 ^ count = len := Nat.mod_eq_of_lt (by omega)
            show ((((List.range count).filter fun q => len.testBit q).map fun q =>
              ({ v with pairs := v.pairs.mapIdx (cutPair start count len q) } : Tensor)).map
                fun t => ρ.val (t.entry j)).sum = _
            rw [List.map_map, List.map_congr_left hcut, List.sum_map_mul_right, sum_below, hlen]
            split_ifs <;> simp
          · rename_i h5
            split at h
            · rename_i h6
              simp only [Option.some.injEq] at h
              subst h
              have hc : (v.denseVars.filter fun d => start ≤ d && d < start + count).length =
                  count := by simpa using h6
              have hne : v.denseVars.isEmpty = false := by
                cases hv : v.denseVars with
                | nil => simp [hv] at h5
                | cons a l => rfl
              have hD := denseIndex_lt v.denseVars j
              have hnum : denseNumber v.denseVars 0 start count (denseIndex v.denseVars 0 j) =
                  j / 2 ^ start % 2 ^ count := by
                have := denseNumber_pick start count j v.denseVars 0 0 (by simp)
                rw [Nat.zero_add] at this
                rw [this, pick_eq start count j v.denseVars (nodup_of_distinctNats _ hdist) hc]
              simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
              rw [Tensor.entry_val, Tensor.entry_val]
              simp only [Tensor.denseVal, hne, Bool.false_eq_true, if_false, Nat.zero_add]
              rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hD]
              simp only [Option.getD_some, hnum]
              split_ifs <;> simp [ρ.zero]
            · cases h

/-- The summands of a cut have the vector's variables, the written-out ones too. -/
theorem tensorBelow_memG (v : Tensor) (start count len : Nat) (l : List Tensor)
    (h : tensorBelow v start count len = some l) (t : Tensor) (ht : t ∈ l) :
    t.denseVars = v.denseVars ∧ t.vars = v.vars := by
  unfold tensorBelow at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      rw [List.mem_singleton] at ht
      subst ht
      exact ⟨rfl, rfl⟩
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        rw [List.mem_singleton] at ht
        subst ht
        exact ⟨rfl, rfl⟩
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          cases ht
        · split at h
          · simp only [Option.some.injEq] at h
            subst h
            obtain ⟨q, _, rfl⟩ := List.mem_map.1 ht
            exact ⟨rfl, by simp [Tensor.vars]⟩
          · split at h
            · simp only [Option.some.injEq] at h
              subst h
              rw [List.mem_singleton] at ht
              subst ht
              exact ⟨rfl, rfl⟩
            · cases h

end Desc.K14.Law
