-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Tensors.lean: what the entries of an equality vector, and of a structured
vector cut below a length, read as.

Main names: entry_eq (an entry of Tensor.eq reads as the scalar times eqK), eqK_append,
eqK_add_mul, pairsVal_prod (the product of the pairs' halves, variable by variable), entry_cut,
sum_below, tensorBelow_val.

What is not claimed. tensorBelow_val is for a vector without a written-out factor. Every equation is
between readings, not between the program's words. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes
open OnBytes.Model (Reading)
open OnBytes.Means (Words)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## The equality vector -/

/-- The pairs of an equality vector read as eqK. -/
theorem pairsVal_eq (z : List E) (j : Nat) :
    pairsVal ρ (z.map fun x => (subE oneE x, x)) j = eqK (z.map ρ.val) j := by
  induction z generalizing j with
  | nil => rfl
  | cons x z ih =>
    simp only [List.map_cons, pairsVal, eqK, ih]
    by_cases h : j % 2 = 1 <;> simp [h, ρ.sub, ρ.one]

/-- An entry of an equality vector reads as the scalar times eqK. -/
theorem entry_eq (z : List E) (s : E) (j : Nat) :
    ρ.val ((Tensor.eq z s).entry j) = ρ.val s * eqK (z.map ρ.val) j := by
  rw [Tensor.entry_val]
  simp [Tensor.eq, Tensor.denseVal, pairsVal_eq]

/-- eqK at two lists of coordinates: the second is picked by the higher bits of the index. -/
theorem eqK_append (a b : List K) (j : Nat) :
    eqK (a ++ b) j = eqK a j * eqK b (j / 2 ^ a.length) := by
  induction a generalizing j with
  | nil => simp [eqK]
  | cons x a ih =>
    simp only [List.cons_append, eqK, ih, List.length_cons, Nat.pow_succ', Nat.div_div_eq_div_mul]
    ring

/-- Only the bits of the index below the number of coordinates count. -/
theorem eqK_add_mul (a : List K) (t j : Nat) : eqK a (t + 2 ^ a.length * j) = eqK a t := by
  induction a generalizing t j with
  | nil => rfl
  | cons x a ih =>
    have e : 2 ^ (x :: a).length * j = 2 * (2 ^ a.length * j) := by
      rw [List.length_cons, Nat.pow_succ']; ring
    have h1 : (t + 2 * (2 ^ a.length * j)) % 2 = t % 2 := by omega
    have h2 : (t + 2 * (2 ^ a.length * j)) / 2 = t / 2 + 2 ^ a.length * j := by omega
    rw [e]
    simp only [eqK, h1, h2, ih]

/-! ## The product of the pairs' halves, variable by variable -/

/-- The half of pair number i that the index j picks, read in K. -/
def factor (ps : List (E × E)) (j i : Nat) : K :=
  ρ.val (if j / 2 ^ i % 2 == 1 then (ps.getD i (zeroE, zeroE)).2 else (ps.getD i (zeroE, zeroE)).1)

/-- The product of the pairs' halves is the product of the factors. -/
theorem pairsVal_prod (ps : List (E × E)) (j : Nat) :
    pairsVal ρ ps j = ∏ i ∈ Finset.range ps.length, factor ρ ps j i := by
  induction ps generalizing j with
  | nil => simp [pairsVal]
  | cons p ps ih =>
    rw [List.length_cons, Finset.prod_range_succ', pairsVal, ih, mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      unfold factor
      rw [List.getD_cons_succ, Nat.pow_succ', ← Nat.div_div_eq_div_mul]
    · simp [factor]

/-- The pair that a summand of the cut has in the place of pair number i. -/
def cutPair (start count len q i : Nat) (p : E × E) : E × E :=
  if i < start + q || start + count ≤ i then p
  else if i == start + q then (p.1, zeroE)
  else if len.testBit (i - start) then (zeroE, p.2)
  else (p.1, zeroE)

/-- The index j has, at bit i, what summand number q of the cut lets through. -/
def Keeps (start count len q j i : Nat) : Prop :=
  if i < start + q ∨ start + count ≤ i then True
  else if i = start + q then j / 2 ^ i % 2 ≠ 1
  else (j / 2 ^ i % 2 = 1 ↔ len.testBit (i - start) = true)

/-- It can be computed. -/
instance (start count len q j i : Nat) : Decidable (Keeps start count len q j i) := by
  unfold Keeps; infer_instance

/-- Outside the stretch from bit q on the pair stays. -/
theorem cutPair_out (start count len q i : Nat) (p : E × E)
    (h : i < start + q ∨ start + count ≤ i) : cutPair start count len q i p = p := by
  unfold cutPair
  rw [if_pos (by simpa using h)]

/-- At bit q the high half goes. -/
theorem cutPair_at (start count len q i : Nat) (p : E × E)
    (h : ¬ (i < start + q ∨ start + count ≤ i)) (h2 : i = start + q) :
    cutPair start count len q i p = (p.1, zeroE) := by
  unfold cutPair
  rw [if_neg (by simpa using h), if_pos (by simpa using h2)]

/-- Above bit q, where len has a 1, the low half goes. -/
theorem cutPair_hi (start count len q i : Nat) (p : E × E)
    (h : ¬ (i < start + q ∨ start + count ≤ i)) (h2 : ¬ i = start + q)
    (h3 : len.testBit (i - start) = true) : cutPair start count len q i p = (zeroE, p.2) := by
  unfold cutPair
  rw [if_neg (by simpa using h), if_neg (by simpa using h2), if_pos h3]

/-- Above bit q, where len has a 0, the high half goes. -/
theorem cutPair_lo (start count len q i : Nat) (p : E × E)
    (h : ¬ (i < start + q ∨ start + count ≤ i)) (h2 : ¬ i = start + q)
    (h3 : ¬ len.testBit (i - start) = true) : cutPair start count len q i p = (p.1, zeroE) := by
  unfold cutPair
  rw [if_neg (by simpa using h), if_neg (by simpa using h2), if_neg h3]

/-- A factor of a summand of the cut: the old factor, or 0. -/
theorem factor_cut (ps : List (E × E)) (start count len q j i : Nat) (hi : i < ps.length) :
    factor ρ (ps.mapIdx (cutPair start count len q)) j i =
      (if Keeps start count len q j i then 1 else 0) * factor ρ ps j i := by
  have hg : (ps.mapIdx (cutPair start count len q)).getD i (zeroE, zeroE) =
      cutPair start count len q i (ps.getD i (zeroE, zeroE)) := by
    simp [List.getD_eq_getElem?_getD, hi]
  unfold factor
  rw [hg]
  by_cases h1 : i < start + q ∨ start + count ≤ i
  · have hk : Keeps start count len q j i := by
      unfold Keeps; rw [if_pos h1]; trivial
    rw [cutPair_out _ _ _ _ _ _ h1, if_pos hk, one_mul]
  · by_cases h2 : i = start + q
    · have hk : Keeps start count len q j i ↔ j / 2 ^ i % 2 ≠ 1 := by
        unfold Keeps; rw [if_neg h1, if_pos h2]
      rw [cutPair_at _ _ _ _ _ _ h1 h2]
      by_cases h4 : j / 2 ^ i % 2 = 1
      · rw [if_neg (fun h => hk.1 h h4)]; simp [h4, ρ.zero]
      · rw [if_pos (hk.2 h4)]; simp [h4]
    · have hk : Keeps start count len q j i ↔
          (j / 2 ^ i % 2 = 1 ↔ len.testBit (i - start) = true) := by
        unfold Keeps; rw [if_neg h1, if_neg h2]
      by_cases h3 : len.testBit (i - start) = true
      · rw [cutPair_hi _ _ _ _ _ _ h1 h2 h3]
        by_cases h4 : j / 2 ^ i % 2 = 1
        · rw [if_pos (hk.2 ⟨fun _ => h3, fun _ => h4⟩)]; simp [h4]
        · rw [if_neg (fun h => h4 ((hk.1 h).2 h3))]; simp [h4, ρ.zero]
      · rw [cutPair_lo _ _ _ _ _ _ h1 h2 h3]
        by_cases h4 : j / 2 ^ i % 2 = 1
        · rw [if_neg (fun h => h3 ((hk.1 h).1 h4))]; simp [h4, ρ.zero]
        · rw [if_pos (hk.2 ⟨fun x => absurd x h4, fun x => absurd x h3⟩)]; simp [h4]

/-- The number m is below len, and q is the highest of the low c bits at which they differ. -/
def Below (m len c q : Nat) : Prop :=
  m / 2 ^ q % 2 ≠ 1 ∧ ∀ t, q < t → t < c → (m / 2 ^ t % 2 = 1 ↔ len.testBit t = true)

/-- A summand lets an index through at every bit just if the index's number is below len with q the
highest bit of difference. -/
theorem keeps_all (start count len q j n : Nat) (hq : q < count) (hn : start + count ≤ n) :
    (∀ i ∈ Finset.range n, Keeps start count len q j i) ↔ Below (j / 2 ^ start) len count q := by
  have hb : ∀ t, j / 2 ^ start / 2 ^ t = j / 2 ^ (start + t) := fun t => by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  constructor
  · intro h
    refine ⟨?_, fun t h1 h2 => ?_⟩
    · have h0 := h (start + q) (Finset.mem_range.2 (by omega))
      have e1 : ¬ (start + q < start + q ∨ start + count ≤ start + q) := by omega
      unfold Keeps at h0
      rw [if_neg e1, if_pos rfl] at h0
      rwa [hb]
    · have h0 := h (start + t) (Finset.mem_range.2 (by omega))
      have e1 : ¬ (start + t < start + q ∨ start + count ≤ start + t) := by omega
      have e2 : ¬ (start + t = start + q) := by omega
      unfold Keeps at h0
      rw [if_neg e1, if_neg e2, Nat.add_sub_cancel_left] at h0
      rwa [hb]
  · rintro ⟨h1, h2⟩ i _
    unfold Keeps
    split_ifs with a b
    · subst b
      have h0 := h1
      rw [hb] at h0
      exact h0
    · have h0 := h2 (i - start) (by omega) (by omega)
      rwa [hb, Nat.add_sub_cancel' (by omega)] at h0

open Classical in
/-- Of the bits q of len that are 1, just one is the highest bit of difference if m is below len in
the low c bits, and none else. -/
theorem sum_below (m len : Nat) : ∀ c : Nat,
    (((List.range c).filter fun q => len.testBit q).map fun q =>
      if Below m len c q then (1 : K) else 0).sum = if m % 2 ^ c < len % 2 ^ c then 1 else 0 := by
  intro c
  induction c with
  | zero => simp [Nat.mod_one]
  | succ c ih =>
    have hstep : ∀ q ∈ (List.range c).filter fun q => len.testBit q,
        (if Below m len (c + 1) q then (1 : K) else 0) =
          (if (m / 2 ^ c % 2 = 1 ↔ len.testBit c = true) then 1 else 0) *
            (if Below m len c q then 1 else 0) := by
      intro q hq
      have hqc : q < c := List.mem_range.1 (List.mem_filter.1 hq).1
      have : Below m len (c + 1) q ↔
          ((m / 2 ^ c % 2 = 1 ↔ len.testBit c = true) ∧ Below m len c q) := by
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h2 c hqc (Nat.lt_succ_self c), h1, fun t a b => h2 t a (by omega)⟩
        · rintro ⟨h0, h1, h2⟩
          refine ⟨h1, fun t a b => ?_⟩
          by_cases e : t = c
          · subst e; exact h0
          · exact h2 t a (by omega)
      by_cases a : (m / 2 ^ c % 2 = 1 ↔ len.testBit c = true) <;> by_cases b : Below m len c q <;>
        simp [this, a, b]
    have hlast : Below m len (c + 1) c ↔ m / 2 ^ c % 2 ≠ 1 :=
      ⟨fun h => h.1, fun h => ⟨h, fun t a b => by omega⟩⟩
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append,
      List.map_congr_left hstep, List.sum_map_mul_left, ih]
    have hm := @Nat.mod_pow_succ m 2 c
    have hl := @Nat.mod_pow_succ len 2 c
    have hx := Nat.mod_lt m (Nat.two_pow_pos c)
    have hy := Nat.mod_lt len (Nat.two_pow_pos c)
    have ht : len.testBit c = decide (len / 2 ^ c % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
    by_cases hb : len.testBit c = true
    · have b : len / 2 ^ c % 2 = 1 := by simpa [ht] using hb
      have hf : List.filter (fun q => len.testBit q) [c] = [c] := by simp [hb]
      rw [hf]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      by_cases a : m / 2 ^ c % 2 = 1
      · rw [if_pos (iff_of_true a hb), if_neg (fun h => hlast.1 h a), one_mul, add_zero, hm, hl, a,
          b]
        exact if_congr (by omega) rfl rfl
      · have a0 : m / 2 ^ c % 2 = 0 := by omega
        rw [if_neg (fun h => a (h.2 hb)), if_pos (hlast.2 a), zero_mul, zero_add, hm, hl, a0, b,
          if_pos (by omega)]
    · have b : len / 2 ^ c % 2 = 0 := by
        have : ¬ len / 2 ^ c % 2 = 1 := by simpa [ht] using hb
        omega
      have hf : List.filter (fun q => len.testBit q) [c] = [] := by simp [hb]
      rw [hf]
      simp only [List.map_nil, List.sum_nil, add_zero]
      by_cases a : m / 2 ^ c % 2 = 1
      · rw [if_neg (fun h => hb (h.1 a)), zero_mul, hm, hl, a, b, if_neg (by omega)]
      · have a0 : m / 2 ^ c % 2 = 0 := by omega
        rw [if_pos (iff_of_false a hb), one_mul, hm, hl, a0, b]
        exact if_congr (by omega) rfl rfl

/-- A number whose bits 1 are all marked is at most the sum of the marked powers of two. -/
theorem le_marked (b : Nat → Bool) (m : Nat) : ∀ c : Nat,
    (∀ t < c, m / 2 ^ t % 2 = 1 → b t = true) →
    m % 2 ^ c ≤ (List.range c).foldl (fun s t => if b t then s + 2 ^ t else s) 0 := by
  intro c
  induction c with
  | zero => intro _; simp [Nat.mod_one]
  | succ c ih =>
    intro h
    have h0 := ih fun t ht => h t (by omega)
    rw [List.range_succ, List.foldl_append, Nat.mod_pow_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ c) with a | a
    · rw [a]; split_ifs <;> omega
    · rw [a, if_pos (h c (Nat.lt_succ_self c) a)]; omega

/-- A number that has a bit 1 wherever a mark is, is at least the sum of the marked powers. -/
theorem marked_le (b : Nat → Bool) (m : Nat) : ∀ c : Nat,
    (∀ t < c, b t = true → m / 2 ^ t % 2 = 1) →
    (List.range c).foldl (fun s t => if b t then s + 2 ^ t else s) 0 ≤ m % 2 ^ c := by
  intro c
  induction c with
  | zero => intro _; simp
  | succ c ih =>
    intro h
    have h0 := ih fun t ht => h t (by omega)
    rw [List.range_succ, List.foldl_append, Nat.mod_pow_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    split_ifs with a
    · rw [h c (Nat.lt_succ_self c) a]; omega
    · omega

/-! ## A vector cut below a length -/

/-- An entry of a vector without a written-out factor. -/
theorem entry_plain (v : Tensor) (hd : v.denseVars = []) (j : Nat) :
    ρ.val (v.entry j) = ρ.val v.scalar * pairsVal ρ v.pairs j := by
  rw [Tensor.entry_val]
  simp [Tensor.denseVal, hd]

/-- An entry with a factor 0 reads as 0. -/
theorem entry_zero (v : Tensor) (hd : v.denseVars = []) (j i : Nat) (hi : i < v.pairs.length)
    (h : factor ρ v.pairs j i = 0) : ρ.val (v.entry j) = 0 := by
  rw [entry_plain ρ v hd, pairsVal_prod, Finset.prod_eq_zero (Finset.mem_range.2 hi) h, mul_zero]

open Classical in
/-- An entry of summand number q of the cut. -/
theorem entry_cut (v : Tensor) (hd : v.denseVars = []) (start count len q j : Nat)
    (hq : q < count) (hn : start + count ≤ v.pairs.length) :
    ρ.val (({ v with
      pairs := v.pairs.mapIdx (cutPair start count len q), denseVars := [] } : Tensor).entry j) =
      (if Below (j / 2 ^ start) len count q then 1 else 0) * ρ.val (v.entry j) := by
  rw [entry_plain ρ ({ v with
      pairs := v.pairs.mapIdx (cutPair start count len q), denseVars := [] } : Tensor) rfl,
    entry_plain ρ v hd, pairsVal_prod, pairsVal_prod, List.length_mapIdx,
    Finset.prod_congr rfl fun i hi => factor_cut ρ v.pairs start count len q j i
      (Finset.mem_range.1 hi), Finset.prod_mul_distrib, Finset.prod_boole]
  by_cases hB : Below (j / 2 ^ start) len count q
  · rw [if_pos hB, if_pos ((keeps_all start count len q j _ hq hn).2 hB)]; ring
  · rw [if_neg hB, if_neg fun h => hB ((keeps_all start count len q j _ hq hn).1 h)]; ring

/-- **A vector cut below a length**: the summands add up to the vector where the index's number on
the variables start, .., start + count - 1 is below len, and to 0 elsewhere. -/
theorem tensorBelow_val (v : Tensor) (hd : v.denseVars = []) (start count len : Nat)
    (l : List Tensor) (h : tensorBelow v start count len = some l) (j : Nat) :
    (l.map fun t => ρ.val (t.entry j)).sum =
      if j / 2 ^ start % 2 ^ count < len then ρ.val (v.entry j) else 0 := by
  classical
  have hb : ∀ t, j / 2 ^ start / 2 ^ t = j / 2 ^ (start + t) := fun t => by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  unfold tensorBelow at h
  simp only [hd] at h
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
          | false => simp [hz]
          | true =>
            refine absurd (entry_zero ρ v hd j (start + t) (by omega) ?_) hne
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
              simpa using hm
            refine hne (entry_zero ρ v hd j (start + t) (by omega) ?_).symm
            rw [hb] at hbit
            have hc : ¬ (j / 2 ^ (start + t) % 2 == 1) = true := by simp [hbit]
            unfold factor
            rw [if_neg hc]
            exact val_of_isZeroE ρ _ hz
          · rw [if_neg hlt]; simp
        · rename_i h3 h4
          simp only [List.filter_nil, List.length_nil, beq_self_eq_true, if_true,
            Option.some.injEq] at h
          subst h
          have hcut : ∀ q ∈ (List.range count).filter fun q => len.testBit q,
              ((fun t : Tensor => ρ.val (t.entry j)) ∘ fun q =>
                ({ v with pairs := v.pairs.mapIdx (cutPair start count len q),
                          denseVars := [] } : Tensor)) q =
              (if Below (j / 2 ^ start) len count q then 1 else 0) * ρ.val (v.entry j) :=
            fun q hq => entry_cut ρ v hd start count len q j
              (List.mem_range.1 (List.mem_filter.1 hq).1) hn
          have hlen : len % 2 ^ count = len := Nat.mod_eq_of_lt (by omega)
          show ((((List.range count).filter fun q => len.testBit q).map fun q =>
            ({ v with pairs := v.pairs.mapIdx (cutPair start count len q),
                      denseVars := [] } : Tensor)).map
              fun t => ρ.val (t.entry j)).sum = _
          rw [List.map_map, List.map_congr_left hcut, List.sum_map_mul_right, sum_below, hlen]
          split_ifs <;> simp

/-- The summands of a cut have the vector's number of variables and no written-out factor. -/
theorem tensorBelow_mem (v : Tensor) (hd : v.denseVars = []) (start count len : Nat)
    (l : List Tensor) (h : tensorBelow v start count len = some l) (t : Tensor) (ht : t ∈ l) :
    t.denseVars = [] ∧ t.vars = v.vars := by
  unfold tensorBelow at h
  simp only [hd] at h
  split at h
  · cases h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      rw [List.mem_singleton] at ht
      subst ht
      exact ⟨hd, rfl⟩
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        rw [List.mem_singleton] at ht
        subst ht
        exact ⟨hd, rfl⟩
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          cases ht
        · simp only [List.filter_nil, List.length_nil, beq_self_eq_true, if_true,
            Option.some.injEq] at h
          subst h
          obtain ⟨q, _, rfl⟩ := List.mem_map.1 ht
          exact ⟨rfl, by simp [Tensor.vars]⟩

end Desc.K14.Law
