-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsPlan.lean: WHERE h ≤ k: IN THE PUBLIC LISTS OF COINS'
NUMBERS OF A ROW OF A FOLD's FRESH TABLE OF k VARIABLES IN 2 ^ h ROWS (plan k h b,
Johnson/SendSim/At/RideLay.lean) NO NUMBER STANDS TWICE, EVERY NUMBER LIES BELOW 2 k + 1, AND A
NUMBER STANDS AT ONE PLACE's NUMBER IN WHICHEVER ROWS IT STANDS. Index arithmetic alone: no coin, no
field, no shape is named. One definition with code; statements with their proofs.

  coinPlace       **the place's number of a coin's number**: a function of k, h and the number
  plan_place, plan_one_place   a number in the entry number j of a row has coinPlace = j: so it
                  stands at one place's number in all rows
  plan_once       **in one row no number stands twice**: neither twice in one place nor at two
                  places
  plan_places, plan_below   a row has 2 k - h + 1 places; its numbers lie below 2 k + 1
  plan_mem        the numbers of a row, sorted in three
  plan_rows_low, plan_rows_high   **THE PACKING's OWN WAY, TOLD AS IT IS**: a coefficient of a
                  variable up to h stands in just the rows that reach that variable (reaches,
                  Fmt/M1Fold.lean: the row's bits from the variable's on are all 1); the
                  coefficients of the variables above h, and the constant's coin, stand IN EVERY ROW
  plan_last_all        every number below 2 k + 1 stands in the last row
  The others: small steps.

pairs_length and pairs_get (Honest/K1/RideLaw.lean) are called. plan, firstPlan and ixOf are another
file's definitions, called here, not typed again; that file shows that a row, read in the field, is
the plan's sums, and says of itself that it does not say at how many places a coin stands, nor that
the laying is one to one.
Kin. THE NEAREST: Honest/K1/RideLaw.lean's sig, sig_lt, sig_inj, sig_onto and lay_one: the case of
one row (h = 0), told from the place to the coin: that coinPlace k 0 is sig's inverse there is tied
by no theorem. That file's own limit: at more than one row it has no law on how the coins are laid.
This file is the half of that law that is on the numbers.
What is spent. h ≤ k is a premise of every main statement. plan_place, plan_one_place, plan_once,
plan_places and plan_rows_low fail without it; plan_below fails without it at k = 0 alone; plan_mem,
plan_rows_high and plan_last_all take it and do not need it. At (k, h) = (1, 2) the last row is [[0,
1, 1], [2], [2]] (by the definitions' text). At k = 0, where h = 0, the constant's number 2 (k - 1)
is 0, by the naturals' subtraction, and all the laws hold.
What is not claimed. That the laying is one to one: no coin is named here. Anything on a coin's
value, on what a table is for, or on what follows where a number stands in several rows. Nothing on
soundness, completeness or hiding.
-/
import Johnson.SendSim.At.RideLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes.SendSim.At (ixOf plan firstPlan)
open Fmt.M1.FoldOwn (reaches)

/-- A fold that lays f i behind a list at the members i that pass p: the list, then the passing
members' values. -/
theorem foldl_filter {α : Type} (p : ℕ → Bool) (f : ℕ → α) : ∀ (L : List ℕ) (s : List α),
    L.foldl (fun s i => if p i then s ++ [f i] else s) s = s ++ (L.filter p).map f
  | [], s => by simp
  | i :: L, s => by
    rw [List.foldl_cons, foldl_filter p f L]
    by_cases h : p i = true
    · simp [h]
    · simp [h]

/-- A row's first list: the one number that every row has there, then one for each variable up to h
that the row reaches. -/
theorem firstPlan_list (k h b : ℕ) : firstPlan k h b =
    (if h < k then ixOf k (h + 1) 1 else 2 * (k - 1)) ::
      ((List.range h).filter fun i => reaches h b (i + 1)).map fun i => ixOf k (i + 1) 1 := by
  unfold firstPlan
  rw [foldl_filter (fun i => reaches h b (i + 1)) (fun i => ixOf k (i + 1) 1)]
  rfl

/-- **The place's number at which the coin number n stands**, in whichever rows it stands: a
function of k, h and n alone. Meant for n below 2 k + 1 and h ≤ k. -/
def coinPlace (k h n : ℕ) : ℕ :=
  if n = 2 * (k - 1) then (if h < k then 2 * k - h else 0)
  else if n < 2 * (k - 1) then
    (if n % 2 = 0 then (if n / 2 + 1 ≤ h + 1 then 0 else h + 2 + 2 * (n / 2 + 1 - h - 2))
     else (if n / 2 + 1 ≤ h + 1 then n / 2 + 1 else h + 3 + 2 * (n / 2 + 1 - h - 2)))
  else if n = 2 * (k - 1) + 1 then (if k ≤ h + 1 then 0 else h + 2 + 2 * (k - h - 2))
  else (if k ≤ h + 1 then k else h + 3 + 2 * (k - h - 2))

/-- The place's number of the coefficient of degree 1 at the variable l. -/
theorem coinPlace_ix1 {k h l : ℕ} (h1 : 1 ≤ l) (hl : l ≤ k) :
    coinPlace k h (ixOf k l 1) = if l ≤ h + 1 then 0 else h + 2 + 2 * (l - h - 2) := by
  unfold coinPlace ixOf
  split_ifs <;> omega

/-- The place's number of the coefficient of degree 2 at the variable l. -/
theorem coinPlace_ix2 {k h l : ℕ} (h1 : 1 ≤ l) (hl : l ≤ k) :
    coinPlace k h (ixOf k l 2) = if l ≤ h + 1 then l else h + 3 + 2 * (l - h - 2) := by
  unfold coinPlace ixOf
  split_ifs <;> omega

/-- The place's number of the constant's coin, the number 2 (k - 1). -/
theorem coinPlace_const (k h : ℕ) :
    coinPlace k h (2 * (k - 1)) = if h < k then 2 * k - h else 0 := by
  unfold coinPlace
  simp

/-- **A number that stands in the entry number j of a row has the place's number j.** -/
theorem plan_place {k h b : ℕ} (hh : h ≤ k) : ∀ (j : ℕ) (I : List ℕ), (plan k h b)[j]? = some I →
    ∀ n ∈ I, coinPlace k h n = j := by
  intro j I hI n hn
  unfold plan at hI
  cases j with
  | zero =>
    rw [List.cons_append, List.getElem?_cons_zero] at hI
    obtain rfl := Option.some.inj hI
    rw [firstPlan_list] at hn
    rcases List.mem_cons.1 hn with rfl | hn
    · by_cases hk : h < k
      · rw [if_pos hk, coinPlace_ix1 (by omega) (by omega), if_pos (by omega)]
      · rw [if_neg hk, coinPlace_const, if_neg hk]
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hn
      have hi' := List.mem_range.1 (List.mem_filter.1 hi).1
      rw [coinPlace_ix1 (by omega) (by omega), if_pos (by omega)]
  | succ j' =>
    rw [List.cons_append, List.getElem?_cons_succ] at hI
    by_cases hj : j' < h
    · rw [List.getElem?_append_left (by simpa using hj), List.getElem?_map,
        List.getElem?_range hj] at hI
      obtain rfl := Option.some.inj hI
      replace hn : n ∈ (if reaches h b (j' + 1) = true then [ixOf k (j' + 1) 2] else []) := hn
      by_cases hr : reaches h b (j' + 1) = true
      · rw [if_pos hr] at hn
        obtain rfl := List.mem_singleton.1 hn
        rw [coinPlace_ix2 (by omega) (by omega), if_pos (by omega)]
      · rw [if_neg hr] at hn
        cases hn
    · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_lt hj)] at hI
      simp only [List.length_map, List.length_range] at hI
      by_cases hk : h < k
      · rw [if_pos hk] at hI
        obtain ⟨q, hq⟩ : ∃ q, j' - h = q := ⟨_, rfl⟩
        rw [hq] at hI
        cases q with
        | zero =>
          rw [List.cons_append, List.getElem?_cons_zero] at hI
          obtain rfl := Option.some.inj hI
          obtain rfl := List.mem_singleton.1 hn
          rw [coinPlace_ix2 (by omega) (by omega), if_pos (by omega)]
          omega
        | succ q' =>
          rw [List.cons_append, List.getElem?_cons_succ] at hI
          by_cases hq' : q' < 2 * (k - h - 1)
          · rw [List.getElem?_append_left (by rw [K1.pairs_length]; exact hq'),
              K1.pairs_get _ _ _ _ hq'] at hI
            obtain rfl := Option.some.inj hI
            by_cases he : q' % 2 = 0
            · rw [if_pos he] at hn
              obtain rfl := List.mem_singleton.1 hn
              rw [coinPlace_ix1 (by omega) (by omega), if_neg (by omega)]
              omega
            · rw [if_neg he] at hn
              obtain rfl := List.mem_singleton.1 hn
              rw [coinPlace_ix2 (by omega) (by omega), if_neg (by omega)]
              omega
          · rw [List.getElem?_append_right (by rw [K1.pairs_length]; omega), K1.pairs_length] at hI
            obtain ⟨u, hu⟩ : ∃ u, q' - 2 * (k - h - 1) = u := ⟨_, rfl⟩
            rw [hu] at hI
            cases u with
            | zero =>
              rw [List.getElem?_cons_zero] at hI
              obtain rfl := Option.some.inj hI
              obtain rfl := List.mem_singleton.1 hn
              rw [coinPlace_const, if_pos hk]
              omega
            | succ u' => simp at hI
      · rw [if_neg hk] at hI
        simp at hI

/-- **In whichever rows a number stands, it stands at one place's number.** -/
theorem plan_one_place {k h b b' j j' n : ℕ} (hh : h ≤ k) (h1 : n ∈ (plan k h b).getD j [])
    (h2 : n ∈ (plan k h b').getD j' []) : j = j' := by
  rw [List.getD_eq_getElem?_getD] at h1 h2
  cases e1 : (plan k h b)[j]? with
  | none => rw [e1] at h1; cases h1
  | some I =>
    cases e2 : (plan k h b')[j']? with
    | none => rw [e2] at h2; cases h2
    | some I' =>
      rw [e1] at h1
      rw [e2] at h2
      exact (plan_place hh j I e1 n h1).symm.trans (plan_place hh j' I' e2 n h2)

/-- On plain lists: where each member of the entry number j has the key s + j, and no entry has a
member twice, the entries laid in a row have no member twice. -/
theorem flatten_nodup_of_key {α : Type} (g : α → ℕ) : ∀ (L : List (List α)) (s : ℕ),
    (∀ j I, L[j]? = some I → ∀ x ∈ I, g x = s + j) → (∀ I ∈ L, I.Nodup) → L.flatten.Nodup
  | [], _, _, _ => by simp
  | I :: L, s, hk, hn => by
    rw [List.flatten_cons, List.nodup_append]
    refine ⟨hn I List.mem_cons_self, ?_, ?_⟩
    · refine flatten_nodup_of_key g L (s + 1) (fun j J hJ x hx => ?_)
        fun J hJ => hn J (List.mem_cons_of_mem _ hJ)
      have := hk (j + 1) J (by rw [List.getElem?_cons_succ]; exact hJ) x hx
      omega
    · intro x hx y hy e
      obtain ⟨J, hJ, hyJ⟩ := List.mem_flatten.1 hy
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hJ
      have h0 := hk 0 I (by rw [List.getElem?_cons_zero]) x hx
      have h1 := hk (j + 1) J (by rw [List.getElem?_cons_succ]; exact hj) y hyJ
      rw [e] at h0
      omega

/-- The numbers of the coefficients of degree 1 rise with the variable. -/
theorem ix1_lt {k i i' : ℕ} (h : i < i') (h' : i' + 1 ≤ k) :
    ixOf k (i + 1) 1 < ixOf k (i' + 1) 1 := by
  unfold ixOf
  split_ifs <;> omega

/-- A row's first list has no number twice. -/
theorem firstPlan_nodup {k h b : ℕ} (hh : h ≤ k) : (firstPlan k h b).Nodup := by
  rw [firstPlan_list, List.nodup_cons]
  constructor
  · intro hm
    obtain ⟨i, hi, e⟩ := List.mem_map.1 hm
    have hi' := List.mem_range.1 (List.mem_filter.1 hi).1
    by_cases hk : h < k
    · rw [if_pos hk] at e
      have := ix1_lt (k := k) hi' (by omega)
      omega
    · rw [if_neg hk] at e
      unfold ixOf at e
      split_ifs at e <;> omega
  · refine List.Nodup.map_on (fun i hi i' hi' e => ?_) (List.nodup_range.filter _)
    have a1 := List.mem_range.1 (List.mem_filter.1 hi).1
    have a2 := List.mem_range.1 (List.mem_filter.1 hi').1
    rcases Nat.lt_trichotomy i i' with q | q | q
    · have := ix1_lt (k := k) q (by omega)
      omega
    · exact q
    · have := ix1_lt (k := k) q (by omega)
      omega

/-- No entry of a row has a number twice. -/
theorem plan_entry_nodup {k h b : ℕ} (hh : h ≤ k) : ∀ I ∈ plan k h b, I.Nodup := by
  intro I hI
  unfold plan at hI
  rw [List.cons_append] at hI
  rcases List.mem_cons.1 hI with rfl | hI
  · exact firstPlan_nodup hh
  · rcases List.mem_append.1 hI with hI | hI
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hI
      split_ifs <;> simp
    · split_ifs at hI with hk
      · rw [List.cons_append] at hI
        rcases List.mem_cons.1 hI with rfl | hI
        · simp
        · rcases List.mem_append.1 hI with hI | hI
          · obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 hI
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl <;> simp
          · obtain rfl := List.mem_singleton.1 hI
            simp
      · cases hI

/-- **IN ONE ROW NO NUMBER STANDS TWICE**: neither twice in one place nor at two places. -/
theorem plan_once {k h b : ℕ} (hh : h ≤ k) : (plan k h b).flatten.Nodup :=
  flatten_nodup_of_key (coinPlace k h) (plan k h b) 0
    (fun j I hI n hn => by rw [plan_place hh j I hI n hn, Nat.zero_add]) (plan_entry_nodup hh)

/-- A row has 2 k - h + 1 places. -/
theorem plan_places {k h b : ℕ} (hh : h ≤ k) : (plan k h b).length = 2 * k - h + 1 := by
  unfold plan
  by_cases hk : h < k
  · rw [if_pos hk]
    simp only [List.cons_append, List.length_cons, List.length_append, List.length_map,
      List.length_range, K1.pairs_length, List.length_nil]
    omega
  · rw [if_neg hk]
    simp only [List.cons_append, List.length_cons, List.length_append, List.length_map,
      List.length_range, List.length_nil]
    omega

/-- Two coefficients with one number are one coefficient. -/
theorem ixOf_inj {k l t l' t' : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ k) (h3 : t = 1 ∨ t = 2) (h1' : 1 ≤ l')
    (h2' : l' ≤ k) (h3' : t' = 1 ∨ t' = 2) (e : ixOf k l t = ixOf k l' t') : l = l' ∧ t = t' := by
  unfold ixOf at e
  rcases h3 with rfl | rfl <;> rcases h3' with rfl | rfl <;> split_ifs at e <;> omega

/-- No coefficient has the constant's number. -/
theorem ixOf_ne_const {k l t : ℕ} (h1 : 1 ≤ l) (h3 : t = 1 ∨ t = 2) :
    ixOf k l t ≠ 2 * (k - 1) := by
  unfold ixOf
  rcases h3 with rfl | rfl <;> split_ifs <;> omega

/-- A coefficient's number lies below 2 k + 1. -/
theorem ixOf_below {k l t : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ k) (h3 : t = 1 ∨ t = 2) :
    ixOf k l t < 2 * k + 1 := by
  unfold ixOf
  rcases h3 with rfl | rfl <;> split_ifs <;> omega

/-- The members of a row's first list. -/
theorem mem_first {k h b n : ℕ} : n ∈ firstPlan k h b ↔
    n = (if h < k then ixOf k (h + 1) 1 else 2 * (k - 1)) ∨
      ∃ i, i < h ∧ reaches h b (i + 1) = true ∧ n = ixOf k (i + 1) 1 := by
  rw [firstPlan_list, List.mem_cons]
  constructor
  · rintro (e | hm)
    · exact .inl e
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hm
      exact .inr ⟨i, List.mem_range.1 (List.mem_filter.1 hi).1, (List.mem_filter.1 hi).2, rfl⟩
  · rintro (e | ⟨i, hi, hr, rfl⟩)
    · exact .inl e
    · exact .inr (List.mem_map.2 ⟨i, List.mem_filter.2 ⟨List.mem_range.2 hi, hr⟩, rfl⟩)

/-- The members of the places 1 to h. -/
theorem mem_second {k h b n : ℕ} :
    n ∈ ((List.range h).map fun i =>
      if reaches h b (i + 1) then [ixOf k (i + 1) 2] else []).flatten ↔
      ∃ i, i < h ∧ reaches h b (i + 1) = true ∧ n = ixOf k (i + 1) 2 := by
  constructor
  · intro hm
    obtain ⟨I, hI, hn⟩ := List.mem_flatten.1 hm
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hI
    replace hn : n ∈ (if reaches h b (i + 1) = true then [ixOf k (i + 1) 2] else []) := hn
    by_cases hr : reaches h b (i + 1) = true
    · rw [if_pos hr] at hn
      exact ⟨i, List.mem_range.1 hi, hr, List.mem_singleton.1 hn⟩
    · rw [if_neg hr] at hn
      cases hn
  · rintro ⟨i, hi, hr, rfl⟩
    refine List.mem_flatten.2 ⟨[ixOf k (i + 1) 2], List.mem_map.2 ⟨i, List.mem_range.2 hi, ?_⟩,
      List.mem_singleton.2 rfl⟩
    show (if reaches h b (i + 1) = true then [ixOf k (i + 1) 2] else []) = _
    rw [if_pos hr]

/-- The members of the places behind h, where h < k. -/
theorem mem_third {k h n : ℕ} :
    n ∈ ([ixOf k (h + 1) 2] ::
      ((List.range (k - h - 1)).flatMap fun i =>
        [[ixOf k (h + 2 + i) 1], [ixOf k (h + 2 + i) 2]]) ++ [[2 * (k - 1)]]).flatten ↔
      n = ixOf k (h + 1) 2 ∨ (∃ i, i < k - h - 1 ∧
        (n = ixOf k (h + 2 + i) 1 ∨ n = ixOf k (h + 2 + i) 2)) ∨ n = 2 * (k - 1) := by
  rw [List.cons_append, List.flatten_cons, List.flatten_append, List.mem_append, List.mem_append,
    List.mem_singleton]
  constructor
  · rintro (e | hm | hm)
    · exact .inl e
    · obtain ⟨I, hI, hn⟩ := List.mem_flatten.1 hm
      obtain ⟨i, hi, hI'⟩ := List.mem_flatMap.1 hI
      rcases List.mem_cons.1 hI' with rfl | hI'
      · exact .inr (.inl ⟨i, List.mem_range.1 hi, .inl (List.mem_singleton.1 hn)⟩)
      · obtain rfl := List.mem_singleton.1 hI'
        exact .inr (.inl ⟨i, List.mem_range.1 hi, .inr (List.mem_singleton.1 hn)⟩)
    · simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_singleton] at hm
      exact .inr (.inr hm)
  · rintro (e | ⟨i, hi, e | e⟩ | e)
    · exact .inl e
    · exact .inr (.inl (List.mem_flatten.2 ⟨[ixOf k (h + 2 + i) 1],
        List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_cons_self⟩,
        List.mem_singleton.2 e⟩))
    · exact .inr (.inl (List.mem_flatten.2 ⟨[ixOf k (h + 2 + i) 2],
        List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
          List.mem_cons_of_mem _ List.mem_cons_self⟩, List.mem_singleton.2 e⟩))
    · refine .inr (.inr ?_)
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_singleton]
      exact e

/-- **The numbers of a row, sorted in three**: the constant's; those of the variables above h; those
of the variables up to h that the row reaches. -/
theorem plan_mem {k h b n : ℕ} (hh : h ≤ k) : n ∈ (plan k h b).flatten ↔
    n = 2 * (k - 1) ∨ (∃ l t, h < l ∧ l ≤ k ∧ (t = 1 ∨ t = 2) ∧ n = ixOf k l t) ∨
      ∃ l t, 1 ≤ l ∧ l ≤ h ∧ (t = 1 ∨ t = 2) ∧ reaches h b l = true ∧ n = ixOf k l t := by
  unfold plan
  rw [List.cons_append, List.flatten_cons, List.flatten_append, List.mem_append, List.mem_append,
    mem_first, mem_second]
  by_cases hk : h < k
  · rw [if_pos hk, if_pos hk, mem_third]
    constructor
    · rintro ((rfl | ⟨i, hi, hr, rfl⟩) | ⟨i, hi, hr, rfl⟩ | rfl | ⟨i, hi, rfl | rfl⟩ | rfl)
      · exact .inr (.inl ⟨h + 1, 1, by omega, by omega, .inl rfl, rfl⟩)
      · exact .inr (.inr ⟨i + 1, 1, by omega, by omega, .inl rfl, hr, rfl⟩)
      · exact .inr (.inr ⟨i + 1, 2, by omega, by omega, .inr rfl, hr, rfl⟩)
      · exact .inr (.inl ⟨h + 1, 2, by omega, by omega, .inr rfl, rfl⟩)
      · exact .inr (.inl ⟨h + 2 + i, 1, by omega, by omega, .inl rfl, rfl⟩)
      · exact .inr (.inl ⟨h + 2 + i, 2, by omega, by omega, .inr rfl, rfl⟩)
      · exact .inl rfl
    · rintro (rfl | ⟨l, t, a1, a2, a3, rfl⟩ | ⟨l, t, a1, a2, a3, hr, rfl⟩)
      · exact .inr (.inr (.inr (.inr rfl)))
      · by_cases e : l = h + 1
        · subst e
          rcases a3 with rfl | rfl
          · exact .inl (.inl rfl)
          · exact .inr (.inr (.inl rfl))
        · obtain ⟨i, rfl⟩ : ∃ i, l = h + 2 + i := ⟨l - h - 2, by omega⟩
          rcases a3 with rfl | rfl
          · exact .inr (.inr (.inr (.inl ⟨i, by omega, .inl rfl⟩)))
          · exact .inr (.inr (.inr (.inl ⟨i, by omega, .inr rfl⟩)))
      · obtain ⟨i, rfl⟩ : ∃ i, l = i + 1 := ⟨l - 1, by omega⟩
        rcases a3 with rfl | rfl
        · exact .inl (.inr ⟨i, by omega, hr, rfl⟩)
        · exact .inr (.inl ⟨i, by omega, hr, rfl⟩)
  · rw [if_neg hk, if_neg hk]
    constructor
    · rintro ((rfl | ⟨i, hi, hr, rfl⟩) | ⟨i, hi, hr, rfl⟩ | hm)
      · exact .inl rfl
      · exact .inr (.inr ⟨i + 1, 1, by omega, by omega, .inl rfl, hr, rfl⟩)
      · exact .inr (.inr ⟨i + 1, 2, by omega, by omega, .inr rfl, hr, rfl⟩)
      · cases hm
    · rintro (rfl | ⟨l, t, a1, a2, a3, rfl⟩ | ⟨l, t, a1, a2, a3, hr, rfl⟩)
      · exact .inl (.inl rfl)
      · omega
      · obtain ⟨i, rfl⟩ : ∃ i, l = i + 1 := ⟨l - 1, by omega⟩
        rcases a3 with rfl | rfl
        · exact .inl (.inr ⟨i, by omega, hr, rfl⟩)
        · exact .inr (.inl ⟨i, by omega, hr, rfl⟩)

/-- Every number of a row lies below 2 k + 1. -/
theorem plan_below {k h b : ℕ} (hh : h ≤ k) : ∀ n ∈ (plan k h b).flatten, n < 2 * k + 1 := by
  intro n hn
  rcases (plan_mem hh).1 hn with rfl | ⟨l, t, a1, a2, a3, rfl⟩ | ⟨l, t, a1, a2, a3, -, rfl⟩
  · omega
  · exact ixOf_below (by omega) a2 a3
  · exact ixOf_below a1 (by omega) a3

/-- **THE PACKING's OWN WAY (1)**: a coefficient of a variable l up to h stands in just the rows
that reach l. -/
theorem plan_rows_low {k h b l t : ℕ} (hh : h ≤ k) (h1 : 1 ≤ l) (hl : l ≤ h) (ht : t = 1 ∨ t = 2) :
    ixOf k l t ∈ (plan k h b).flatten ↔ reaches h b l = true := by
  rw [plan_mem hh]
  constructor
  · rintro (e | ⟨l', t', a1, a2, a3, e⟩ | ⟨l', t', a1, a2, a3, hr, e⟩)
    · exact absurd e (ixOf_ne_const h1 ht)
    · have := (ixOf_inj h1 (by omega) ht (by omega) a2 a3 e).1
      omega
    · rw [(ixOf_inj h1 (by omega) ht a1 (by omega) a3 e).1]
      exact hr
  · exact fun hr => .inr (.inr ⟨l, t, h1, hl, ht, hr, rfl⟩)

/-- **THE PACKING's OWN WAY (2)**: the coefficients of the variables above h, and the constant's
coin, whose number is 2 (k - 1) (0 at k = 0), stand in every row. -/
theorem plan_rows_high {k h b : ℕ} (hh : h ≤ k) :
    (∀ l, h < l → l ≤ k → ∀ t, t = 1 ∨ t = 2 → ixOf k l t ∈ (plan k h b).flatten) ∧
      2 * (k - 1) ∈ (plan k h b).flatten :=
  ⟨fun l a1 a2 t a3 => (plan_mem hh).2 (.inr (.inl ⟨l, t, a1, a2, a3, rfl⟩)),
    (plan_mem hh).2 (.inl rfl)⟩

/-- The last row reaches every variable. -/
theorem reaches_last {h l : ℕ} (h1 : 1 ≤ l) : reaches h (2 ^ h - 1) l = true := by
  unfold reaches
  rw [List.all_eq_true]
  intro j hj
  have := List.mem_range.1 hj
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_true (by omega)

/-- Every number below 2 k + 1 stands in the last row. -/
theorem plan_last_all {k h : ℕ} (hh : h ≤ k) :
    ∀ n, n < 2 * k + 1 → n ∈ (plan k h (2 ^ h - 1)).flatten := by
  intro n hn
  rw [plan_mem hh]
  by_cases e0 : n = 2 * (k - 1)
  · exact .inl e0
  · obtain ⟨l, t, a1, a2, a3, rfl⟩ : ∃ l t, 1 ≤ l ∧ l ≤ k ∧ (t = 1 ∨ t = 2) ∧ n = ixOf k l t := by
      by_cases e1 : n < 2 * (k - 1)
      · refine ⟨n / 2 + 1, n % 2 + 1, by omega, by omega, by omega, ?_⟩
        unfold ixOf
        rw [if_pos (by omega)]
        omega
      · refine ⟨k, n - 2 * (k - 1), by omega, le_refl _, by omega, ?_⟩
        unfold ixOf
        rw [if_neg (by omega)]
        omega
    by_cases q : h < l
    · exact .inr (.inl ⟨l, t, q, a2, a3, rfl⟩)
    · exact .inr (.inr ⟨l, t, a1, by omega, a3, reaches_last a1, rfl⟩)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.foldl_filter
#print axioms ProofFile.Honest.K14.firstPlan_list
#print axioms ProofFile.Honest.K14.coinPlace_ix1
#print axioms ProofFile.Honest.K14.coinPlace_ix2
#print axioms ProofFile.Honest.K14.coinPlace_const
#print axioms ProofFile.Honest.K14.plan_place
#print axioms ProofFile.Honest.K14.plan_one_place
#print axioms ProofFile.Honest.K14.flatten_nodup_of_key
#print axioms ProofFile.Honest.K14.ix1_lt
#print axioms ProofFile.Honest.K14.firstPlan_nodup
#print axioms ProofFile.Honest.K14.plan_entry_nodup
#print axioms ProofFile.Honest.K14.plan_once
#print axioms ProofFile.Honest.K14.plan_places
#print axioms ProofFile.Honest.K14.ixOf_inj
#print axioms ProofFile.Honest.K14.ixOf_ne_const
#print axioms ProofFile.Honest.K14.ixOf_below
#print axioms ProofFile.Honest.K14.mem_first
#print axioms ProofFile.Honest.K14.mem_second
#print axioms ProofFile.Honest.K14.mem_third
#print axioms ProofFile.Honest.K14.plan_mem
#print axioms ProofFile.Honest.K14.plan_below
#print axioms ProofFile.Honest.K14.plan_rows_low
#print axioms ProofFile.Honest.K14.plan_rows_high
#print axioms ProofFile.Honest.K14.reaches_last
#print axioms ProofFile.Honest.K14.plan_last_all
