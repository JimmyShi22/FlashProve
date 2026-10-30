-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkForm.lean: further laws on the entries of the program's structured vectors.

The program's verifier keeps a vector of coefficients as a short description: a tensor is a scalar
times, for each binary digit of the index, one half of a pair (OnBytes/Iop/Tensor.lean). What an
entry reads as under a reading of the program's elements in a commutative ring, and how scaling and
inserted variables change it, is in OnBytes/Iop/TensorLaws.lean. This file adds the two calls of
which the rows of a link are made, for tensors without a written-out factor.

 The cut at a length (`tensorBelow`, from variable 0 on). The program returns a list of tensors:
   the tensor itself or nothing where it sees that no entry other than 0 is concerned, else one
   tensor for each digit 1 of the length. `sum_tensorBelow`: the entries of the list's members at an
   index j add up to the tensor's entry if the low digits of j give a number below the length, and
   to 0 else.
 The placing of a vector on a table (`VectorLay.onTable`). `entry_onTable`: the entry at an index of
   the table is the tensor's entry at the number of the vector's entry that is there, and 0
   where the tensor does not reach.

Main definitions: `bitSum`, `hitsAt`, `cutAt`, `cutMask`.
Main theorems: `pairsVal_mask`, `sum_hitsAt`, `tensorBelow_plain`, `entry_cutAt`,
`sum_tensorBelow`, `tensorBelow_shape`, `entry_pad`, `pairsVal_rotate`, `onTable_plain_eq`,
`entry_onTable`.

Not claimed. Nothing on a tensor with a written-out factor, nor on a cut that begins above
variable 0.
-/
import OnBytes.Iop.TensorLaws
import OnBytes.Slice.ProgField

set_option autoImplicit false

namespace OnBytes.Slice
open OnBytes.Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-! ## Binary digits -/

/-- The lowest digit, as the program tests it. -/
theorem beq_one_eq_testBit (j : ℕ) : (j % 2 == 1) = j.testBit 0 := by
  rw [Nat.testBit_zero]
  by_cases h : j % 2 = 1
  · rw [decide_eq_true h, beq_iff_eq.2 h]
  · rw [decide_eq_false h]
    exact beq_eq_false_iff_ne.2 h

/-- The c + 1 lowest digits: the c lowest and digit c. -/
theorem mod_pow_succ_testBit (x c : ℕ) :
    x % 2 ^ (c + 1) = x % 2 ^ c + if x.testBit c then 2 ^ c else 0 := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ c) with h | h
  · rw [h, decide_eq_false (by omega), Nat.mul_zero]
    rfl
  · rw [h, decide_eq_true rfl, Nat.mul_one]
    rfl

/-- The sum of 2 ^ t over the t below c that pass a test. -/
def bitSum (g : ℕ → Bool) (c : ℕ) : ℕ :=
  (List.range c).foldl (fun s t => if g t then s + 2 ^ t else s) 0

/-- One more digit. -/
theorem bitSum_succ (g : ℕ → Bool) (c : ℕ) :
    bitSum g (c + 1) = if g c then bitSum g c + 2 ^ c else bitSum g c := by
  unfold bitSum
  rw [List.range_succ, List.foldl_append]
  rfl

/-- A number whose digits 1 all pass the test is at most the sum. -/
theorem mod_le_bitSum (g : ℕ → Bool) (j : ℕ) : ∀ c : ℕ,
    (∀ t, t < c → j.testBit t = true → g t = true) → j % 2 ^ c ≤ bitSum g c
  | 0, _ => by rw [pow_zero, Nat.mod_one]; exact Nat.zero_le _
  | c + 1, h => by
    have ih := mod_le_bitSum g j c fun t ht => h t (Nat.lt_succ_of_lt ht)
    rw [mod_pow_succ_testBit, bitSum_succ]
    by_cases hb : j.testBit c = true
    · rw [if_pos hb, if_pos (h c (Nat.lt_succ_self c) hb)]
      omega
    · rw [if_neg hb]
      split <;> omega

/-- A number that has the digit 1 wherever the test passes is at least the sum. -/
theorem bitSum_le_mod (g : ℕ → Bool) (j : ℕ) : ∀ c : ℕ,
    (∀ t, t < c → g t = true → j.testBit t = true) → bitSum g c ≤ j % 2 ^ c
  | 0, _ => Nat.zero_le _
  | c + 1, h => by
    have ih := bitSum_le_mod g j c fun t ht => h t (Nat.lt_succ_of_lt ht)
    rw [mod_pow_succ_testBit, bitSum_succ]
    by_cases hg : g c = true
    · rw [if_pos hg, if_pos (h c (Nat.lt_succ_self c) hg)]
      omega
    · rw [if_neg hg]
      omega

/-! ## The product of the pairs' halves -/

/-- One pair taken off, with the digit as a test. -/
theorem pairsVal_cons (p : E × E) (ps : List (E × E)) (j : ℕ) :
    pairsVal ρ (p :: ps) j = ρ.val (if j.testBit 0 then p.2 else p.1) * pairsVal ρ ps (j / 2) := by
  rw [← beq_one_eq_testBit]
  rfl

/-- The product is 0 if the half that some digit picks reads as 0. -/
theorem pairsVal_eq_zero : ∀ (ps : List (E × E)) (j t : ℕ), t < ps.length →
    ρ.val (if j.testBit t then (ps.getD t (zeroE, zeroE)).2 else (ps.getD t (zeroE, zeroE)).1) = 0 →
    pairsVal ρ ps j = 0
  | [], _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | p :: ps, j, 0, _, h0 => by
    rw [pairsVal_cons]
    rw [show (p :: ps).getD 0 (zeroE, zeroE) = p from rfl] at h0
    rw [h0, zero_mul]
  | p :: ps, j, t + 1, h, h0 => by
    rw [pairsVal_cons, pairsVal_eq_zero ps (j / 2) t (Nat.lt_of_succ_lt_succ h) (by
      rw [← Nat.testBit_succ]
      exact h0), mul_zero]

/-- Pairs of which some halves are struck out: m i b says whether the half b of pair number i
stays. The product is the old one if every digit picks a half that stays, else 0. -/
theorem pairsVal_mask : ∀ (ps : List (E × E)) (m : ℕ → Bool → Bool) (j : ℕ),
    pairsVal ρ (ps.mapIdx fun i p =>
        (if m i false then p.1 else zeroE, if m i true then p.2 else zeroE)) j =
      if (List.range ps.length).all fun i => m i (j.testBit i) then pairsVal ρ ps j else 0
  | [], _, _ => rfl
  | p :: ps, m, j => by
    rw [List.mapIdx_cons, pairsVal_cons, pairsVal_cons,
      pairsVal_mask ps (fun i => m (i + 1)) (j / 2), List.length_cons, List.range_succ_eq_map,
      List.all_cons, List.all_map]
    have hs : (fun i => m (i + 1) ((j / 2).testBit i)) =
        ((fun i => m i (j.testBit i)) ∘ Nat.succ) := by
      funext i
      show _ = m (i + 1) (j.testBit (i + 1))
      rw [Nat.testBit_succ]
    rw [hs]
    cases hb : j.testBit 0 <;> cases hm : m 0 (j.testBit 0) <;> rw [hb] at hm <;>
      simp [hm, ρ.zero]

/-! ## A vector cut off at a length -/

/-- Digit q of j is 0, and the digits of j above q and below c are those of len. If digit q of len
is 1, this says that q is the highest of the c lowest digits in which j and len differ, and that j
is the smaller one there: j is below len for the reason q. -/
def hitsAt (c len j q : ℕ) : Bool :=
  !j.testBit q && (List.range c).all fun i => decide (i ≤ q) || (j.testBit i == len.testBit i)

/-- One more digit above q: it has to agree too. -/
theorem hitsAt_succ_of_lt (c len j q : ℕ) (h : q < c) :
    hitsAt (c + 1) len j q = (hitsAt c len j q && (j.testBit c == len.testBit c)) := by
  unfold hitsAt
  rw [List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
    decide_eq_false (by omega), Bool.false_or, Bool.and_assoc]

/-- At the highest digit nothing is asked but that j has a 0 there. -/
theorem hitsAt_self (c len j : ℕ) : hitsAt (c + 1) len j c = !j.testBit c := by
  unfold hitsAt
  rw [List.all_eq_true.2 fun i hi => by
    rw [decide_eq_true (Nat.le_of_lt_succ (List.mem_range.1 hi)), Bool.true_or], Bool.and_true]

/-- Of the digits 1 of len, exactly one is such a reason if j is below len in the c lowest digits,
and none else. -/
theorem sum_hitsAt (len j : ℕ) : ∀ c : ℕ,
    (((List.range c).filter fun q => len.testBit q).map fun q =>
      if hitsAt c len j q then (1 : K) else 0).sum = if j % 2 ^ c < len % 2 ^ c then 1 else 0
  | 0 => by simp [Nat.mod_one]
  | c + 1 => by
    have ih := sum_hitsAt len j c
    have h1 : (((List.range c).filter fun q => len.testBit q).map fun q =>
        if hitsAt (c + 1) len j q then (1 : K) else 0) =
        ((List.range c).filter fun q => len.testBit q).map fun q =>
          if (j.testBit c == len.testBit c) then (if hitsAt c len j q then (1 : K) else 0)
          else 0 :=
      List.map_congr_left fun q hq => by
        rw [hitsAt_succ_of_lt c len j q (List.mem_range.1 (List.mem_filter.1 hq).1)]
        cases hitsAt c len j q <;> cases (j.testBit c == len.testBit c) <;> rfl
    have h2 : (([c].filter fun q => len.testBit q).map fun q =>
        if hitsAt (c + 1) len j q then (1 : K) else 0).sum =
        if len.testBit c then (if j.testBit c then 0 else 1) else 0 := by
      cases hlb : len.testBit c
      · rw [List.filter_cons_of_neg (by rw [hlb]; exact Bool.false_ne_true)]
        rfl
      · rw [List.filter_cons_of_pos hlb, List.filter_nil, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, add_zero, hitsAt_self]
        cases j.testBit c <;> rfl
    have hj := Nat.mod_lt j (Nat.two_pow_pos c)
    have hl := Nat.mod_lt len (Nat.two_pow_pos c)
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, h1, h2,
      mod_pow_succ_testBit j c, mod_pow_succ_testBit len c]
    cases hjb : j.testBit c <;> cases hlb : len.testBit c
    · simp [ih]
    · have e : j % 2 ^ c < len % 2 ^ c + 2 ^ c := by omega
      simp [e]
    · have e : ¬ (j % 2 ^ c + 2 ^ c < len % 2 ^ c) := by omega
      simp [e]
    · simp [ih]

/-- A tensor of which all entries are struck out but those that are below len for the reason q. -/
def cutAt (v : Tensor) (count len q : ℕ) : Tensor :=
  { v with
    pairs := v.pairs.mapIdx fun i p =>
      if i < q || count ≤ i then p
      else if i == q then (p.1, zeroE)
      else if len.testBit i then (zeroE, p.2)
      else (p.1, zeroE) }

/-- The program's cut of a tensor without a written-out factor, from variable 0 on. -/
theorem tensorBelow_plain (v : Tensor) (hv : v.denseVars = []) (count len : ℕ) :
    tensorBelow v 0 count len =
      if v.vars < count || 2 ^ count < len then none
      else if len == 2 ^ count then some [v]
      else if bitSum (fun t => !isZeroE (v.pairs.getD t (zeroE, zeroE)).2) count < len then some [v]
      else if len ≤ bitSum (fun t => isZeroE (v.pairs.getD t (zeroE, zeroE)).1) count then some []
      else some (((List.range count).filter fun q => len.testBit q).map fun q =>
        cutAt v count len q) := by
  unfold tensorBelow bitSum cutAt
  simp [hv]

/-- Which halves the cut for the reason q leaves: all of the pairs below q and from count on, the
half 0 of pair q, and of a pair between them the half that len's digit names. -/
def cutMask (count len q i : ℕ) (b : Bool) : Bool :=
  decide (i < q) || decide (count ≤ i) || (if i == q then !b else (b == len.testBit i))

/-- The pairs of such a cut, as pairs of which some halves are struck out. -/
theorem cutAt_pairs (v : Tensor) (count len q : ℕ) :
    (cutAt v count len q).pairs = v.pairs.mapIdx fun i p =>
      (if cutMask count len q i false then p.1 else zeroE,
        if cutMask count len q i true then p.2 else zeroE) := by
  unfold cutAt cutMask
  refine congrArg (fun f => v.pairs.mapIdx f) (funext fun i => funext fun p => ?_)
  by_cases h1 : i < q
  · simp [h1]
  · by_cases h2 : count ≤ i
    · simp [h2]
    · by_cases h3 : i = q
      · subst h3
        simp [h2]
      · cases len.testBit i <;> simp [h1, h2, h3]

/-- Every digit of j picks a half that the cut leaves exactly if j is below len for the reason
q. -/
theorem all_cutMask (n count len j q : ℕ) (hq : q < count) (hn : count ≤ n) :
    ((List.range n).all fun i => cutMask count len q i (j.testBit i)) = hitsAt count len j q := by
  rw [Bool.eq_iff_iff]
  unfold hitsAt cutMask
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq]
  constructor
  · intro H
    refine ⟨?_, fun i hi => ?_⟩
    · rcases H q (by omega) with (h | h) | h
      · omega
      · omega
      · rwa [if_pos (beq_self_eq_true q)] at h
    · by_cases h1 : i ≤ q
      · exact Or.inl h1
      · rcases H i (by omega) with (h | h) | h
        · omega
        · omega
        · rw [if_neg (by simp; omega)] at h
          exact Or.inr h
  · rintro ⟨H1, H2⟩ i _
    by_cases h1 : i < q
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : count ≤ i
      · exact Or.inl (Or.inr h2)
      · refine Or.inr ?_
        by_cases h3 : i = q
        · rw [if_pos (by simp [h3]), h3]
          exact H1
        · rw [if_neg (by simp [h3])]
          rcases H2 i (by omega) with h | h
          · omega
          · exact h

/-- An entry of the cut for the reason q. -/
theorem entry_cutAt (v : Tensor) (count len q j : ℕ) (hq : q < count) (hc : count ≤ v.vars) :
    ρ.val ((cutAt v count len q).entry j) =
      if hitsAt count len j q then ρ.val (v.entry j) else 0 := by
  rw [Tensor.entry_val, Tensor.entry_val, cutAt_pairs, pairsVal_mask,
    all_cutMask v.pairs.length count len j q hq hc]
  have hd : (cutAt v count len q).denseVal ρ j = v.denseVal ρ j := rfl
  have hs : (cutAt v count len q).scalar = v.scalar := rfl
  rw [hd, hs]
  cases hitsAt count len j q
  · simp
  · simp

/-- The program's cut of a vector at a length. For a tensor without a written-out factor, cut
from variable 0 on: the sum of the parts' entries at j is the tensor's entry if the count lowest
digits of j give a number below len, else 0. -/
theorem sum_tensorBelow (v : Tensor) (hv : v.denseVars = []) (count len : ℕ) (l : List Tensor)
    (h : tensorBelow v 0 count len = some l) (j : ℕ) :
    (l.map fun w => ρ.val (w.entry j)).sum =
      if j % 2 ^ count < len then ρ.val (v.entry j) else 0 := by
  have hjc := Nat.mod_lt j (Nat.two_pow_pos count)
  have hval : ρ.val (v.entry j) = ρ.val v.scalar * pairsVal ρ v.pairs j := by
    rw [Tensor.entry_val]
    unfold Tensor.denseVal
    rw [hv]
    exact mul_one _
  rw [tensorBelow_plain v hv] at h
  by_cases h1 : (decide (v.vars < count) || decide (2 ^ count < len)) = true
  · rw [if_pos h1] at h
    cases h
  rw [if_neg h1] at h
  have h1' : count ≤ v.vars ∧ len ≤ 2 ^ count := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at h1
    exact h1
  by_cases h2 : (len == 2 ^ count) = true
  · rw [if_pos h2] at h
    obtain rfl := Option.some.inj h
    rw [if_pos (by rw [beq_iff_eq.1 h2]; exact hjc)]
    simp
  rw [if_neg h2] at h
  have hlt : len < 2 ^ count := lt_of_le_of_ne h1'.2 fun e => h2 (beq_iff_eq.2 e)
  by_cases h3 : bitSum (fun t => !isZeroE (v.pairs.getD t (zeroE, zeroE)).2) count < len
  · -- no entry other than 0 is at or after the length
    rw [if_pos h3] at h
    obtain rfl := Option.some.inj h
    by_cases h4 : j % 2 ^ count < len
    · rw [if_pos h4]
      simp
    · rw [if_neg h4]
      have hex : ¬ ∀ t, t < count → j.testBit t = true →
          (!isZeroE (v.pairs.getD t (zeroE, zeroE)).2) = true := fun H =>
        h4 (lt_of_le_of_lt (mod_le_bitSum _ j count H) h3)
      simp only [not_forall] at hex
      obtain ⟨t, ht, hb, hz⟩ := hex
      have hz' : isZeroE (v.pairs.getD t (zeroE, zeroE)).2 = true := by
        cases hh : isZeroE (v.pairs.getD t (zeroE, zeroE)).2
        · rw [hh] at hz
          exact absurd rfl hz
        · rfl
      have h0 : pairsVal ρ v.pairs j = 0 :=
        pairsVal_eq_zero ρ v.pairs j t (lt_of_lt_of_le ht h1'.1) (by
          rw [if_pos hb, (isZeroE_eq _).1 hz']
          exact ρ.zero)
      simp [hval, h0]
  rw [if_neg h3] at h
  by_cases h5 : len ≤ bitSum (fun t => isZeroE (v.pairs.getD t (zeroE, zeroE)).1) count
  · -- no entry other than 0 is before the length
    rw [if_pos h5] at h
    obtain rfl := Option.some.inj h
    by_cases h4 : j % 2 ^ count < len
    · rw [if_pos h4]
      have hex : ¬ ∀ t, t < count → isZeroE (v.pairs.getD t (zeroE, zeroE)).1 = true →
          j.testBit t = true := fun H =>
        absurd (lt_of_lt_of_le h4 (le_trans h5 (bitSum_le_mod _ j count H))) (lt_irrefl _)
      simp only [not_forall] at hex
      obtain ⟨t, ht, hz, hb⟩ := hex
      have h0 : pairsVal ρ v.pairs j = 0 :=
        pairsVal_eq_zero ρ v.pairs j t (lt_of_lt_of_le ht h1'.1) (by
          rw [if_neg hb, (isZeroE_eq _).1 hz]
          exact ρ.zero)
      simp [hval, h0]
    · rw [if_neg h4]
      rfl
  rw [if_neg h5] at h
  obtain rfl := Option.some.inj h
  -- one part for each digit 1 of the length
  rw [List.map_map]
  have e1 : (((List.range count).filter fun q => len.testBit q).map
      ((fun w => ρ.val (w.entry j)) ∘ fun q => cutAt v count len q)) =
      ((List.range count).filter fun q => len.testBit q).map fun q =>
        (if hitsAt count len j q then (1 : K) else 0) * ρ.val (v.entry j) :=
    List.map_congr_left fun q hq => by
      show ρ.val ((cutAt v count len q).entry j) = _
      rw [entry_cutAt ρ v count len q j (List.mem_range.1 (List.mem_filter.1 hq).1) h1'.1]
      cases hitsAt count len j q <;> simp
  rw [e1, List.sum_map_mul_right, sum_hitsAt, Nat.mod_eq_of_lt hlt]
  by_cases h4 : j % 2 ^ count < len
  · rw [if_pos h4, if_pos h4, one_mul]
  · rw [if_neg h4, if_neg h4, zero_mul]

/-- The parts of a cut have the tensor's number of variables and no written-out factor. -/
theorem tensorBelow_shape (v : Tensor) (hv : v.denseVars = []) (count len : ℕ) (l : List Tensor)
    (h : tensorBelow v 0 count len = some l) :
    ∀ w ∈ l, w.vars = v.vars ∧ w.denseVars = [] := by
  rw [tensorBelow_plain v hv] at h
  intro w hw
  split at h
  · cases h
  · split at h
    · obtain rfl := Option.some.inj h
      obtain rfl := List.mem_singleton.1 hw
      exact ⟨rfl, hv⟩
    · split at h
      · obtain rfl := Option.some.inj h
        obtain rfl := List.mem_singleton.1 hw
        exact ⟨rfl, hv⟩
      · split at h
        · obtain rfl := Option.some.inj h
          cases hw
        · obtain rfl := Option.some.inj h
          obtain ⟨q, -, rfl⟩ := List.mem_map.1 hw
          exact ⟨by show (v.pairs.mapIdx _).length = _; rw [List.length_mapIdx]; rfl, hv⟩

/-! ## A vector placed on a table -/

/-- An entry of a tensor without a written-out factor. -/
theorem entry_plain (v : Tensor) (hv : v.denseVars = []) (j : ℕ) :
    ρ.val (v.entry j) = ρ.val v.scalar * pairsVal ρ v.pairs j := by
  rw [Tensor.entry_val]
  unfold Tensor.denseVal
  rw [hv]
  exact mul_one _

/-- Such an entry depends on the digits of the index below the number of variables alone. -/
theorem entry_mod (v : Tensor) (hv : v.denseVars = []) (j : ℕ) :
    ρ.val (v.entry (j % 2 ^ v.vars)) = ρ.val (v.entry j) := by
  rw [entry_plain ρ v hv, entry_plain ρ v hv]
  exact congrArg _ (pairsVal_mod ρ v.pairs j)

/-- The pairs of a tensor with inserted variables. -/
theorem insertChoice_pairs (v : Tensor) (pos count value : ℕ) :
    (v.insertChoice pos count value).pairs =
      v.pairs.take pos ++ choicePairs count value ++ v.pairs.drop pos := rfl

/-- Inserted variables bring no written-out factor. -/
theorem insertChoice_plain (v : Tensor) (hv : v.denseVars = []) (pos count value : ℕ) :
    (v.insertChoice pos count value).denseVars = [] := by
  show v.denseVars.map _ = []
  rw [hv]
  rfl

/-- A tensor on the low digits of an index of n digits, taken as 0 where a higher digit is 1. -/
theorem entry_pad (v : Tensor) (hv : v.denseVars = []) (n J : ℕ) (hn : v.vars ≤ n)
    (hJ : J < 2 ^ n) :
    ρ.val ((v.insertChoice v.vars (n - v.vars) 0).entry J) =
      if J < 2 ^ v.vars then ρ.val (v.entry J) else 0 := by
  rw [Tensor.entry_insertChoice ρ v v.vars (n - v.vars) 0 J (Nat.le_refl _),
    ← entry_mod ρ v hv (unshift v.vars (n - v.vars) J), unshift_mod, entry_mod ρ v hv,
    Nat.zero_mod]
  have hlt : J / 2 ^ v.vars < 2 ^ (n - v.vars) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.sub_add_cancel hn]
    exact hJ
  rw [Nat.mod_eq_of_lt hlt]
  by_cases h : J < 2 ^ v.vars
  · rw [if_pos h, if_pos (Nat.div_eq_of_lt h), one_mul]
  · rw [if_neg h, if_neg, zero_mul]
    intro h0
    exact h ((Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).1 h0)

/-- Pairs of which the first pb are moved after the others: the digits of the index move
likewise. -/
theorem pairsVal_rotate (ps : List (E × E)) (rb pb i : ℕ) (hl : ps.length = rb + pb)
    (hi : i < 2 ^ (rb + pb)) :
    pairsVal ρ (ps.drop pb ++ ps.take pb) i =
      pairsVal ρ ps (i / 2 ^ rb + (i % 2 ^ rb) * 2 ^ pb) := by
  have hd : (ps.drop pb).length = rb := by rw [List.length_drop, hl, Nat.add_sub_cancel]
  have ht : (ps.take pb).length = pb := by
    rw [List.length_take, hl]
    omega
  have hq : i / 2 ^ rb < 2 ^ pb := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.add_comm]
    exact hi
  have e1 : (i / 2 ^ rb + (i % 2 ^ rb) * 2 ^ pb) % 2 ^ pb = i / 2 ^ rb := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]
  have e2 : (i / 2 ^ rb + (i % 2 ^ rb) * 2 ^ pb) / 2 ^ pb = i % 2 ^ rb := by
    rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hq, Nat.zero_add]
  have a1 := pairsVal_mod ρ (ps.take pb) (i / 2 ^ rb + (i % 2 ^ rb) * 2 ^ pb)
  have a2 := pairsVal_mod ρ (ps.drop pb) i
  rw [ht, e1] at a1
  rw [hd] at a2
  conv_rhs => rw [← List.take_append_drop pb ps]
  rw [pairsVal_append, pairsVal_append, hd, ht, e2, ← a1, a2, mul_comm]

/-- How the program places a tensor without a written-out factor on a table: variables that pick 0
are put on top and, if a row holds consecutive entries, the variables of a place are moved after
those of a row. -/
theorem onTable_plain_eq (l : VectorLay) (v : Tensor) (hv : v.denseVars = []) :
    (l.onTable v).scalar = v.scalar ∧ (l.onTable v).denseVars = [] ∧
      (l.onTable v).pairs =
        if l.rowsHigh then
          (v.insertChoice v.vars (l.bits - v.vars) 0).pairs.drop l.placeBits ++
            (v.insertChoice v.vars (l.bits - v.vars) 0).pairs.take l.placeBits
        else (v.insertChoice v.vars (l.bits - v.vars) 0).pairs := by
  have hw := insertChoice_plain v hv v.vars (l.bits - v.vars) 0
  unfold VectorLay.onTable
  by_cases hh : l.rowsHigh = true
  · simp only [hh, if_true]
    refine ⟨rfl, ?_, rfl⟩
    show (v.insertChoice v.vars (l.bits - v.vars) 0).denseVars.map _ = []
    rw [hw]
    rfl
  · simp only [hh, Bool.false_eq_true, if_false]
    exact ⟨rfl, hw, trivial⟩

/-- The number of the vector's entry that is at an index of a table. -/
theorem entryAt_eq (l : VectorLay) (i : ℕ) :
    l.entryAt i =
      if l.rowsHigh then i / 2 ^ l.rowBits + (i % 2 ^ l.rowBits) * 2 ^ l.placeBits else i := rfl

/-- A vector's tensor, placed on a table. The entry at an index of the table is the tensor's entry
at the number of the vector's entry that is there, and 0 where the tensor does not reach. -/
theorem entry_onTable (l : VectorLay) (v : Tensor) (hv : v.denseVars = []) (hb : v.vars ≤ l.bits)
    (i : ℕ) (hi : i < 2 ^ l.bits) :
    ρ.val ((l.onTable v).entry i) =
      if l.entryAt i < 2 ^ v.vars then ρ.val (v.entry (l.entryAt i)) else 0 := by
  have hw := insertChoice_plain v hv v.vars (l.bits - v.vars) 0
  obtain ⟨hs, hd, hp⟩ := onTable_plain_eq l v hv
  rw [entry_plain ρ _ hd, hs, hp, entryAt_eq]
  by_cases hh : l.rowsHigh = true
  · rw [if_pos hh, if_pos hh]
    have hlen : (v.insertChoice v.vars (l.bits - v.vars) 0).pairs.length =
        l.rowBits + l.placeBits := by
      rw [insertChoice_pairs, List.length_append, List.length_append, choicePairs_length,
        List.length_take, List.length_drop]
      have h1 : v.vars = v.pairs.length := rfl
      have h2 : l.bits = l.rowBits + l.placeBits := rfl
      omega
    have hJ : i / 2 ^ l.rowBits + (i % 2 ^ l.rowBits) * 2 ^ l.placeBits < 2 ^ l.bits := by
      have hq : i / 2 ^ l.rowBits < 2 ^ l.placeBits := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.add_comm]
        exact hi
      have hr := Nat.mod_lt i (Nat.two_pow_pos l.rowBits)
      calc i / 2 ^ l.rowBits + (i % 2 ^ l.rowBits) * 2 ^ l.placeBits
          < 2 ^ l.placeBits + (i % 2 ^ l.rowBits) * 2 ^ l.placeBits := Nat.add_lt_add_right hq _
        _ = (i % 2 ^ l.rowBits + 1) * 2 ^ l.placeBits := by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
        _ ≤ 2 ^ l.rowBits * 2 ^ l.placeBits := Nat.mul_le_mul_right _ hr
        _ = 2 ^ l.bits := (Nat.pow_add 2 _ _).symm
    rw [← entry_pad ρ v hv l.bits _ hb hJ, entry_plain ρ _ hw,
      pairsVal_rotate ρ _ l.rowBits l.placeBits i hlen hi]
    rfl
  · rw [if_neg hh, if_neg hh, ← entry_pad ρ v hv l.bits i hb hi, entry_plain ρ _ hw]
    rfl

end OnBytes.Slice

#print axioms OnBytes.Slice.mod_le_bitSum
#print axioms OnBytes.Slice.bitSum_le_mod
#print axioms OnBytes.Slice.pairsVal_eq_zero
#print axioms OnBytes.Slice.pairsVal_mask
#print axioms OnBytes.Slice.sum_hitsAt
#print axioms OnBytes.Slice.tensorBelow_plain
#print axioms OnBytes.Slice.all_cutMask
#print axioms OnBytes.Slice.entry_cutAt
#print axioms OnBytes.Slice.sum_tensorBelow
#print axioms OnBytes.Slice.tensorBelow_shape
#print axioms OnBytes.Slice.entry_mod
#print axioms OnBytes.Slice.entry_pad
#print axioms OnBytes.Slice.pairsVal_rotate
#print axioms OnBytes.Slice.onTable_plain_eq
#print axioms OnBytes.Slice.entry_onTable
#print axioms OnBytes.Slice.beq_one_eq_testBit
#print axioms OnBytes.Slice.mod_pow_succ_testBit
#print axioms OnBytes.Slice.bitSum_succ
#print axioms OnBytes.Slice.pairsVal_cons
#print axioms OnBytes.Slice.hitsAt_succ_of_lt
#print axioms OnBytes.Slice.hitsAt_self
#print axioms OnBytes.Slice.cutAt_pairs
#print axioms OnBytes.Slice.entry_plain
#print axioms OnBytes.Slice.insertChoice_pairs
#print axioms OnBytes.Slice.insertChoice_plain
#print axioms OnBytes.Slice.entryAt_eq
