-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/BlkSetBits.lean: a structured vector with some of its variables set to the bits of a
number.

`Lkp.setBits v low high number` (OnBytes/Iop/Lkp.lean) sets the variables from low up to below high
of a vector of product form to the bits of a number: they leave their factors in the scalar, and the
other variables stay. This file says what the entries of the result read as, under any reading of
the program's elements (OnBytes/Iop/TensorLaws.lean): the entry at e is the entry of v at the index
that has the low bits of e, then the number's bits from low to below high, then the other bits of e.

Main definitions: `setW` (the product of the halves that are picked), `setIdx` (the index).
Main theorems.
 `setBits_fold`    what the loop has made after any number of variables.
 `setW_eq`         the product of the picked halves is the pairs' product at the index.
 `setIdx_kept`, `setIdx_set`, `setIdx_kept_add`, `setIdx_set_add`, `setIdx_closed`   the index, in
                   closed form.
 `vars_setBits`    the result has the variables that were not set.
 `entry_setBits`   the entries of the result.
 `entry_onBlock`   the same for the part of a vector on one block of planes.

Not claimed. Nothing for a vector with a written-out factor, which the loop drops.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Iop.TensorLaws
import OnBytes.Iop.Lkp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace OnBytes.Slice.Planes
open OnBytes.Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The product of the halves that are picked: of a variable from low to below high the half that
the number's bit picks, of any other variable the half that the next bit of e picks. s: the number
of the first pair's variable. -/
def setW (low high number : ℕ) : ℕ → List (E × E) → ℕ → K
  | _, [], _ => 1
  | s, p :: ps, e =>
    if low ≤ s ∧ s < high then
      ρ.val (if number.testBit s then p.2 else p.1) * setW low high number (s + 1) ps e
    else ρ.val (if e % 2 == 1 then p.2 else p.1) * setW low high number (s + 1) ps (e / 2)

/-- The program's loop, from the variable number s on. -/
def setLoop (low high number s : ℕ) (ps : List (E × E)) (part : Tensor) : Tensor :=
  ((List.range' s ps.length).zip ps).foldl (fun (part : Tensor) p =>
    if low ≤ p.1 && p.1 < high then
      part.scale (if number.testBit p.1 then p.2.2 else p.2.1)
    else part.push p.2.1 p.2.2) part

/-- One step of the loop. -/
theorem setLoop_cons (low high number s : ℕ) (p : E × E) (ps : List (E × E)) (part : Tensor) :
    setLoop low high number s (p :: ps) part =
      setLoop low high number (s + 1) ps
        (if low ≤ s && s < high then part.scale (if number.testBit s then p.2 else p.1)
          else part.push p.1 p.2) := by
  unfold setLoop
  rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.foldl_cons]

/-- A multiple of a vector has its written-out variables. -/
theorem denseVars_scale (v : Tensor) (y : E) : (v.scale y).denseVars = v.denseVars := by
  unfold Tensor.scale
  rfl

/-- A vector with one more pair has its written-out variables. -/
theorem denseVars_push (v : Tensor) (a b : E) : (v.push a b).denseVars = v.denseVars := by
  unfold Tensor.push
  rfl

/-- The scalar of a multiple. -/
theorem scalar_scale (v : Tensor) (y : E) : (v.scale y).scalar = mulE v.scalar y := by
  unfold Tensor.scale
  rfl

/-- A multiple of a vector has its pairs. -/
theorem pairs_scale (v : Tensor) (y : E) : (v.scale y).pairs = v.pairs := by
  unfold Tensor.scale
  rfl

/-- A vector with one more pair has its scalar. -/
theorem scalar_push (v : Tensor) (a b : E) : (v.push a b).scalar = v.scalar := by
  unfold Tensor.push
  rfl

/-- The pairs of a vector with one more pair. -/
theorem pairs_push (v : Tensor) (a b : E) : (v.push a b).pairs = v.pairs ++ [(a, b)] := by
  unfold Tensor.push
  rfl

/-- What the loop has made: the scalar times the pairs' product, at any index. -/
theorem setBits_fold (low high number : ℕ) : ∀ (ps : List (E × E)) (s : ℕ) (part : Tensor) (x : ℕ),
    part.denseVars = [] →
    (setLoop low high number s ps part).denseVars = [] ∧
      ρ.val (setLoop low high number s ps part).scalar *
          pairsVal ρ (setLoop low high number s ps part).pairs x =
        ρ.val part.scalar * pairsVal ρ part.pairs x *
          setW ρ low high number s ps (x / 2 ^ part.pairs.length)
  | [], _, part, x, h => ⟨h, (mul_one _).symm⟩
  | p :: ps, s, part, x, h => by
    rw [setLoop_cons]
    by_cases hc : low ≤ s ∧ s < high
    · have hb : (decide (low ≤ s) && decide (s < high)) = true := by
        rw [decide_eq_true hc.1, decide_eq_true hc.2]
        rfl
      rw [if_pos hb, setW, if_pos hc]
      generalize (if number.testBit s then p.2 else p.1) = y
      have ih := setBits_fold low high number ps (s + 1) (part.scale y) x
        ((denseVars_scale part y).trans h)
      refine ⟨ih.1, ?_⟩
      rw [ih.2, scalar_scale, pairs_scale, ρ.mul]
      ring
    · have hb : ¬ (decide (low ≤ s) && decide (s < high)) = true := by
        intro hh
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hh
        exact hc hh
      rw [if_neg hb]
      have ih := setBits_fold low high number ps (s + 1) (part.push p.1 p.2) x
        ((denseVars_push part p.1 p.2).trans h)
      refine ⟨ih.1, ?_⟩
      rw [ih.2, setW, if_neg hc, scalar_push, pairs_push, pairsVal_append, List.length_append,
        List.length_singleton, pow_succ, ← Nat.div_div_eq_div_mul, pairsVal, pairsVal, mul_one]
      ring

/-- The index whose bits are picked. k: the number of variables that are left. -/
def setIdx (low high number : ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, 0, _ => 0
  | s, k + 1, e =>
    if low ≤ s ∧ s < high then
      (if number.testBit s then 1 else 0) + 2 * setIdx low high number (s + 1) k e
    else e % 2 + 2 * setIdx low high number (s + 1) k (e / 2)

/-- The product of the picked halves is the pairs' product at the index. -/
theorem setW_eq (low high number : ℕ) : ∀ (ps : List (E × E)) (s e : ℕ),
    setW ρ low high number s ps e = pairsVal ρ ps (setIdx low high number s ps.length e)
  | [], _, _ => rfl
  | p :: ps, s, e => by
    rw [setW, List.length_cons, setIdx, pairsVal]
    by_cases hc : low ≤ s ∧ s < high
    · rw [if_pos hc, if_pos hc, setW_eq low high number ps]
      by_cases hb : number.testBit s = true
      · simp only [hb, if_true]
        rw [show (1 + 2 * setIdx low high number (s + 1) ps.length e) % 2 = 1 by omega,
          show (1 + 2 * setIdx low high number (s + 1) ps.length e) / 2 =
            setIdx low high number (s + 1) ps.length e by omega]
        rfl
      · simp only [hb, Bool.false_eq_true, if_false]
        rw [show (0 + 2 * setIdx low high number (s + 1) ps.length e) % 2 = 0 by omega,
          show (0 + 2 * setIdx low high number (s + 1) ps.length e) / 2 =
            setIdx low high number (s + 1) ps.length e by omega]
        rfl
    · rw [if_neg hc, if_neg hc, setW_eq low high number ps]
      rw [show (e % 2 + 2 * setIdx low high number (s + 1) ps.length (e / 2)) % 2 = e % 2 by omega,
        show (e % 2 + 2 * setIdx low high number (s + 1) ps.length (e / 2)) / 2 =
          setIdx low high number (s + 1) ps.length (e / 2) by omega]

/-- A stretch of variables that all stay. -/
theorem setIdx_kept (low high number : ℕ) : ∀ (k s e : ℕ),
    (∀ t, s ≤ t → t < s + k → ¬(low ≤ t ∧ t < high)) →
    setIdx low high number s k e = e % 2 ^ k
  | 0, _, _, _ => by simp [setIdx, Nat.mod_one]
  | k + 1, s, e, h => by
    rw [setIdx, if_neg (h s (le_refl s) (by omega)),
      setIdx_kept low high number k (s + 1) (e / 2) fun t h1 h2 => h t (by omega) (by omega),
      pow_succ', Nat.mod_mul]

/-- A stretch of variables that are all set. -/
theorem setIdx_set (low high number : ℕ) : ∀ (k s e : ℕ),
    (∀ t, s ≤ t → t < s + k → low ≤ t ∧ t < high) →
    setIdx low high number s k e = number / 2 ^ s % 2 ^ k
  | 0, _, _, _ => by simp [setIdx, Nat.mod_one]
  | k + 1, s, e, h => by
    rw [setIdx, if_pos (h s (le_refl s) (by omega)),
      setIdx_set low high number k (s + 1) e fun t h1 h2 => h t (by omega) (by omega),
      pow_succ' 2 k, Nat.mod_mul, Nat.div_div_eq_div_mul, ← pow_succ,
      Nat.testBit_eq_decide_div_mod_eq]
    by_cases hb : number / 2 ^ s % 2 = 1
    · rw [decide_eq_true hb, if_pos rfl, hb]
    · rw [decide_eq_false hb, if_neg (by decide)]
      omega

/-- Variables that all stay, then others. -/
theorem setIdx_kept_add (low high number b : ℕ) : ∀ (a s e : ℕ),
    (∀ t, s ≤ t → t < s + a → ¬(low ≤ t ∧ t < high)) →
    setIdx low high number s (a + b) e =
      e % 2 ^ a + 2 ^ a * setIdx low high number (s + a) b (e / 2 ^ a)
  | 0, s, e, _ => by simp [Nat.mod_one]
  | a + 1, s, e, h => by
    rw [show a + 1 + b = (a + b) + 1 by omega, setIdx, if_neg (h s (le_refl s) (by omega)),
      setIdx_kept_add low high number b a (s + 1) (e / 2) fun t h1 h2 => h t (by omega) (by omega),
      pow_succ' 2 a, Nat.mod_mul, Nat.div_div_eq_div_mul, show s + 1 + a = s + (a + 1) by omega]
    ring

/-- Variables that are all set, then others. -/
theorem setIdx_set_add (low high number b : ℕ) : ∀ (a s e : ℕ),
    (∀ t, s ≤ t → t < s + a → low ≤ t ∧ t < high) →
    setIdx low high number s (a + b) e =
      number / 2 ^ s % 2 ^ a + 2 ^ a * setIdx low high number (s + a) b e
  | 0, s, e, _ => by simp [Nat.mod_one]
  | a + 1, s, e, h => by
    rw [show a + 1 + b = (a + b) + 1 by omega, setIdx, if_pos (h s (le_refl s) (by omega)),
      setIdx_set_add low high number b a (s + 1) e fun t h1 h2 => h t (by omega) (by omega),
      pow_succ' 2 a, Nat.mod_mul, Nat.div_div_eq_div_mul, ← pow_succ,
      show s + 1 + a = s + (a + 1) by omega, Nat.testBit_eq_decide_div_mod_eq]
    by_cases hb : number / 2 ^ s % 2 = 1
    · rw [decide_eq_true hb, if_pos rfl, hb]
      ring
    · rw [decide_eq_false hb, if_neg (by decide), show number / 2 ^ s % 2 = 0 by omega]
      ring

/-- The index, in closed form. -/
theorem setIdx_closed (low high number N e : ℕ) (h1 : low ≤ high) (h2 : high ≤ N) :
    setIdx low high number 0 N e =
      e % 2 ^ low + 2 ^ low * (number / 2 ^ low % 2 ^ (high - low)) +
        2 ^ high * (e / 2 ^ low % 2 ^ (N - high)) := by
  have hN : N = low + ((high - low) + (N - high)) := by omega
  conv_lhs => rw [hN]
  rw [setIdx_kept_add low high number _ low 0 e (fun t _ h => by omega), Nat.zero_add,
    setIdx_set_add low high number _ (high - low) low _ (fun t ha hb => by omega),
    Nat.add_sub_cancel' h1,
    setIdx_kept low high number (N - high) high _ (fun t ha _ => by omega)]
  have hp : 2 ^ high = 2 ^ low * 2 ^ (high - low) := by rw [← pow_add, Nat.add_sub_cancel' h1]
  rw [hp]
  ring

/-! ## The number of variables that stay -/

/-- How many of the k variables from s on stay. -/
def keptN (low high : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | s, k + 1 => (if low ≤ s ∧ s < high then 0 else 1) + keptN low high (s + 1) k

/-- The loop adds a pair for each variable that stays. -/
theorem setLoop_length (low high number : ℕ) : ∀ (ps : List (E × E)) (s : ℕ) (part : Tensor),
    (setLoop low high number s ps part).pairs.length =
      part.pairs.length + keptN low high s ps.length
  | [], _, _ => rfl
  | p :: ps, s, part => by
    rw [setLoop_cons, setLoop_length low high number ps, List.length_cons, keptN]
    by_cases hc : low ≤ s ∧ s < high
    · have hb : (decide (low ≤ s) && decide (s < high)) = true := by
        rw [decide_eq_true hc.1, decide_eq_true hc.2]
        rfl
      rw [if_pos hb, if_pos hc, pairs_scale, Nat.zero_add]
    · have hb : ¬ (decide (low ≤ s) && decide (s < high)) = true := by
        intro hh
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hh
        exact hc hh
      rw [if_neg hb, if_neg hc, pairs_push, List.length_append, List.length_singleton]
      omega

/-- The variables that stay, in two stretches. -/
theorem keptN_add (low high b : ℕ) : ∀ (a s : ℕ),
    keptN low high s (a + b) = keptN low high s a + keptN low high (s + a) b
  | 0, s => by simp [keptN]
  | a + 1, s => by
    rw [show a + 1 + b = (a + b) + 1 by omega, keptN, keptN, keptN_add low high b a (s + 1),
      show s + 1 + a = s + (a + 1) by omega]
    omega

/-- A stretch of variables that all stay. -/
theorem keptN_kept (low high : ℕ) : ∀ (k s : ℕ),
    (∀ t, s ≤ t → t < s + k → ¬(low ≤ t ∧ t < high)) → keptN low high s k = k
  | 0, _, _ => rfl
  | k + 1, s, h => by
    rw [keptN, if_neg (h s (le_refl s) (by omega)),
      keptN_kept low high k (s + 1) fun t h1 h2 => h t (by omega) (by omega)]
    omega

/-- A stretch of variables that are all set. -/
theorem keptN_set (low high : ℕ) : ∀ (k s : ℕ),
    (∀ t, s ≤ t → t < s + k → low ≤ t ∧ t < high) → keptN low high s k = 0
  | 0, _, _ => rfl
  | k + 1, s, h => by
    rw [keptN, if_pos (h s (le_refl s) (by omega)),
      keptN_set low high k (s + 1) fun t h1 h2 => h t (by omega) (by omega)]

/-- The result has the variables that were not set. -/
theorem vars_setBits (v : Tensor) (low high number : ℕ) (h1 : low ≤ high)
    (h2 : high ≤ v.pairs.length) :
    (Lkp.setBits v low high number).vars = v.pairs.length - (high - low) := by
  have e : Lkp.setBits v low high number =
      setLoop low high number 0 v.pairs { scalar := v.scalar } := by
    unfold Lkp.setBits setLoop
    rw [List.range_eq_range']
  unfold Tensor.vars
  rw [e, setLoop_length]
  have hN : v.pairs.length = low + ((high - low) + (v.pairs.length - high)) := by omega
  conv_lhs => rw [hN]
  rw [keptN_add, keptN_add, keptN_kept low high low 0 (fun t _ h => by omega), Nat.zero_add,
    keptN_set low high (high - low) low (fun t ha hb => by omega), Nat.add_sub_cancel' h1,
    keptN_kept low high _ high (fun t ha _ => by omega)]
  show 0 + (low + (0 + (v.pairs.length - high))) = _
  omega

/-- The program's function is the loop from the first variable on. -/
theorem setBits_eq (v : Tensor) (low high number : ℕ) :
    Lkp.setBits v low high number = setLoop low high number 0 v.pairs { scalar := v.scalar } := by
  unfold Lkp.setBits setLoop
  rw [List.range_eq_range']

/-- The entries of a vector of product form with the variables from low to below high set to the
bits of a number. -/
theorem entry_setBits (v : Tensor) (low high number e : ℕ) (hv : v.denseVars = [])
    (h1 : low ≤ high) (h2 : high ≤ v.pairs.length) :
    ρ.val ((Lkp.setBits v low high number).entry e) =
      ρ.val (v.entry (e % 2 ^ low + 2 ^ low * (number / 2 ^ low % 2 ^ (high - low)) +
        2 ^ high * (e / 2 ^ low % 2 ^ (v.pairs.length - high)))) := by
  obtain ⟨f1, f2⟩ := setBits_fold ρ low high number v.pairs 0 { scalar := v.scalar } e rfl
  rw [setBits_eq, Tensor.entry_val, Tensor.entry_val, f2, setW_eq,
    setIdx_closed low high number _ _ h1 h2]
  unfold Tensor.denseVal
  rw [f1, hv]
  simp [pairsVal]

/-- The part of a vector of product form on one block of planes: at the entry with the plane
j' of the block and the row t it has the vector's entry at the plane first + j' and the row t. -/
theorem entry_onBlock (v : Tensor) (mu first lb j' t : ℕ) (hv : v.denseVars = []) (h1 : lb ≤ mu)
    (h2 : mu ≤ v.pairs.length) (ha : first % 2 ^ lb = 0) (hf : first < 2 ^ mu) (hj : j' < 2 ^ lb)
    (ht : t < 2 ^ (v.pairs.length - mu)) :
    ρ.val ((Lkp.onBlock v mu (first, lb)).entry (j' + 2 ^ lb * t)) =
      ρ.val (v.entry (first + j' + 2 ^ mu * t)) := by
  unfold Lkp.onBlock
  rw [entry_setBits ρ v lb mu first _ hv h1 h2]
  congr 2
  have hp : 2 ^ mu = 2 ^ lb * 2 ^ (mu - lb) := by rw [← pow_add, Nat.add_sub_cancel' h1]
  have e1 : (j' + 2 ^ lb * t) % 2 ^ lb = j' := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  have e2 : (j' + 2 ^ lb * t) / 2 ^ lb = t := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos lb), Nat.div_eq_of_lt hj, Nat.zero_add]
  have e3 : first / 2 ^ lb % 2 ^ (mu - lb) = first / 2 ^ lb :=
    Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [← hp]; exact hf))
  have e4 : 2 ^ lb * (first / 2 ^ lb) = first := by
    have := Nat.div_add_mod first (2 ^ lb)
    omega
  rw [e1, e2, e3, e4, Nat.mod_eq_of_lt ht]
  omega

end OnBytes.Slice.Planes
