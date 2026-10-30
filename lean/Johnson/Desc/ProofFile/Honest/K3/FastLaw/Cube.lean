-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/FastLaw/Cube.lean: numbers and sums for the theorems on the folded
tables (Honest/K3/JobsFast.lean). Definitions and theorems on natural numbers, on lists of Boolean
marks and on sums over a cube, over any field.

Terms. Honest/K3/GLOSSARY.md. In this file a list of marks is a list of Booleans, one for each bit
of a table's numbers: true says that the bit is still free, false that it is bound. (This is none of
the glossary's senses of "mark".) The long cube is the numbers below
2 ^ m, m the number of all bits; the short cube is the numbers below 2 ^ n, n the number of free
bits.

What is shown, by the file's sections.
  1. `at0_zero`, `at0_succ`: the number of the i-th entry whose bit at a position is 0 (`at0`,
     JobsFast.lean), by halving.
  2. Definitions on a list of marks. `nM`: how many bits are free. `posM`: a free bit's position
     among the free ones. `spreadM`: a short number laid out over the free bits. `idx`: the free
     bits' numbers. `compact`: a list cut down to the free bits. `wts`: a list with 0 at the others.
  3. `take_out`: one free bit taken out: the counts; the bound on numbers; and the two entries that
     `bindAt` (JobsFast.lean) joins are those that `setBit` (LookDefs.lean) names.
  4. `idx_length`, `idx_lt`, `idx_all`, `idx_filter`, `idx_pos`, `idx_map`: the list of free bits
     under the operations of `Cube` (JobsFast.lean); with them facts on `compact` and `wts`.
  5. `sum_spread`: the sum over the long cube under weights with zeros is the sum over the short
     one.
  6. `maskN`, with `maskN_length`, `maskN_free`, `wts_maskN`, `maskN_next`: the marks behind l
     rounds of an order.

Hypotheses that remain.
  `O`, `hl`: (in `maskN_next`) o is an order of m bits (`Ord o m`); l < m. `he`: (in
    `setBit_succ_add`) e < 2.
  Without a name, in front of arrows: in `take_out`: bit b is free; in `idx_lt`: b is one of the
    free bits; in `idx_map`, `compact_length`, `wts_length` and `sum_spread`: the list of marks is
    as long as the other list; in `maskN_free`: c < m, and c is none of the order's first l bits.

Users. Honest/K3/FastLaw/Round.lean imports this file. The specification
(Johnson/HonestTrace/LookDefs.lean) keeps a table with some bits bound as a function on all numbers
below 2 ^ m that no longer reads the bound bits (`foldN`), and it sums under weights that are 0 at
the bound coordinates (`wtN`). The folded tables are shorter: the bound bits are taken out of an
entry's number. This file says how a short number lies in the long one.

Limits. No statement of this file speaks of the program's elements, of an array or of a lookup:
Round.lean does.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.JobsFast
import Johnson.HonestTrace.LookCube

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.FastLaw
open Finset TwV
open OnBytes.HonestTrace.Look (setBit wtN sum_cons Ord)
open ProofFile.Honest.K3.Fast (at0)

/-! ## 1 at0, by halving -/

theorem at0_zero (i : ℕ) : at0 0 i = 2 * i := by
  unfold at0
  simp [Nat.mod_one]
  omega

theorem at0_succ (p i : ℕ) : at0 (p + 1) i = 2 * at0 p (i / 2) + i % 2 := by
  unfold at0
  have e1 : i / 2 ^ (p + 1) = i / 2 / 2 ^ p := by
    rw [pow_succ', Nat.div_div_eq_div_mul]
  have e2 : i % 2 ^ (p + 1) = i % 2 + 2 * (i / 2 % 2 ^ p) := by
    rw [pow_succ', Nat.mod_mul]
  rw [e1, e2, pow_succ' 2 (p + 1)]
  ring

/-! ## 2 Marks -/

/-- How many bits are free. -/
def nM : List Bool → ℕ
  | [] => 0
  | true :: M => nM M + 1
  | false :: M => nM M

/-- How many free bits lie below bit b. -/
def posM : List Bool → ℕ → ℕ
  | [], _ => 0
  | _ :: _, 0 => 0
  | true :: M, b + 1 => posM M b + 1
  | false :: M, b + 1 => posM M b

/-- A short number laid out over the free bits; the other bits are 0. -/
def spreadM : List Bool → ℕ → ℕ
  | [], _ => 0
  | true :: M, i => 2 * spreadM M (i / 2) + i % 2
  | false :: M, i => 2 * spreadM M i

/-- The free bits' numbers, rising. -/
def idx : List Bool → List ℕ
  | [] => []
  | true :: M => 0 :: (idx M).map (· + 1)
  | false :: M => (idx M).map (· + 1)

section
variable {K : Type} [Field K]

/-- A list cut down to the free bits' entries. -/
def compact : List Bool → List K → List K
  | true :: M, w :: W => w :: compact M W
  | false :: M, _ :: W => compact M W
  | _, _ => []

/-- A list with 0 at the bits that are not free. -/
def wts : List Bool → List K → List K
  | true :: M, w :: W => w :: wts M W
  | false :: M, _ :: W => 0 :: wts M W
  | _, _ => []

end

/-! ## 3 One free bit taken out -/

theorem setBit_zero_even (v : Bool) (y : ℕ) : setBit 0 v (2 * y) = 2 * y + v.toNat := by
  show 2 * (2 * y / 2) + v.toNat = _
  omega

theorem setBit_succ_even (c : ℕ) (v : Bool) (y : ℕ) :
    setBit (c + 1) v (2 * y) = 2 * setBit c v y := by
  show 2 * setBit c v (2 * y / 2) + 2 * y % 2 = _
  have e : 2 * y / 2 = y := by omega
  rw [e]
  omega

theorem setBit_succ_add (c : ℕ) (v : Bool) (y e : ℕ) (he : e < 2) :
    setBit (c + 1) v (2 * y + e) = 2 * setBit c v y + e := by
  show 2 * setBit c v ((2 * y + e) / 2) + (2 * y + e) % 2 = _
  have e1 : (2 * y + e) / 2 = y := by omega
  rw [e1]
  omega

/-- **One free bit b taken out of the marks M.** With p its position among the free bits: one bit
fewer is free; for a short number i of the marks behind, the two numbers at0 p i and at0 p i + 2 ^ p
are numbers of the marks in front, and laid out they are i laid out, with bit b put to 0 and to
1. -/
theorem take_out : ∀ (b : ℕ) (M : List Bool), M.getD b false = true →
    nM M = nM (M.set b false) + 1 ∧
    (∀ i, i < 2 ^ nM (M.set b false) → at0 (posM M b) i + 2 ^ posM M b < 2 ^ nM M) ∧
    (∀ i, spreadM M (at0 (posM M b) i) = setBit b false (spreadM (M.set b false) i)) ∧
    (∀ i, spreadM M (at0 (posM M b) i + 2 ^ posM M b) =
      setBit b true (spreadM (M.set b false) i))
  | _, [], h => by simp at h
  | 0, false :: M, h => by simp at h
  | 0, true :: M, _ => by
    refine ⟨rfl, fun i hi => ?_, fun i => ?_, fun i => ?_⟩
    · show at0 0 i + 2 ^ 0 < 2 ^ (nM M + 1)
      have hi' : i < 2 ^ nM M := hi
      rw [at0_zero, pow_succ]
      omega
    · show 2 * spreadM M (at0 0 i / 2) + at0 0 i % 2 = setBit 0 false (2 * spreadM M i)
      rw [at0_zero, setBit_zero_even]
      have e : 2 * i / 2 = i := by omega
      rw [e]
      simp
    · show 2 * spreadM M ((at0 0 i + 2 ^ 0) / 2) + (at0 0 i + 2 ^ 0) % 2 =
        setBit 0 true (2 * spreadM M i)
      rw [at0_zero, setBit_zero_even]
      have e : (2 * i + 2 ^ 0) / 2 = i := by simp; omega
      have e' : (2 * i + 2 ^ 0) % 2 = 1 := by simp
      rw [e, e']
      simp
  | b + 1, true :: M, h => by
    have h' : M.getD b false = true := by simpa using h
    obtain ⟨h1, h2, h3, h4⟩ := take_out b M h'
    refine ⟨?_, fun i hi => ?_, fun i => ?_, fun i => ?_⟩
    · show nM M + 1 = nM (M.set b false) + 1 + 1
      rw [h1]
    · show at0 (posM M b + 1) i + 2 ^ (posM M b + 1) < 2 ^ (nM M + 1)
      have hi' : i < 2 ^ (nM (M.set b false) + 1) := hi
      have hi2 : i / 2 < 2 ^ nM (M.set b false) := by
        rw [pow_succ] at hi'
        omega
      have := h2 (i / 2) hi2
      rw [at0_succ, pow_succ, pow_succ 2 (nM M)]
      omega
    · show 2 * spreadM M (at0 (posM M b + 1) i / 2) + at0 (posM M b + 1) i % 2 =
        setBit (b + 1) false (2 * spreadM (M.set b false) (i / 2) + i % 2)
      rw [at0_succ, setBit_succ_add _ _ _ _ (Nat.mod_lt _ (by decide)), ← h3]
      have e : (2 * at0 (posM M b) (i / 2) + i % 2) / 2 = at0 (posM M b) (i / 2) := by omega
      have e' : (2 * at0 (posM M b) (i / 2) + i % 2) % 2 = i % 2 := by omega
      rw [e, e']
    · show 2 * spreadM M ((at0 (posM M b + 1) i + 2 ^ (posM M b + 1)) / 2) +
          (at0 (posM M b + 1) i + 2 ^ (posM M b + 1)) % 2 =
        setBit (b + 1) true (2 * spreadM (M.set b false) (i / 2) + i % 2)
      rw [at0_succ, setBit_succ_add _ _ _ _ (Nat.mod_lt _ (by decide)), ← h4, pow_succ]
      have e : (2 * at0 (posM M b) (i / 2) + i % 2 + 2 ^ posM M b * 2) / 2 =
          at0 (posM M b) (i / 2) + 2 ^ posM M b := by omega
      have e' : (2 * at0 (posM M b) (i / 2) + i % 2 + 2 ^ posM M b * 2) % 2 = i % 2 := by omega
      rw [e, e']
  | b + 1, false :: M, h => by
    have h' : M.getD b false = true := by simpa using h
    obtain ⟨h1, h2, h3, h4⟩ := take_out b M h'
    refine ⟨h1, h2, fun i => ?_, fun i => ?_⟩
    · show 2 * spreadM M (at0 (posM M b) i) = setBit (b + 1) false (2 * spreadM (M.set b false) i)
      rw [setBit_succ_even, h3]
    · show 2 * spreadM M (at0 (posM M b) i + 2 ^ posM M b) =
        setBit (b + 1) true (2 * spreadM (M.set b false) i)
      rw [setBit_succ_even, h4]

/-! ## 4 The list of free bits -/

theorem idx_length : ∀ M : List Bool, (idx M).length = nM M
  | [] => rfl
  | true :: M => by simp [idx, nM, idx_length M]
  | false :: M => by simp [idx, nM, idx_length M]

theorem idx_lt : ∀ (M : List Bool) (b : ℕ), b ∈ idx M → b < M.length
  | [], _, h => by simp [idx] at h
  | true :: M, b, h => by
    simp only [idx, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨a, ha, rfl⟩
    · simp
    · have := idx_lt M a ha
      simp
      omega
  | false :: M, b, h => by
    simp only [idx, List.mem_map] at h
    obtain ⟨a, ha, rfl⟩ := h
    have := idx_lt M a ha
    simp
    omega

theorem idx_all (m : ℕ) : idx (List.replicate m true) = List.range m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, List.range_succ_eq_map]
    show 0 :: (idx (List.replicate m true)).map (· + 1) = _
    rw [ih]

theorem filter_ne_map_succ (l : List ℕ) (b : ℕ) :
    (l.map (· + 1)).filter (· != b + 1) = (l.filter (· != b)).map (· + 1) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : a = b
    · subst h
      simp [ih]
    · have h1 : (a != b) = true := by simpa using h
      have h2 : (a + 1 != b + 1) = true := by simpa using h
      simp only [List.map_cons, List.filter_cons, h1, h2, if_true]
      rw [← ih]

theorem filter_ne_zero_map_succ (l : List ℕ) :
    (l.map (· + 1)).filter (· != 0) = l.map (· + 1) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

/-- The free bits without b are the free bits of the marks with b's mark taken away. -/
theorem idx_filter : ∀ (M : List Bool) (b : ℕ), (idx M).filter (· != b) = idx (M.set b false)
  | [], _ => rfl
  | true :: M, 0 => by
    show (0 :: (idx M).map (· + 1)).filter (· != 0) = (idx M).map (· + 1)
    rw [List.filter_cons]
    simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
    exact filter_ne_zero_map_succ _
  | false :: M, 0 => filter_ne_zero_map_succ _
  | true :: M, b + 1 => by
    show (0 :: (idx M).map (· + 1)).filter (· != b + 1) = 0 :: (idx (M.set b false)).map (· + 1)
    rw [List.filter_cons]
    have h : ((0 : ℕ) != b + 1) = true := by simp
    rw [if_pos h, filter_ne_map_succ, idx_filter M b]
  | false :: M, b + 1 => by
    show ((idx M).map (· + 1)).filter (· != b + 1) = (idx (M.set b false)).map (· + 1)
    rw [filter_ne_map_succ, idx_filter M b]

theorem filter_lt_map_succ (l : List ℕ) (b : ℕ) :
    ((l.map (· + 1)).filter (· < b + 1)).length = (l.filter (· < b)).length := by
  have e : ((fun x => decide (x < b + 1)) ∘ fun x : ℕ => x + 1) = fun x => decide (x < b) := by
    funext x
    simp
  rw [List.filter_map, List.length_map, e]

/-- How many free bits lie below b. -/
theorem idx_pos : ∀ (M : List Bool) (b : ℕ), ((idx M).filter (· < b)).length = posM M b
  | [], _ => rfl
  | true :: M, 0 => by simp [posM]
  | false :: M, 0 => by simp [posM]
  | true :: M, b + 1 => by
    show ((0 :: (idx M).map (· + 1)).filter (· < b + 1)).length = posM M b + 1
    rw [List.filter_cons]
    have h : decide ((0 : ℕ) < b + 1) = true := by simp
    rw [if_pos h, List.length_cons, filter_lt_map_succ, idx_pos M b]
  | false :: M, b + 1 => by
    show (((idx M).map (· + 1)).filter (· < b + 1)).length = posM M b
    rw [filter_lt_map_succ, idx_pos M b]

section
variable {K : Type} [Field K]

/-- A list read at the free bits' numbers is the list cut down to them. -/
theorem idx_map : ∀ (M : List Bool) (W : List K), M.length = W.length →
    (idx M).map (fun b => W.getD b 0) = compact M W
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | true :: M, w :: W, h => by
    have h' : M.length = W.length := by simpa using h
    show (0 :: (idx M).map (· + 1)).map (fun b => (w :: W).getD b 0) = w :: compact M W
    rw [List.map_cons, List.map_map, ← idx_map M W h']
    rfl
  | false :: M, w :: W, h => by
    have h' : M.length = W.length := by simpa using h
    show ((idx M).map (· + 1)).map (fun b => (w :: W).getD b 0) = compact M W
    rw [List.map_map, ← idx_map M W h']
    rfl

omit [Field K] in
theorem compact_length : ∀ (M : List Bool) (W : List K), M.length = W.length →
    (compact M W).length = nM M
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | true :: M, w :: W, h => by
    have h' : M.length = W.length := by simpa using h
    show (compact M W).length + 1 = nM M + 1
    rw [compact_length M W h']
  | false :: M, w :: W, h => by
    have h' : M.length = W.length := by simpa using h
    exact compact_length M W h'

theorem wts_length : ∀ (M : List Bool) (W : List K), M.length = W.length →
    (wts M W).length = W.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | true :: M, w :: W, h => by
    have h' : M.length = W.length := by simpa using h
    show (wts M W).length + 1 = W.length + 1
    rw [wts_length M W h']
  | false :: M, w :: W, h => by
    have h' : M.length = W.length := by simpa using h
    show (wts M W).length + 1 = W.length + 1
    rw [wts_length M W h']

theorem wts_all : ∀ W : List K, wts (List.replicate W.length true) W = W
  | [] => rfl
  | w :: W => by
    show w :: wts (List.replicate W.length true) W = w :: W
    rw [wts_all W]

theorem wts_set : ∀ (M : List Bool) (W : List K) (b : ℕ),
    wts (M.set b false) W = (wts M W).set b 0
  | [], _, _ => by simp [wts]
  | true :: M, [], b => by cases b <;> simp [wts]
  | false :: M, [], b => by cases b <;> simp [wts]
  | true :: M, w :: W, 0 => rfl
  | false :: M, w :: W, 0 => rfl
  | true :: M, w :: W, b + 1 => by
    show w :: wts (M.set b false) W = w :: (wts M W).set b 0
    rw [wts_set M W b]
  | false :: M, w :: W, b + 1 => by
    show 0 :: wts (M.set b false) W = 0 :: (wts M W).set b 0
    rw [wts_set M W b]

/-! ## 5 The sum -/

/-- **The sum over the long cube, under weights that are 0 at the bits that are not free, is the sum
over the short cube**, under the free bits' weights, of the summand at the short number laid
out. -/
theorem sum_spread : ∀ (M : List Bool) (W : List K), M.length = W.length → ∀ F : ℕ → K,
    ∑ X ∈ range (2 ^ W.length), eqN (wts M W) X * F X =
      ∑ i ∈ range (2 ^ nM M), eqN (compact M W) i * F (spreadM M i)
  | [], [], _, F => by simp [wts, compact, nM, spreadM]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | true :: M, w :: W, h, F => by
    have h' : M.length = W.length := by simpa using h
    have e1 := sum_cons w (wts M W) F
    have e2 := sum_cons w (compact M W) fun i => F (spreadM (true :: M) i)
    rw [List.length_cons, wts_length M W h'] at e1
    rw [List.length_cons, compact_length M W h'] at e2
    show ∑ X ∈ range (2 ^ (W.length + 1)), eqN (w :: wts M W) X * F X =
      ∑ i ∈ range (2 ^ (nM M + 1)), eqN (w :: compact M W) i * F (spreadM (true :: M) i)
    rw [e1, e2, sum_spread M W h' fun y => F (2 * y), sum_spread M W h' fun y => F (2 * y + 1)]
    have a0 : ∀ i, spreadM (true :: M) (2 * i) = 2 * spreadM M i := fun i => by
      show 2 * spreadM M (2 * i / 2) + 2 * i % 2 = _
      have e : 2 * i / 2 = i := by omega
      rw [e]
      omega
    have a1 : ∀ i, spreadM (true :: M) (2 * i + 1) = 2 * spreadM M i + 1 := fun i => by
      show 2 * spreadM M ((2 * i + 1) / 2) + (2 * i + 1) % 2 = _
      have e : (2 * i + 1) / 2 = i := by omega
      rw [e]
      omega
    simp only [a0, a1]
  | false :: M, w :: W, h, F => by
    have h' : M.length = W.length := by simpa using h
    have e1 := sum_cons (0 : K) (wts M W) F
    rw [List.length_cons, wts_length M W h'] at e1
    show ∑ X ∈ range (2 ^ (W.length + 1)), eqN (0 :: wts M W) X * F X =
      ∑ i ∈ range (2 ^ nM M), eqN (compact M W) i * F (2 * spreadM M i)
    rw [e1, sum_spread M W h' fun y => F (2 * y)]
    ring

end

/-! ## 6 The marks behind l rounds -/

/-- The marks behind l rounds of the order o, of m bits: the bits of these rounds are not free. -/
def maskN (o : List ℕ) (m : ℕ) : ℕ → List Bool
  | 0 => List.replicate m true
  | l + 1 => (maskN o m l).set (o.getD l 0) false

theorem maskN_length (o : List ℕ) (m : ℕ) : ∀ l, (maskN o m l).length = m
  | 0 => List.length_replicate
  | l + 1 => by
    show ((maskN o m l).set _ false).length = m
    rw [List.length_set, maskN_length o m l]

/-- A bit below m that none of the first l rounds binds is free behind them. -/
theorem maskN_free (o : List ℕ) (m : ℕ) : ∀ (l c : ℕ), c < m → (∀ i < l, o.getD i 0 ≠ c) →
    (maskN o m l).getD c false = true
  | 0, c, hc, _ => by
    show (List.replicate m true).getD c false = true
    rw [List.getD_eq_getElem _ _ (by simpa using hc)]
    simp
  | l + 1, c, hc, h => by
    show ((maskN o m l).set (o.getD l 0) false).getD c false = true
    have hne : o.getD l 0 ≠ c := h l (Nat.lt_succ_self l)
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne, ← List.getD_eq_getElem?_getD]
    exact maskN_free o m l c hc fun i hi => h i (Nat.lt_succ_of_lt hi)

/-- The weights behind l rounds are the point with 0 at the bits that are not free. -/
theorem wts_maskN {K : Type} [Field K] (o : List ℕ) (z : List K) :
    ∀ l, wts (maskN o z.length l) z = wtN o z l
  | 0 => wts_all z
  | l + 1 => by
    show wts ((maskN o z.length l).set (o.getD l 0) false) z = (wtN o z l).set (o.getD l 0) 0
    rw [wts_set, wts_maskN o z l]

/-- Under an order that lists each bit once, the bit of round l is free behind l rounds. -/
theorem maskN_next {o : List ℕ} {m : ℕ} (O : Ord o m) {l : ℕ} (hl : l < m) :
    (maskN o m l).getD (o.getD l 0) false = true :=
  maskN_free o m l _ (O.lt l hl) fun i hi e =>
    absurd (O.inj i (Nat.lt_trans hi hl) l hl e) (Nat.ne_of_lt hi)

end ProofFile.Honest.K3.FastLaw

#print axioms ProofFile.Honest.K3.FastLaw.take_out
#print axioms ProofFile.Honest.K3.FastLaw.sum_spread
#print axioms ProofFile.Honest.K3.FastLaw.idx_filter
#print axioms ProofFile.Honest.K3.FastLaw.idx_pos
#print axioms ProofFile.Honest.K3.FastLaw.idx_map
#print axioms ProofFile.Honest.K3.FastLaw.wts_maskN
#print axioms ProofFile.Honest.K3.FastLaw.maskN_next
#print axioms ProofFile.Honest.K3.FastLaw.at0_zero
#print axioms ProofFile.Honest.K3.FastLaw.at0_succ
#print axioms ProofFile.Honest.K3.FastLaw.setBit_zero_even
#print axioms ProofFile.Honest.K3.FastLaw.setBit_succ_even
#print axioms ProofFile.Honest.K3.FastLaw.setBit_succ_add
#print axioms ProofFile.Honest.K3.FastLaw.idx_length
#print axioms ProofFile.Honest.K3.FastLaw.idx_lt
#print axioms ProofFile.Honest.K3.FastLaw.idx_all
#print axioms ProofFile.Honest.K3.FastLaw.filter_ne_map_succ
#print axioms ProofFile.Honest.K3.FastLaw.filter_ne_zero_map_succ
#print axioms ProofFile.Honest.K3.FastLaw.filter_lt_map_succ
#print axioms ProofFile.Honest.K3.FastLaw.compact_length
#print axioms ProofFile.Honest.K3.FastLaw.wts_length
#print axioms ProofFile.Honest.K3.FastLaw.wts_all
#print axioms ProofFile.Honest.K3.FastLaw.wts_set
#print axioms ProofFile.Honest.K3.FastLaw.maskN_length
#print axioms ProofFile.Honest.K3.FastLaw.maskN_free
