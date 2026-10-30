-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Law/CubeKitA.lean: three definitions, and statements with their proofs.

What is here. Tools for the laws on a sum over a cube: weighted sums (`sumOver`,
Johnson/Desc/K4/Honest/Law/CubeTerms.lean) over the numbers below a power of two, in a commutative
ring.

  `sumOver_congr`, `sumOver_lin`   it reads f below the power alone; it is linear in f
  `lowAt_one`, `lowAt_even`, `lowAt_odd`   a bit 0 laid into a number
  `sumOver_peel`   one pair of weights taken out of the middle
  `bindK`, `sumOver_bind`   a table with one variable set; its sum
  `stepK`, `dotK`, `dotK_step`, `dotK_tab`, `dotK_sum`   a table of weights made pair by pair, and
     the sum under it
  Beside these, smaller steps: `stepK_cons`, `stepK_length`, `tab_length`.

Limits. Nothing here speaks of the program but for `lowAt` (Johnson/Desc/K4/Honest/Cube.lean), which
is arithmetic on numbers.

No property is claimed.
-/
import Johnson.Desc.K4.Honest.Law.CubeTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest.CubeLaw

variable {K : Type} [CommRing K]

/-! ## 1 The sum -/

/-- The sum reads f at the numbers below 2 ^ q.length alone. -/
theorem sumOver_congr : ∀ (q : List (K × K)) (f g : ℕ → K),
    (∀ i, i < 2 ^ q.length → f i = g i) → sumOver q f = sumOver q g
  | [], f, g, h => h 0 (by simp)
  | w :: q, f, g, h => by
    have h0 : sumOver q (fun i => f (2 * i)) = sumOver q (fun i => g (2 * i)) :=
      sumOver_congr q _ _ fun i hi => h (2 * i) (by rw [List.length_cons, pow_succ]; omega)
    have h1 : sumOver q (fun i => f (2 * i + 1)) = sumOver q (fun i => g (2 * i + 1)) :=
      sumOver_congr q _ _ fun i hi => h (2 * i + 1) (by rw [List.length_cons, pow_succ]; omega)
    simp only [sumOver]
    rw [h0, h1]

/-- The sum is linear in f. -/
theorem sumOver_lin : ∀ (q : List (K × K)) (a b : K) (f g : ℕ → K),
    sumOver q (fun i => a * f i + b * g i) = a * sumOver q f + b * sumOver q g
  | [], _, _, _, _ => rfl
  | w :: q, a, b, f, g => by
    have h0 : sumOver q (fun i => a * f (2 * i) + b * g (2 * i)) =
        a * sumOver q (fun i => f (2 * i)) + b * sumOver q (fun i => g (2 * i)) :=
      sumOver_lin q a b (fun i => f (2 * i)) (fun i => g (2 * i))
    have h1 : sumOver q (fun i => a * f (2 * i + 1) + b * g (2 * i + 1)) =
        a * sumOver q (fun i => f (2 * i + 1)) + b * sumOver q (fun i => g (2 * i + 1)) :=
      sumOver_lin q a b (fun i => f (2 * i + 1)) (fun i => g (2 * i + 1))
    simp only [sumOver]
    rw [h0, h1]
    ring

/-! ## 2 A bit laid in -/

theorem lowAt_one (i : ℕ) : lowAt 1 i = 2 * i := by
  unfold lowAt
  rw [Nat.div_one, Nat.mod_one]
  omega

theorem lowAt_even (s i : ℕ) : lowAt (2 * s) (2 * i) = 2 * lowAt s i := by
  have h1 : 2 * i / (2 * s) = i / s := by
    rw [← Nat.div_div_eq_div_mul]
    congr 1
    omega
  have h2 : 2 * i % (2 * s) = 2 * (i % s) := by
    rw [Nat.mod_mul]
    have a : 2 * i % 2 = 0 := by omega
    have b : 2 * i / 2 = i := by omega
    rw [a, b, Nat.zero_add]
  unfold lowAt
  rw [h1, h2]
  ring

theorem lowAt_odd (s i : ℕ) : lowAt (2 * s) (2 * i + 1) = 2 * lowAt s i + 1 := by
  have h1 : (2 * i + 1) / (2 * s) = i / s := by
    rw [← Nat.div_div_eq_div_mul]
    congr 1
    omega
  have h2 : (2 * i + 1) % (2 * s) = 2 * (i % s) + 1 := by
    rw [Nat.mod_mul]
    have a : (2 * i + 1) % 2 = 1 := by omega
    have b : (2 * i + 1) / 2 = i := by omega
    rw [a, b, Nat.add_comm]
  unfold lowAt
  rw [h1, h2]
  ring

/-! ## 3 One pair taken out -/

/-- **One pair of weights taken out of the middle.** -/
theorem sumOver_peel : ∀ (q1 q2 : List (K × K)) (w : K × K) (F : ℕ → K),
    sumOver (q1 ++ w :: q2) F =
      w.1 * sumOver (q1 ++ q2) (fun i => F (lowAt (2 ^ q1.length) i)) +
        w.2 * sumOver (q1 ++ q2) (fun i => F (lowAt (2 ^ q1.length) i + 2 ^ q1.length))
  | [], q2, w, F => by
    simp only [List.nil_append, List.length_nil, pow_zero, lowAt_one, sumOver]
  | u :: q1, q2, w, F => by
    have p : (2 : ℕ) ^ (q1.length + 1) = 2 * 2 ^ q1.length := pow_succ' 2 _
    have a : ∀ i, 2 * lowAt (2 ^ q1.length) i + 2 * 2 ^ q1.length =
        2 * (lowAt (2 ^ q1.length) i + 2 ^ q1.length) := fun i => by ring
    have b : ∀ i, 2 * lowAt (2 ^ q1.length) i + 1 + 2 * 2 ^ q1.length =
        2 * (lowAt (2 ^ q1.length) i + 2 ^ q1.length) + 1 := fun i => by ring
    simp only [List.cons_append, sumOver, List.length_cons]
    rw [p, sumOver_peel q1 q2 w (fun i => F (2 * i)),
      sumOver_peel q1 q2 w (fun i => F (2 * i + 1))]
    simp only [lowAt_even, lowAt_odd, a, b]
    ring

/-- A table with the variable at the place of value s set to r. -/
def bindK (s : ℕ) (r : K) (f : ℕ → K) : ℕ → K :=
  fun i => f (lowAt s i) + r * (f (lowAt s i + s) - f (lowAt s i))

/-- **To set a variable to r is to sum it with the weights 1 - r and r.** -/
theorem sumOver_bind (q1 q2 : List (K × K)) (r : K) (f : ℕ → K) :
    sumOver (q1 ++ q2) (bindK (2 ^ q1.length) r f) = sumOver (q1 ++ (1 - r, r) :: q2) f := by
  have e : bindK (2 ^ q1.length) r f = fun i =>
      (1 - r) * f (lowAt (2 ^ q1.length) i) + r * f (lowAt (2 ^ q1.length) i + 2 ^ q1.length) := by
    funext i
    simp only [bindK]
    ring
  rw [sumOver_peel, e]
  exact sumOver_lin (q1 ++ q2) (1 - r) r (fun i => f (lowAt (2 ^ q1.length) i))
    (fun i => f (lowAt (2 ^ q1.length) i + 2 ^ q1.length))

/-! ## 4 A table of weights -/

/-- One more pair: every entry a becomes the two entries a w.1 and a w.2. -/
def stepK (t : List K) (w : K × K) : List K := t.flatMap fun a => [a * w.1, a * w.2]

/-- The sum of F under a list of weights. -/
def dotK : List K → (ℕ → K) → K
  | [], _ => 0
  | a :: t, F => a * F 0 + dotK t (fun i => F (i + 1))

theorem stepK_cons (a : K) (t : List K) (w : K × K) :
    stepK (a :: t) w = a * w.1 :: a * w.2 :: stepK t w := by
  simp [stepK]

theorem stepK_length (w : K × K) : ∀ t : List K, (stepK t w).length = 2 * t.length
  | [] => rfl
  | a :: t => by
    rw [stepK_cons, List.length_cons, List.length_cons, stepK_length w t, List.length_cons]
    ring

theorem dotK_step : ∀ (t : List K) (w : K × K) (F : ℕ → K),
    dotK (stepK t w) F = dotK t (fun i => w.1 * F (2 * i) + w.2 * F (2 * i + 1))
  | [], _, _ => rfl
  | a :: t, w, F => by
    have h : ∀ i, 2 * (i + 1) = 2 * i + 1 + 1 := fun i => by omega
    rw [stepK_cons]
    simp only [dotK]
    rw [dotK_step t w (fun i => F (i + 1 + 1))]
    simp only [h, Nat.mul_zero, Nat.zero_add]
    ring

/-- **The sum under the table that is made of the pairs.** The table is folded over q.reverse: so
the first pair of q stands at bit 0. -/
theorem dotK_tab : ∀ (q : List (K × K)) (F : ℕ → K),
    dotK (q.reverse.foldl stepK [1]) F = sumOver q F
  | [], F => by simp [dotK, sumOver]
  | w :: q, F => by
    rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, dotK_step,
      dotK_tab q]
    exact sumOver_lin q w.1 w.2 (fun i => F (2 * i)) (fun i => F (2 * i + 1))

theorem tab_length : ∀ (ws : List (K × K)) (t : List K),
    (ws.foldl stepK t).length = 2 ^ ws.length * t.length
  | [], t => by simp
  | w :: ws, t => by
    rw [List.foldl_cons, tab_length ws, stepK_length, List.length_cons]
    ring

theorem dotK_sum : ∀ (t : List K) (F : ℕ → K),
    dotK t F = ∑ i ∈ Finset.range t.length, t.getD i 0 * F i
  | [], _ => by simp [dotK]
  | a :: t, F => by
    rw [dotK, dotK_sum t, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

end OnBytes.Desc.First.K4.Honest.CubeLaw

#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.sumOver_congr
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.sumOver_lin
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.lowAt_one
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.lowAt_even
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.lowAt_odd
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.sumOver_peel
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.bindK
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.sumOver_bind
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.stepK
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.dotK
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.stepK_cons
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.stepK_length
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.dotK_step
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.dotK_tab
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.tab_length
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.dotK_sum
