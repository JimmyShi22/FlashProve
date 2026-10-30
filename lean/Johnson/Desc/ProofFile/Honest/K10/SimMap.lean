-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/SimMap.lean: the closing of a segment (K10): `RunOneToOne` (Honest/K10/Sim.lean's
(3a)), proved: over every commutative ring (in the lowest universe), at every k ≥ 1, the map from a run's 2 k + 1
coefficients to what is sent of them (`runSent`) and the map back (`runBack`) undo each other. Algebra on two written
maps: it names no part, no side and no law on coins.

  `backB`, `runBackN_eq`   the map back with its inner letter named
    `sent_odd`, `sent_even`, `sumB_step`, `phiB_low`, `phiB_top`   `runSentN` at a round's two numbers; one step of
                   `sumB`; `phiB` at its two arms
    `back_low_even`, `back_low_odd`, `back_top0`, `back_top1`, `back_top2`, `backB_zero`, `backB_top`, `backB_mid`,
                   `sorts`   `runBackN` and its inner letter at each sort of number; the five sorts
    `back_sentN`, `sent_backN`   each undoes the other, by number
    `atN_lt`   `atN` under the count is the function's own value
  **`run_one_to_one`**   `RunOneToOne`

Limits. What follows from it for a part is not said here. No property of the protocol is claimed: nothing is said on its
soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Sim
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10

section
variable {R : Type} [CommRing R]

/-- The inner letter of `runBackN`. -/
def backB (k : Nat) (s : Nat → R) (l : Nat) : R :=
  if l = 0 then s 0 else if l = k then 0 else s (2 * l - 1)

theorem runBackN_eq (k : Nat) (s : Nat → R) (i : Nat) :
    runBackN k s i =
      if i = 2 * k - 2 then s (2 * k - 1)
      else if i = 2 * k then s (2 * k)
      else if i = 2 * k - 1 then backB k s (k - 1) - s (2 * k) - 2 * s (2 * k - 1)
      else if i % 2 = 1 then s (2 * (i / 2 + 1))
      else backB k s (i / 2) - 2 * backB k s (i / 2 + 1) - s (2 * (i / 2 + 1)) := rfl

theorem sent_odd (k m : Nat) (w : Nat → R) :
    runSentN k w (2 * m + 1) =
      sumB k w (k - (m + 1)) + (if m + 1 = k then w (2 * k - 2) else 0) := by
  have h1 : (2 * m) % 2 = 0 := by omega
  have h2 : (2 * m) / 2 = m := by omega
  simp only [runSentN]
  rw [if_pos h1, h2]

theorem sent_even (k m : Nat) (w : Nat → R) :
    runSentN k w (2 * m + 1 + 1) = if m + 1 = k then w (2 * k) else w (2 * (m + 1) - 1) := by
  have h1 : ¬ (2 * m + 1) % 2 = 0 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  simp only [runSentN]
  rw [if_neg h1, h2]

theorem sumB_step (k m : Nat) (hm : m < k) (w : Nat → R) :
    sumB k w (k - m) = phiB k w (m + 1) + 2 * sumB k w (k - (m + 1)) := by
  have e1 : k - m = (k - (m + 1)) + 1 := by omega
  have e2 : k - (k - (m + 1)) = m + 1 := by omega
  rw [e1]
  show phiB k w (k - (k - (m + 1))) + 2 * sumB k w (k - (m + 1)) = _
  rw [e2]

theorem phiB_low (n m : Nat) (hm : m < n) (w : Nat → R) :
    phiB (n + 1) w (m + 1) = w (2 * m) + w (2 * m + 1) := by
  have e1 : 2 * (m + 1) - 2 = 2 * m := by omega
  have e2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  unfold phiB
  rw [if_neg (by omega), e1, e2]

theorem phiB_top (n : Nat) (w : Nat → R) :
    phiB (n + 1) w (n + 1) = 2 * w (2 * n) + w (2 * n + 1) + w (2 * n + 1 + 1) := by
  have e1 : 2 * (n + 1) - 2 = 2 * n := by omega
  have e2 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  have e3 : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
  unfold phiB
  rw [if_pos rfl, e1, e2, e3]

theorem back_low_even (n m : Nat) (hm : m < n) (s : Nat → R) :
    runBackN (n + 1) s (2 * m) =
      backB (n + 1) s m - 2 * backB (n + 1) s (m + 1) - s (2 * m + 1 + 1) := by
  have e1 : (2 * m) / 2 = m := by omega
  have e2 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
  rw [runBackN_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), e1,
    e2]

theorem back_low_odd (n m : Nat) (hm : m < n) (s : Nat → R) :
    runBackN (n + 1) s (2 * m + 1) = s (2 * m + 1 + 1) := by
  have e1 : (2 * m + 1) / 2 = m := by omega
  have e2 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
  rw [runBackN_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), e1,
    e2]

theorem back_top0 (n : Nat) (s : Nat → R) : runBackN (n + 1) s (2 * n) = s (2 * n + 1) := by
  have e : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  rw [runBackN_eq, if_pos (by omega), e]

theorem back_top1 (n : Nat) (s : Nat → R) :
    runBackN (n + 1) s (2 * n + 1) =
      backB (n + 1) s n - s (2 * n + 1 + 1) - 2 * s (2 * n + 1) := by
  have e1 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  have e2 : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
  have e3 : n + 1 - 1 = n := by omega
  rw [runBackN_eq, if_neg (by omega), if_neg (by omega), if_pos (by omega), e1, e3, e2]

theorem back_top2 (n : Nat) (s : Nat → R) :
    runBackN (n + 1) s (2 * n + 1 + 1) = s (2 * n + 1 + 1) := by
  have e : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
  rw [runBackN_eq, if_neg (by omega), if_pos (by omega), e]

theorem backB_zero (k : Nat) (s : Nat → R) : backB k s 0 = s 0 := by
  unfold backB
  rw [if_pos rfl]

theorem backB_top (n : Nat) (s : Nat → R) : backB (n + 1) s (n + 1) = 0 := by
  unfold backB
  rw [if_neg (by omega), if_pos rfl]

theorem backB_mid (n m : Nat) (hm : m < n) (s : Nat → R) :
    backB (n + 1) s (m + 1) = s (2 * m + 1) := by
  have e : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  unfold backB
  rw [if_neg (by omega), if_neg (by omega), e]

/-- Each number below 2 n + 3 is of one of five sorts. -/
theorem sorts (n i : Nat) (hi : i < 2 * (n + 1) + 1) :
    (∃ m, m < n ∧ i = 2 * m) ∨ (∃ m, m < n ∧ i = 2 * m + 1) ∨ i = 2 * n ∨ i = 2 * n + 1 ∨
      i = 2 * n + 1 + 1 := by
  by_cases h : i < 2 * n
  · by_cases h2 : i % 2 = 0
    · exact Or.inl ⟨i / 2, by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨i / 2, by omega, by omega⟩)
  · exact Or.inr (Or.inr (by omega))

/-- **The way back undoes the map**, by number. -/
theorem back_sentN (n : Nat) (W s : Nat → R)
    (hs : ∀ j, j < 2 * (n + 1) + 1 → s j = runSentN (n + 1) W j) (i : Nat)
    (hi : i < 2 * (n + 1) + 1) : runBackN (n + 1) s i = W i := by
  have s_odd_low : ∀ m, m < n → s (2 * m + 1) = sumB (n + 1) W (n + 1 - (m + 1)) := by
    intro m hm
    rw [hs _ (by omega), sent_odd, if_neg (by omega), add_zero]
  have s_even_low : ∀ m, m < n → s (2 * m + 1 + 1) = W (2 * m + 1) := by
    intro m hm
    have e : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [hs _ (by omega), sent_even, if_neg (by omega), e]
  have s_odd_top : s (2 * n + 1) = W (2 * n) := by
    have e : 2 * (n + 1) - 2 = 2 * n := by omega
    rw [hs _ (by omega), sent_odd, if_pos rfl, Nat.sub_self, e]
    show (0 : R) + W (2 * n) = W (2 * n)
    rw [zero_add]
  have s_even_top : s (2 * n + 1 + 1) = W (2 * n + 1 + 1) := by
    have e : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    rw [hs _ (by omega), sent_even, if_pos rfl, e]
  have hB : ∀ l, l ≤ n + 1 → backB (n + 1) s l = sumB (n + 1) W (n + 1 - l) := by
    intro l hl
    rcases Nat.eq_zero_or_pos l with h0 | h0
    · subst h0
      rw [backB_zero, hs 0 (by omega)]
      rfl
    · obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
      by_cases hm : m < n
      · rw [backB_mid n m hm, s_odd_low m hm]
      · obtain rfl : m = n := by omega
        rw [backB_top, Nat.sub_self]
        rfl
  rcases sorts n i hi with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | rfl | rfl | rfl
  · rw [back_low_even n m hm, hB m (by omega), hB (m + 1) (by omega), s_even_low m hm,
      sumB_step (n + 1) m (by omega), phiB_low n m hm]
    ring
  · rw [back_low_odd n m hm, s_even_low m hm]
  · rw [back_top0, s_odd_top]
  · rw [back_top1, hB n (by omega), s_even_top, s_odd_top, sumB_step (n + 1) n (by omega),
      phiB_top, Nat.sub_self]
    show 2 * W (2 * n) + W (2 * n + 1) + W (2 * n + 1 + 1) + 2 * (0 : R) - W (2 * n + 1 + 1) -
      2 * W (2 * n) = W (2 * n + 1)
    ring
  · rw [back_top2, s_even_top]

/-- **The map undoes the way back**, by number. -/
theorem sent_backN (n : Nat) (s W : Nat → R)
    (hW : ∀ i, i < 2 * (n + 1) + 1 → W i = runBackN (n + 1) s i) (j : Nat)
    (hj : j < 2 * (n + 1) + 1) : runSentN (n + 1) W j = s j := by
  have hS : ∀ d, d ≤ n + 1 → sumB (n + 1) W d = backB (n + 1) s (n + 1 - d) := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero, backB_top]
      rfl
    | succ d ih =>
      intro hd
      have ihd := ih (by omega)
      obtain ⟨m, hm⟩ : ∃ m, n + 1 - d = m + 1 := ⟨n - d, by omega⟩
      have e : n + 1 - (d + 1) = m := by omega
      show phiB (n + 1) W (n + 1 - d) + 2 * sumB (n + 1) W d = _
      rw [ihd, hm, e]
      by_cases hmn : m < n
      · rw [phiB_low n m hmn, hW _ (by omega), hW (2 * m + 1) (by omega), back_low_even n m hmn,
          back_low_odd n m hmn]
        ring
      · have hm' : m = n := by omega
        rw [hm', phiB_top, hW (2 * n) (by omega), hW (2 * n + 1) (by omega),
          hW (2 * n + 1 + 1) (by omega), back_top0, back_top1, back_top2, backB_top]
        ring
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0
    show sumB (n + 1) W (n + 1) = s 0
    rw [hS (n + 1) (le_refl _), Nat.sub_self, backB_zero]
  · by_cases hodd : j % 2 = 1
    · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m + 1 := ⟨j / 2, by omega⟩
      rw [sent_odd, hS _ (by omega)]
      have e : n + 1 - (n + 1 - (m + 1)) = m + 1 := by omega
      rw [e]
      by_cases hmn : m < n
      · rw [if_neg (by omega), add_zero, backB_mid n m hmn]
      · have hm' : m = n := by omega
        have e2 : 2 * (n + 1) - 2 = 2 * n := by omega
        rw [hm', if_pos rfl, backB_top, zero_add, e2, hW _ (by omega), back_top0]
    · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m + 1 + 1 := ⟨j / 2 - 1, by omega⟩
      rw [sent_even]
      by_cases hmn : m < n
      · have e2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
        rw [if_neg (by omega), e2, hW _ (by omega), back_low_odd n m hmn]
      · have hm' : m = n := by omega
        have e2 : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
        rw [hm', if_pos rfl, e2, hW _ (by omega), back_top2]

theorem atN_lt {n : Nat} (f : Fin n → R) (j : Nat) (hj : j < n) : atN f j = f ⟨j, hj⟩ := by
  unfold atN
  rw [dif_pos hj]

end

/-- **`RunOneToOne`.** -/
theorem run_one_to_one : RunOneToOne := by
  intro R _ k hk
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  refine ⟨fun w => funext fun i => ?_, fun s => funext fun i => ?_⟩
  · show runBackN (n + 1) (atN (runSent (n + 1) w)) i.1 = w i
    rw [back_sentN n (atN w) (atN (runSent (n + 1) w))
      (fun j hj => by rw [atN_lt _ j hj]; rfl) i.1 i.2, atN_lt w i.1 i.2]
  · show runSentN (n + 1) (atN (runBack (n + 1) s)) i.1 = s i
    rw [sent_backN n (atN s) (atN (runBack (n + 1) s))
      (fun j hj => by rw [atN_lt _ j hj]; rfl) i.1 i.2, atN_lt s i.1 i.2]

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.backB
#print axioms ProofFile.Honest.K10.runBackN_eq
#print axioms ProofFile.Honest.K10.sent_odd
#print axioms ProofFile.Honest.K10.sent_even
#print axioms ProofFile.Honest.K10.sumB_step
#print axioms ProofFile.Honest.K10.phiB_low
#print axioms ProofFile.Honest.K10.phiB_top
#print axioms ProofFile.Honest.K10.back_low_even
#print axioms ProofFile.Honest.K10.back_low_odd
#print axioms ProofFile.Honest.K10.back_top0
#print axioms ProofFile.Honest.K10.back_top1
#print axioms ProofFile.Honest.K10.back_top2
#print axioms ProofFile.Honest.K10.backB_zero
#print axioms ProofFile.Honest.K10.backB_top
#print axioms ProofFile.Honest.K10.backB_mid
#print axioms ProofFile.Honest.K10.sorts
#print axioms ProofFile.Honest.K10.back_sentN
#print axioms ProofFile.Honest.K10.sent_backN
#print axioms ProofFile.Honest.K10.atN_lt
#print axioms ProofFile.Honest.K10.run_one_to_one
