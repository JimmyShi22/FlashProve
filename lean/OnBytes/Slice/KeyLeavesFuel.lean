-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyLeavesFuel.lean: the loop that cuts a run of padding into cubes has steps enough.

`Lkp.cubesOf` (OnBytes/Iop/Lkp.lean) cuts a run of numbers into aligned blocks in at most 130 steps.
Each step takes the largest aligned block that begins at the next number and fits what is left, of
at most 2 ^ 62 numbers. OnBytes/Slice/KeyLeavesCubes.lean asks as a public test that nothing is left
after the steps (`Covered`). This file shows that the test holds for every run that lies below 2 ^ n
with n at most 61: 2 n + 1 steps are enough.

The argument is the one in the program's comment. While the block's size is bounded by how far the
next number is aligned, the next number behind the block is aligned further: the sizes grow, and
there are at most n such steps. Once a block's size is bounded by what is left, less than that size
is left behind it and the next number is still aligned to it: the sizes shrink, and there are at
most n + 1 such steps.

With it the statement on the leaves of the key trees holds under the program's own public tests
alone (`top`): they bound the number of bits of a key's number by 61.

Main theorems.
 `growBits_le`, `growBits_stop`, `growBits_ge`   the search for a block's size: its bound, why it
                   stops, and how far it gets at least.
 `leftAfter_mono`   more steps leave nothing if fewer do.
 `shrink`           if less than 2 ^ c is left and the next number is aligned to 2 ^ c, c steps are
                    enough.
 `grow`             if the next number is aligned to 2 ^ a, (n - a) + n + 1 steps are enough.
 `covered_of_le`    every run below 2 ^ n, n at most 61, is covered.
 `bits_lt`, `covered_of_tests`   the program's tests give it for every run of padding of a lookup.
 `top`              the statement `Top` of OnBytes/Slice/KeyLeaves.lean.

Not claimed. Nothing on runs of padding with a step other than 1. That the functions over the field
are the readings of the program's. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyLeavesTop

set_option autoImplicit false

namespace OnBytes.Slice.Leaves
open OnBytes.Params (WfRun WfPart WfLookup)

/-! ## The search for a block's size -/

/-- The search goes up by at most its number of steps. -/
theorem growBits_le (x left : ℕ) : ∀ k b, Lkp.growBits x left k b ≤ b + k
  | 0, _ => Nat.le_refl _
  | k + 1, b => by
    unfold Lkp.growBits
    split
    · have := growBits_le x left k (b + 1)
      omega
    · omega

/-- If the search stops before its steps are used up, the next size is not aligned or does not
fit. -/
theorem growBits_stop (x left : ℕ) : ∀ k b, Lkp.growBits x left k b < b + k →
    ¬(x % 2 ^ (Lkp.growBits x left k b + 1) = 0 ∧ 2 ^ (Lkp.growBits x left k b + 1) ≤ left)
  | 0, b, h => absurd h (Nat.lt_irrefl _)
  | k + 1, b, h => by
    unfold Lkp.growBits at h ⊢
    by_cases hc : (x % 2 ^ (b + 1) == 0 && decide (2 ^ (b + 1) ≤ left)) = true
    · rw [if_pos hc] at h ⊢
      exact growBits_stop x left k (b + 1) (by omega)
    · rw [if_neg hc]
      rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      exact hc

/-- The search gets at least to a, if all sizes up to a are aligned and fit. -/
theorem growBits_ge (x left a : ℕ) (h1 : x % 2 ^ a = 0) (h2 : 2 ^ a ≤ left) :
    ∀ k b, b ≤ a → a ≤ b + k → a ≤ Lkp.growBits x left k b
  | 0, b, _, h => h
  | k + 1, b, hb, h => by
    unfold Lkp.growBits
    by_cases e : b = a
    · subst e
      split
      · have := growBits_spec x left k (b + 1)
        have hm : ∀ k' b', b' ≤ Lkp.growBits x left k' b' := by
          intro k'
          induction k' with
          | zero => intro b'; exact Nat.le_refl _
          | succ k' ih =>
            intro b'
            unfold Lkp.growBits
            split
            · exact le_trans (Nat.le_succ _) (ih (b' + 1))
            · exact Nat.le_refl _
        exact le_trans (Nat.le_succ _) (hm k (b + 1))
      · exact Nat.le_refl _
    · have hlt : b + 1 ≤ a := by omega
      have d1 : x % 2 ^ (b + 1) = 0 :=
        Nat.mod_eq_zero_of_dvd ((pow_dvd_pow 2 hlt).trans (Nat.dvd_of_mod_eq_zero h1))
      have d2 : 2 ^ (b + 1) ≤ left := le_trans (Nat.pow_le_pow_right (by decide) hlt) h2
      have hc : (x % 2 ^ (b + 1) == 0 && decide (2 ^ (b + 1) ≤ left)) = true := by
        rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
        exact ⟨d1, d2⟩
      rw [if_pos hc]
      exact growBits_ge x left a h1 h2 k (b + 1) hlt (by omega)

/-! ## The loop -/

/-- Where nothing is left, nothing is left after any number of steps. -/
theorem leftAfter_zero (k x : ℕ) : leftAfter k x 0 = 0 := by
  cases k <;> rfl

/-- More steps leave nothing if fewer do. -/
theorem leftAfter_mono : ∀ (k x left : ℕ), leftAfter k x left = 0 → ∀ j, leftAfter (k + j) x left =
0
  | 0, x, left, h, j => by
    have h0 : left = 0 := h
    rw [h0]
    exact leftAfter_zero _ _
  | k + 1, x, left, h, j => by
    rw [show k + 1 + j = (k + j) + 1 by omega]
    unfold leftAfter at h ⊢
    by_cases h0 : (left == 0) = true
    · rw [if_pos h0]
    · rw [if_neg h0] at h ⊢
      exact leftAfter_mono k _ _ h j

/-- More steps leave nothing if fewer do. -/
theorem leftAfter_le {k k' x left : ℕ} (h : leftAfter k x left = 0) (hk : k ≤ k') :
    leftAfter k' x left = 0 := by
  have := leftAfter_mono k x left h (k' - k)
  rwa [Nat.add_sub_cancel' hk] at this

/-- One step, where something is left. -/
theorem leftAfter_succ (k x left : ℕ) (h : left ≠ 0) :
    leftAfter (k + 1) x left =
      leftAfter k (x + 2 ^ Lkp.growBits x left 62 0) (left - 2 ^ Lkp.growBits x left 62 0) := by
  conv_lhs => unfold leftAfter
  rw [if_neg (by simpa using h)]

/-- The sizes shrink. If less than 2 ^ c is left and the next number is aligned to 2 ^ c, c
steps are enough. -/
theorem shrink : ∀ (c x left : ℕ), c ≤ 62 → x % 2 ^ c = 0 → left < 2 ^ c → leftAfter c x left = 0
  | 0, _, left, _, _, h => by
    show left = 0
    simpa using h
  | c + 1, x, left, hc, hx, hl => by
    by_cases h0 : left = 0
    · rw [h0]
      exact leftAfter_zero _ _
    rw [leftAfter_succ c x left h0]
    obtain ⟨g1, g2⟩ := growBits_spec x left 62 0 (by rw [pow_zero, Nat.mod_one])
      (by rw [pow_zero]; omega)
    generalize hb : Lkp.growBits x left 62 0 = b at g1 g2 ⊢
    have hbc : b ≤ c := by
      have : 2 ^ b < 2 ^ (c + 1) := lt_of_le_of_lt g2 hl
      have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 this
      omega
    have hstop := growBits_stop x left 62 0 (by rw [hb]; omega)
    rw [hb] at hstop
    have hd : x % 2 ^ (b + 1) = 0 :=
      Nat.mod_eq_zero_of_dvd ((pow_dvd_pow 2 (by omega : b + 1 ≤ c + 1)).trans
        (Nat.dvd_of_mod_eq_zero hx))
    have hlt : left < 2 ^ (b + 1) := by
      by_contra hn
      exact hstop ⟨hd, by omega⟩
    refine leftAfter_le (shrink b _ _ (by omega) ?_ ?_) hbc
    · rw [Nat.add_mod, g1, Nat.mod_self, Nat.add_zero, Nat.zero_mod]
    · rw [pow_succ] at hlt
      omega

/-- The sizes grow, then shrink. If the run lies below 2 ^ n and the next number is aligned to
2 ^ a, (n - a) + n + 1 steps are enough. -/
theorem grow (n : ℕ) (hn : n ≤ 61) : ∀ (d a x left : ℕ), n - a = d → a ≤ n → x % 2 ^ a = 0 →
    x + left ≤ 2 ^ n → leftAfter (d + n + 1) x left = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro a x left hd ha hx hxl
    by_cases h0 : left = 0
    · rw [h0]
      exact leftAfter_zero _ _
    by_cases hs : left < 2 ^ a
    · exact leftAfter_le (shrink a x left (by omega) hx hs) (by omega)
    rw [leftAfter_succ (d + n) x left h0]
    obtain ⟨g1, g2⟩ := growBits_spec x left 62 0 (by rw [pow_zero, Nat.mod_one])
      (by rw [pow_zero]; omega)
    have hge := growBits_ge x left a hx (by omega) 62 0 (Nat.zero_le _) (by omega)
    generalize hb : Lkp.growBits x left 62 0 = b at g1 g2 hge ⊢
    have hbn : b ≤ n := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 (by omega)
    have hstop := growBits_stop x left 62 0 (by rw [hb]; omega)
    rw [hb] at hstop
    have hx' : (x + 2 ^ b) % 2 ^ b = 0 := by
      rw [Nat.add_mod, g1, Nat.mod_self, Nat.add_zero, Nat.zero_mod]
    by_cases hl : left < 2 ^ (b + 1)
    · refine leftAfter_le (shrink b _ _ (by omega) hx' ?_) (by omega)
      rw [pow_succ] at hl
      omega
    · have hnd : x % 2 ^ (b + 1) ≠ 0 := fun hz => hstop ⟨hz, by omega⟩
      -- x is 2 ^ b modulo 2 ^ (b + 1), so the next number is aligned to 2 ^ (b + 1)
      have hx2 : (x + 2 ^ b) % 2 ^ (b + 1) = 0 := by
        obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero g1
        have hodd : q % 2 = 1 := by
          by_contra hq2
          have hq0 : q % 2 = 0 := by omega
          obtain ⟨q', hq'⟩ := Nat.dvd_of_mod_eq_zero hq0
          exact hnd (Nat.mod_eq_zero_of_dvd ⟨q', by rw [hq, hq', pow_succ]; ring⟩)
        refine Nat.mod_eq_zero_of_dvd ⟨(q + 1) / 2, ?_⟩
        have h2 : 2 * ((q + 1) / 2) = q + 1 := by omega
        calc x + 2 ^ b = 2 ^ b * (q + 1) := by rw [hq]; ring
          _ = 2 ^ b * (2 * ((q + 1) / 2)) := by rw [h2]
          _ = 2 ^ (b + 1) * ((q + 1) / 2) := by rw [pow_succ]; ring
      have hb1 : b + 1 ≤ n := by
        by_contra hc
        have hbe : b = n := by omega
        subst hbe
        have : x = 0 := by omega
        exact hnd (by rw [this]; exact Nat.zero_mod _)
      have := ih (n - (b + 1)) (by omega) (b + 1) (x + 2 ^ b) (left - 2 ^ b) rfl hb1 hx2 (by omega)
      exact leftAfter_le this (by omega)

/-- Every run of neighbours that lies below 2 ^ n, n at most 61, is covered. -/
theorem covered_of_le (p : Lkp.Padding) (n : ℕ) (hn : n ≤ 61) (h : p.first + p.length ≤ 2 ^ n) :
    Covered p :=
  leftAfter_le (grow n hn n 0 p.first p.length (Nat.sub_zero n) (Nat.zero_le _)
    (by rw [pow_zero, Nat.mod_one]) h) (by omega)

/-! ## From the program's public tests -/

/-- The number of bits of a key's number is below the number of planes. -/
theorem partsFit_bits (m : Wf.Matrix) (l : WfLookup) : ∀ (ps : List WfPart) (keys : ℕ),
    Wf.partsFit m l keys ps = true → ∀ p ∈ ps, p.logPlaces + m.kCol < Wf.planesOf l
  | [], _, _, p, hp => by cases hp
  | q :: ps, keys, h, p, hp => by
    simp only [Wf.partsFit, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hp with e | hp
    · subst e
      exact h.1.1.1.1.2
    · exact partsFit_bits m l ps _ h.2 p hp

/-- A key's number has at most 61 bits. -/
theorem bits_lt {m : Wf.Matrix} {l : WfLookup} {p : WfPart} (hl : Wf.lookupOk Wf.fBits l = true)
    (hm : Wf.fitsMatrix m l = true) (hp : p ∈ l.parts) : p.logPlaces + m.kCol ≤ 61 := by
  have h1 := partsFit_bits m l l.parts 0 hm p hp
  simp only [Wf.lookupOk, Bool.and_eq_true, decide_eq_true_eq] at hl
  have h2 : Wf.planesOf l ≤ 62 := hl.1.1.1.1.1.1.1.1.1.2
  omega

/-- A member of a numbered list is a member of the list. -/
theorem fst_mem_of_mem_zipIdx {α : Type} : ∀ (l : List α) (k : ℕ) (x : α × ℕ), x ∈ l.zipIdx k →
    x.1 ∈ l
  | [], _, _, h => by cases h
  | a :: l, k, x, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.1 h with h | h
    · rw [h]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (fst_mem_of_mem_zipIdx l (k + 1) x h)

/-- The program's public tests give that every run of padding of a lookup is covered. -/
theorem covered_of_tests (m : Wf.Matrix) (l : WfLookup) (id : ℕ)
    (hl : Wf.lookupOk Wf.fBits l = true) (hm : Wf.fitsMatrix m l = true) :
    ∀ q ∈ (Wf.lookupOf id m l).padding, Covered q := by
  intro q hq
  have hq' : q ∈ (l.parts.zipIdx 0).flatMap fun x =>
      (Wf.paddingFrom m.kCol x.2 l.paddingKey.toNat x.1.logPlaces 0 x.1.runs #[]).toList := hq
  obtain ⟨x, hx, hqx⟩ := List.mem_flatMap.1 hq'
  have hp : x.1 ∈ l.parts := fst_mem_of_mem_zipIdx l.parts 0 x hx
  rw [paddingFrom_eq] at hqx
  rcases List.mem_append.1 hqx with h | h
  · cases h
  obtain ⟨g, hg, hs⟩ := List.mem_flatMap.1 h
  have hle := gaps_le _ _ _ (runsOk_of hl hp) g hg
  unfold Wf.stretch at hs
  split at hs
  · next hlt =>
    rw [List.mem_singleton.1 hs]
    refine covered_of_le _ (x.1.logPlaces + m.kCol) (bits_lt hl hm hp) ?_
    show g.1 * 2 ^ m.kCol + (g.2 - g.1) * 2 ^ m.kCol ≤ _
    rw [← Nat.add_mul, Nat.add_sub_cancel' (le_of_lt hlt), pow_add]
    exact Nat.mul_le_mul_right _ hle
  · cases hs

/-- The claim on the leaves of a part's key tree holds exactly if the pending row on the matrix
holds, under the program's own public tests and the two conditions on the letters that `Top`
names. -/
theorem top : Top :=
  top_of_covered fun m l id _ hl hm => covered_of_tests m l id hl hm

end OnBytes.Slice.Leaves
