-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegIdxRun.lean: runs of variables as sources of bits (`Src`, Cm/SegIdx.lean).

Definitions with their short proofs; a tool for whoever writes families.
A source says where a bit comes from: a variable of the cube, its negation, or a constant. A list
of sources forms a number at each vertex (`Src.num`); `Src.OK l v`: every variable that l names is
below v, and none is named twice. Index atoms are written down with such lists (Cm/SegIdx.lean,
Cm/TargetSegIdxModel.lean).

Main names:
  `Src.run o w`: the w variables o, o + 1, .., o + w - 1, in this order (most significant bit
    first).
  `num_run`: for o + w ≤ v, at the vertex b of v variables its number is b / 2^(v - o - w) mod 2^w:
    the digits of b from variable o to variable o + w - 1.
  `mem_vars_run`, `ok_run`, `ok_append`, `ok_bit`: so that `Src.OK` of a concatenation of disjoint
    runs and constants is shown by comparing numbers.
-/
import Cm.SegIdxUnitProofs

set_option autoImplicit false

namespace Cm
open Cb

/-- the variables o, .., o + w - 1 -/
def Src.run (o w : ℕ) : List Src := (List.range w).map fun t => Src.var (o + t)

theorem run_length (o w : ℕ) : (Src.run o w).length = w := by simp [Src.run]

theorem run_succ (o w : ℕ) : Src.run o (w + 1) = Src.run o w ++ [Src.var (o + w)] := by
  simp [Src.run, List.range_succ]

theorem num_var {u v : ℕ} (hu : u < v) (b : ℕ) :
    Src.num [Src.var u] v b = b / 2 ^ (v - 1 - u) % 2 := by
  have h2 : b / 2 ^ (v - 1 - u) % 2 = 0 ∨ b / 2 ^ (v - 1 - u) % 2 = 1 := by omega
  rcases h2 with h | h <;> simp [Src.num, numL, Src.bitAt, hu, Nat.testBit_eq_decide_div_mod_eq, h]

theorem num_run :
    ∀ (o w : ℕ) {v : ℕ}, o + w ≤ v → ∀ b, Src.num (Src.run o w) v b = b / 2 ^ (v - o - w) % 2 ^ w
  | o, 0, v, _, b => by simp [Src.run, Src.num, numL, Nat.mod_one]
  | o, w + 1, v, h, b => by
      have e1 : v - o - w = (v - o - (w + 1)) + 1 := by omega
      have e2 : v - 1 - (o + w) = v - o - (w + 1) := by omega
      rw [run_succ, num_append, num_run o w (by omega) b, num_var (by omega) b, e1, e2,
        List.length_singleton, pow_one, pow_succ 2 (v - o - (w + 1)), ← Nat.div_div_eq_div_mul,
        pow_succ 2 w, Nat.mul_comm (2 ^ w) 2, Nat.mod_mul]
      ring

theorem vars_run (o w : ℕ) : Src.vars (Src.run o w) = (List.range w).map fun t => o + t := by
  induction w with
  | zero => rfl
  | succ w ih => rw [run_succ, vars_append, ih, List.range_succ, List.map_append]; rfl

theorem mem_vars_run {o w u : ℕ} : u ∈ Src.vars (Src.run o w) ↔ o ≤ u ∧ u < o + w := by
  rw [vars_run, List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have := List.mem_range.1 ht
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨u - o, List.mem_range.2 (by omega), by omega⟩

theorem ok_run {o w v : ℕ} (h : o + w ≤ v) : Src.OK (Src.run o w) v := by
  refine ⟨?_, fun u hu => by have := mem_vars_run.1 hu; omega⟩
  rw [vars_run]
  exact (List.nodup_range).map fun a b hab => by omega

theorem ok_append {l l' : List Src} {v : ℕ} (h : Src.OK l v) (h' : Src.OK l' v)
    (hd : ∀ u ∈ Src.vars l, ∀ u' ∈ Src.vars l', u ≠ u') : Src.OK (l ++ l') v := by
  unfold Src.OK
  rw [vars_append]
  exact ⟨List.nodup_append.2 ⟨h.1, h'.1, hd⟩,
    fun u hu => (List.mem_append.1 hu).elim (h.2 u) (h'.2 u)⟩

theorem ok_bit (β : Bool) (v : ℕ) : Src.OK [Src.bit β] v :=
  ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩

theorem ok_nil (v : ℕ) : Src.OK [] v := ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩

/-- two runs, the second after the first (a + m ≤ b), both below v, have `Src.OK` together -/
theorem ok_run_run {a m b n v : ℕ} (h1 : a + m ≤ b) (h2 : b + n ≤ v) :
    Src.OK (Src.run a m ++ Src.run b n) v :=
  ok_append (ok_run (by omega)) (ok_run h2) fun u hu u' hu' => by
    have := mem_vars_run.1 hu
    have := mem_vars_run.1 hu'
    omega

end Cm
