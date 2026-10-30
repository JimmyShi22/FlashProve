-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/GateRows.lean: the verifier's two tables of the gate, at the stored example's
numbers (step 2^-8, bound 4095, routed experts, the gate's clamp), are the library's reference
tables, entry by entry. (That the lookup's tables FL and FS are therefore the library's:
Johnson/Meaning/GateLut.lean.)

  silu_word: entry t of the first table is refSILU t + 4096, for every t below 65536.
  sig_word: entry u of the second is refSIGM (u + 2^14), for every u below 32768.
  fs_upper: entry u of the second, from 32768 on, is the clamp of u - 49152 to -127 .. 127, plus
    128.
It joins Johnson/Meaning/GateLists.lean (the words as functions of a power; the powers as a
recursion) with Johnson/Meaning/GateWords.lean (the kernel's 17 evaluations).
Not claimed: that the stored words are the rounded values of the real functions.
-/
import Johnson.Meaning.GateWords
import Johnson.Road.HeadTabs
import Johnson.Road.HeadLaid

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.Gate

open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (fxOne gateTables siluWord sigmoidAt fsWord clampHalf rowFS expPowers)
open Meaning.Rope (xAt)
open Inst.Model (dec tbRef refSILU refSIGM FL FS)

/-- A stored word of SILU that does not pass 8190 comes back from the library's clamp. -/
theorem clamp_silu {d : ℕ} (h : d ≤ 8190) :
    Inst.Model.clamp 4095 ((d : ℤ) - 4095) + 4096 = ((d + 1 : ℕ) : ℤ) := by
  unfold Inst.Model.clamp
  have h' : (d : ℤ) ≤ 8190 := by exact_mod_cast h
  have h0 : (0 : ℤ) ≤ d := Int.natCast_nonneg d
  rw [max_eq_left (by omega), min_eq_left (by omega)]
  push_cast
  omega

/-- The first table's entry is siluWord at the array of powers. -/
theorem silu_get (p3 gcl : Bool) {t : ℕ} (ht : t < 65536) :
    (gateTables 8 4095 p3 gcl).1.getD t 0 = siluWord 8 4095 (expPowers 8 32768) t := by
  unfold gateTables
  dsimp only
  rw [Hd.getD_rangeMap _ _ _ ht, if_pos (show ((8 : ℕ) == 8) = true from rfl)]

/-- ENTRY t OF THE VERIFIER's TABLE SILU IS THE LIBRARY's, PLUS 4096. -/
theorem silu_word (p3 gcl : Bool) {t : ℕ} (ht : t < 65536) :
    (((gateTables 8 4095 p3 gcl).1.getD t 0 : ℕ) : ℤ) = refSILU (t : ℤ) + 4096 := by
  rw [silu_get p3 gcl ht, siluWord_eq]
  by_cases h : t < 32768
  · have ea : distS 8 t = min (32768 - t) 16384 := by
      unfold distS
      rw [if_pos h]
    generalize distS 8 t = a at ea ⊢
    have ha : a ≤ 16384 := by omega
    have ha0 : a ≠ 0 := by omega
    rw [powers_get 8 32768 (by omega), decide_eq_true h]
    obtain ⟨s1, s2, -⟩ := step_neg (all_ok ha) ha0
    rw [s1]
    unfold refSILU
    have ei : (min (max ((t : ℤ) - 2 ^ 15) (-2 ^ 14)) (2 ^ 14 - 1) + 2 ^ 14).toNat = 16384 - a := by
      omega
    rw [ei]
    exact (clamp_silu s2).symm
  · have ea : distS 8 t = min (t - 32768) 16383 := by
      unfold distS
      rw [if_neg h]
    generalize distS 8 t = a at ea ⊢
    have ha : a ≤ 16384 := by omega
    have ha0 : a ≠ 16384 := by omega
    rw [powers_get 8 32768 (by omega), decide_eq_false h]
    obtain ⟨s1, s2, -⟩ := step_pos (all_ok ha) ha0
    rw [s1]
    unfold refSILU
    have ei : (min (max ((t : ℤ) - 2 ^ 15) (-2 ^ 14)) (2 ^ 14 - 1) + 2 ^ 14).toNat = 16384 + a := by
      omega
    rw [ei]
    exact (clamp_silu s2).symm

/-- The second table's entry. -/
theorem fs_get {u : ℕ} (hu : u < 65536) :
    (gateTables 8 4095 true true).2.getD u 0 = fsWord true (expPowers 8 32768) u := by
  unfold gateTables
  dsimp only
  rw [if_pos rfl, Hd.getD_rangeMap _ _ _ hu]

/-- ENTRY u OF THE LOWER HALF OF THE VERIFIER's TABLE FS IS THE LIBRARY's SIGMOID. -/
theorem sig_word {u : ℕ} (hu : u < 32768) :
    (((gateTables 8 4095 true true).2.getD u 0 : ℕ) : ℤ) = refSIGM ((u : ℤ) + 2 ^ 14) := by
  have e : fsWord true (expPowers 8 32768) u = sigmoidAt (expPowers 8 32768) (u + 16384) := by
    unfold fsWord
    simp [hu]
  rw [fs_get (by omega), e, sigmoidAt_eq]
  have er : refSIGM ((u : ℤ) + 2 ^ 14) =
      ((16 * min (dec Inst.Model.Data.sigm 13 u) 4096 : ℕ) : ℤ) := by
    unfold refSIGM
    have ei : ((u : ℤ) + 2 ^ 14 - 2 ^ 14).toNat = u := by omega
    rw [ei]
    push_cast
    rfl
  rw [er]
  by_cases h : u + 16384 < 32768
  · rw [if_pos h, powers_get 8 32768 (by omega), decide_eq_true h]
    obtain ⟨-, -, s3⟩ := step_neg (all_ok (a := 32768 - (u + 16384)) (by omega)) (by omega)
    rw [s3]
    have ei : 16384 - (32768 - (u + 16384)) = u := by omega
    rw [ei]
  · rw [if_neg h, powers_get 8 32768 (by omega), decide_eq_false h]
    obtain ⟨-, -, s3⟩ := step_pos (all_ok (a := u + 16384 - 32768) (by omega)) (by omega)
    rw [s3]
    have ei : 16384 + (u + 16384 - 32768) = u := by omega
    rw [ei]

/-- The upper half of the table FS is the gate's clamp. -/
theorem fs_upper {u : ℕ} (h1 : 32768 ≤ u) (h2 : u < 65536) :
    (((gateTables 8 4095 true true).2.getD u 0 : ℕ) : ℤ) =
      Inst.Model.clamp 127 ((u : ℤ) - 49152) + 128 := by
  have e : fsWord true (expPowers 8 32768) u = clampHalf u := by
    unfold fsWord
    simp [Nat.not_lt.mpr h1]
  rw [fs_get h2, e]
  unfold clampHalf Inst.Model.clamp
  split <;> omega

#print axioms silu_word
#print axioms sig_word
#print axioms fs_upper

end Meaning.Gate
