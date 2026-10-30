-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/GateLut.lean: the lookup's tables FL and FS of a layer sub-proof, at the stored
example's numbers, are the library's, in the sense of Hd.IsLut (Johnson/Road/HeadTabs.lean:116): as
many rows; row by row the verifier's word is the residue of a natural number that is the library's
entry; so is the padding row's.

  tauFLw, tauFSw: the two arrays, in the letters of the layers' layout
    (OnBytes/Model/LayerLayout.lean, the fields tauFL and tauFS).
  isLut_FL, isLut_FS. Beside isLut_R16, isLut_R8, isLut_FC these are all kinds of calls
    of a layer sub-proof.
From silu_word, sig_word, fs_upper (Johnson/Meaning/GateRows.lean).
-/
import Johnson.Meaning.GateRows

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.Gate

open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (gateTables rowFS)
open Inst.Model (tbRef refSILU refSIGM FL FS)

/-- The array of the table FL. -/
def tauFLw : Array UInt64 :=
  (Array.range 65536).map fun t => (t + (gateTables 8 4095 true true).1.getD t 0 * 2 ^ 28).toUInt64

/-- The array of the table FS. -/
def tauFSw : Array UInt64 :=
  (Array.range 65536).map fun t => (rowFS true (gateTables 8 4095 true true).2 t).toUInt64

/-- A word of the table SILU has at most 13 bits. -/
theorem silu_le {t : ℕ} (ht : t < 65536) : (gateTables 8 4095 true true).1.getD t 0 ≤ 8191 := by
  have h := silu_word true true ht
  have b := (Inst.Model.clamp_bounds (c := 4095) (by norm_num)
    ((Inst.Model.dec Inst.Model.Data.silu 13
      (min (max ((t : ℤ) - 2 ^ 15) (-2 ^ 14)) (2 ^ 14 - 1) + 2 ^ 14).toNat : ℤ) - 4095)).2
  have e : refSILU (t : ℤ) ≤ 4095 := b
  omega

/-- Row u of FL. -/
theorem rowFL_eq {u : ℕ} (hu : u < 65536) :
    ((u + (gateTables 8 4095 true true).1.getD u 0 * 2 ^ 28 : ℕ) : ℤ) = (FL tbRef).row u := by
  have h := silu_word true true hu
  show _ = (u : ℤ) + 2 ^ 28 * (refSILU (u : ℤ) + 2 ^ 12)
  push_cast
  rw [h]
  ring

theorem isLut_FL {c : Call} (hτ : c.tau = some tauFLw) (hk : c.k = 16) (h0 : c.t0 = 32768) :
    Hd.IsLut c (FL tbRef) where
  rows := by rw [hk]; rfl
  row u hu := by
    have hu' : u < 65536 := hu
    have hb := silu_le hu'
    refine ⟨u + (gateTables 8 4095 true true).1.getD u 0 * 2 ^ 28, ?_, rowFL_eq hu'⟩
    rw [Hd.tauAt_some hτ]
    unfold tauFLw
    rw [Hd.getD_map_rangeT _ _ _ _ hu']
    exact Hd.word_eq_fOfNat (by omega)
  pad := by
    have hb := silu_le (t := 32768) (by norm_num)
    refine ⟨32768 + (gateTables 8 4095 true true).1.getD 32768 0 * 2 ^ 28, ?_, ?_⟩
    · rw [Hd.tauAt_some hτ, h0]
      unfold tauFLw
      rw [Hd.getD_map_rangeT _ _ _ _ (by norm_num)]
      exact Hd.word_eq_fOfNat (by omega)
    · rw [rowFL_eq (by norm_num)]
      show ((32768 : ℕ) : ℤ) + 2 ^ 28 * (refSILU ((32768 : ℕ) : ℤ) + 2 ^ 12) =
        2 ^ 15 + 2 ^ 28 * (refSILU (2 ^ 15) + 2 ^ 12)
      norm_num

/-- Row u of FS, and a bound. -/
theorem rowFS_eq {u : ℕ} (hu : u < 65536) :
    ((rowFS true (gateTables 8 4095 true true).2 u : ℕ) : ℤ) = (FS tbRef).row u ∧
      rowFS true (gateTables 8 4095 true true).2 u < 2 ^ 41 := by
  by_cases h : u < 32768
  · have w := sig_word h
    have e : rowFS true (gateTables 8 4095 true true).2 u =
        u + (gateTables 8 4095 true true).2.getD u 0 * 2 ^ 17 := by
      unfold rowFS
      rw [if_neg (by simp [h])]
    have r : (FS tbRef).row u = (u : ℤ) + 2 ^ 17 * refSIGM ((u : ℤ) + 2 ^ 14) := by
      show (if u < 2 ^ 15 then (u : ℤ) + 2 ^ 17 * refSIGM ((u : ℤ) + 2 ^ 14) else _) = _
      rw [if_pos (show u < 2 ^ 15 from h)]
    have b : refSIGM ((u : ℤ) + 2 ^ 14) ≤ 65536 := by
      unfold refSIGM
      have := min_le_right
        (Inst.Model.dec Inst.Model.Data.sigm 13 ((u : ℤ) + 2 ^ 14 - 2 ^ 14).toNat : ℤ) 4096
      omega
    rw [e, r]
    refine ⟨?_, by omega⟩
    push_cast
    rw [w]
    ring
  · have h1 : 32768 ≤ u := Nat.not_lt.mp h
    have w := fs_upper h1 hu
    have e : rowFS true (gateTables 8 4095 true true).2 u =
        u + (gateTables 8 4095 true true).2.getD u 0 * 2 ^ 28 + 2 ^ 40 := by
      unfold rowFS
      rw [if_pos (by simp [h1])]
    have r : (FS tbRef).row u =
        (u : ℤ) + 2 ^ 28 * (Inst.Model.clamp 127 ((u : ℤ) - 49152) + 128) + 2 ^ 40 := by
      show (if u < 2 ^ 15 then _ else
        (u : ℤ) + 2 ^ 28 * (Inst.Model.clamp 127 ((u : ℤ) - 49152) + 128) + 2 ^ 40) = _
      rw [if_neg (show ¬ u < 2 ^ 15 from h)]
    have b := (Inst.Model.clamp_bounds (c := 127) (by norm_num) ((u : ℤ) - 49152)).2
    rw [e, r]
    refine ⟨?_, by omega⟩
    push_cast
    rw [w]
    ring

theorem isLut_FS {c : Call} (hτ : c.tau = some tauFSw) (hk : c.k = 16) (h0 : c.t0 = 32768) :
    Hd.IsLut c (FS tbRef) where
  rows := by rw [hk]; rfl
  row u hu := by
    have hu' : u < 65536 := hu
    obtain ⟨e, b⟩ := rowFS_eq hu'
    refine ⟨rowFS true (gateTables 8 4095 true true).2 u, ?_, e⟩
    rw [Hd.tauAt_some hτ]
    unfold tauFSw
    rw [Hd.getD_map_rangeT _ _ _ _ hu']
    exact Hd.word_eq_fOfNat (by omega)
  pad := by
    obtain ⟨e, b⟩ := rowFS_eq (u := 32768) (by norm_num)
    refine ⟨rowFS true (gateTables 8 4095 true true).2 32768, ?_, ?_⟩
    · rw [Hd.tauAt_some hτ, h0]
      unfold tauFSw
      rw [Hd.getD_map_rangeT _ _ _ _ (by norm_num)]
      exact Hd.word_eq_fOfNat (by omega)
    · rw [e]
      show (if (32768 : ℕ) < 2 ^ 15 then
          ((32768 : ℕ) : ℤ) + 2 ^ 17 * tbRef.SIGM (((32768 : ℕ) : ℤ) + 2 ^ 14)
        else ((32768 : ℕ) : ℤ) +
          2 ^ 28 * (Inst.Model.clamp 127 (((32768 : ℕ) : ℤ) - 49152) + 128) + 2 ^ 40) =
        2 ^ 15 + 2 ^ 28 * (Inst.Model.clamp 127 (2 ^ 15 - 49152) + 128) + 2 ^ 40
      rw [if_neg (by norm_num)]
      norm_num

#print axioms isLut_FL
#print axioms isLut_FS

end Meaning.Gate
