-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/ReadsLiveOf.lean: THE SMALLNESS TEST: ONE TABLE A MATRIX, NONE OF WHOSE
WEIGHTS HAS THE VALUE 0, GIVES `readsLive` (Johnson/Desc/K8/Honest/LinkedFew.lean). A definition, a
statement and its proof. On plain data: no block, no prover. Lemmas; none of the library's goals.

  `LiveTable tl mu Fn`   Fn is a table of the closed list that is read on matrix mu (its vector is
      number 0 or 2); its length is not 0 and divides the matrix's number of rows of cells; none of
      its weights has the value 0
  `val_ne_of_word`   a word below the prime (okE: so is every output of addE and mulE) that is not
      the word 0 has a value other than 0
  `zzCol_at`   the column of a digit of row i of cells of a matrix
  **`readsLive_of`**   IF tl passes `tiesLaid` and each matrix has such a table: THEN `readsLive tl`
      says yes
The argument: a column is a digit of row i of cells of one matrix (the tiling); segment i / len of
the table covers it at place i % len, in one of its two windows alone; so what that read lays there
has the weight's value, or 2^10 times it.
By: mem_readsList (OnBytes/Tie/Pv/Tail/EndLoopsB.lean) · highDigit_val (EndClaims.lean) ·
gl_two_ne_zero (Cb/Pv/Head/NormGl.lean) · OnBytes.Slice.isZeroE_iff (OnBytes/Slice/ProgField.lean) ·
okE_add, okE_mul (Johnson/Top/H/P1Tie/Words.lean).
Limits. That a segment's list has such tables is not shown here. Nothing on any measure.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.LinkedFew

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open OnBytes.Tie.Pv.Tail.Port

/-- A table of the closed list that is read on matrix mu, none of whose weights has the value 0. -/
def LiveTable (tl : HTailF2) (mu : Nat) (Fn : HFun) : Prop :=
  Fn ∈ tl.funs.toList ∧ Fn.mat = mu ∧ (Fn.tree = 0 ∨ Fn.tree = 2) ∧ 0 < Fn.len ∧
    (tl.mats.getD mu {}).m % Fn.len = 0 ∧
    ∀ j, j < Fn.len → Reading.gl.val (Fn.phi.getD j zeroE) ≠ 0

/-- A word below the prime that is not the word 0 has a value other than 0. -/
theorem val_ne_of_word (w : E) (hok : OnBytes.okE w = true) (hz : isZeroE w = false) :
    Reading.gl.val w ≠ 0 := by
  intro h0
  have h1 : isZeroE w = true := (OnBytes.Slice.isZeroE_iff w hok).2 h0
  rw [hz] at h1
  cases h1

/-- The column of a digit of row i of cells of a matrix. -/
theorem zzCol_at (tl : HTailF2) (mu plane i : Nat) (hmu : mu < tl.NM) (hp : plane ≤ 1)
    (hi : i < (tl.mats.getD mu {}).m) :
    (tl.zzCol mu plane i).getD 0 = plane * tl.mz + tl.off.getD mu 0 + i := by
  unfold HTailF2.zzCol
  rw [if_pos (by rw [decide_eq_true hmu, decide_eq_true hp, decide_eq_true hi]; rfl)]
  rfl

/-- **One live table a matrix gives `readsLive`.** -/
theorem readsLive_of (tl : HTailF2) (hP : tiesLaid tl = true)
    (h : ∀ mu, mu < tl.NM → ∃ Fn, LiveTable tl mu Fn) : readsLive tl = true := by
  have hT := tiesLaid_spec tl hP
  unfold readsLive
  rw [List.all_eq_true]
  intro x hx
  have hx' := List.mem_range.1 hx
  obtain ⟨mu, plane, i, hmu, hp, hi, rfl⟩ : ∃ mu plane i, mu < tl.NM ∧ plane ≤ 1 ∧
      i < (tl.mats.getD mu {}).m ∧ x = plane * tl.mz + tl.off.getD mu 0 + i := by
    by_cases hlow : x < tl.mz
    · obtain ⟨mu, hmu, c1, c2⟩ := hT.cover x hlow
      exact ⟨mu, 0, x - tl.off.getD mu 0, hmu, by omega, by omega, by omega⟩
    · obtain ⟨mu, hmu, c1, c2⟩ := hT.cover (x - tl.mz) (by omega)
      exact ⟨mu, 1, x - tl.mz - tl.off.getD mu 0, hmu, by omega, by omega, by omega⟩
  obtain ⟨Fn, hFn, rfl, htree, hlen, hdiv, hlive⟩ := h mu hmu
  have hw := hT.within Fn.mat hmu
  have e1 : Fn.len * (i / Fn.len) + i % Fn.len = i := Nat.div_add_mod i Fn.len
  have e2 : i / Fn.len * Fn.len = Fn.len * (i / Fn.len) := Nat.mul_comm _ _
  have hj : i % Fn.len < Fn.len := Nat.mod_lt _ hlen
  have hsg : i / Fn.len < (tl.mats.getD Fn.mat {}).m / Fn.len := by
    rw [Nat.div_lt_iff_lt_mul hlen, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)]
    exact hi
  have hle : i / Fn.len * Fn.len + Fn.len ≤ (tl.mats.getD Fn.mat {}).m := by
    have h1 : (i / Fn.len + 1) * Fn.len ≤ (tl.mats.getD Fn.mat {}).m / Fn.len * Fn.len :=
      Nat.mul_le_mul_right _ hsg
    rw [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv), Nat.succ_mul] at h1
    exact h1
  have hs : i / Fn.len * Fn.len < (tl.mats.getD Fn.mat {}).m := by omega
  rw [List.any_eq_true]
  refine ⟨(Fn, i / Fn.len), (mem_readsList tl tl.funs Fn _).2 ⟨hFn, hmu, htree, hsg⟩, ?_⟩
  have hv : Reading.gl.val (readCoefE tl (Fn, i / Fn.len)
      (plane * tl.mz + tl.off.getD Fn.mat 0 + i)) ≠ 0 := by
    unfold readCoefE
    simp only []
    rw [zzCol_at tl Fn.mat 0 _ hmu (Nat.zero_le _) hs,
      zzCol_at tl Fn.mat 1 _ hmu (Nat.le_refl _) hs, Reading.gl.add, highDigit_val Reading.gl]
    have hpc : plane = 0 ∨ plane = 1 := by omega
    rcases hpc with rfl | rfl
    · rw [if_pos (by omega), if_neg (by omega), Reading.gl.zero, mul_zero, add_zero]
      have e3 : 0 * tl.mz + tl.off.getD Fn.mat 0 + i -
          (0 * tl.mz + tl.off.getD Fn.mat 0 + i / Fn.len * Fn.len) = i % Fn.len := by omega
      rw [e3]
      exact hlive _ hj
    · rw [if_neg (by omega), if_pos (by omega), Reading.gl.zero, zero_add]
      have e3 : 1 * tl.mz + tl.off.getD Fn.mat 0 + i -
          (1 * tl.mz + tl.off.getD Fn.mat 0 + i / Fn.len * Fn.len) = i % Fn.len := by omega
      rw [e3]
      exact mul_ne_zero (pow_ne_zero _ Cb.Pv.Head.gl_two_ne_zero) (hlive _ hj)
  cases hz : isZeroE (readCoefE tl (Fn, i / Fn.len)
      (plane * tl.mz + tl.off.getD Fn.mat 0 + i)) with
  | false => rfl
  | true =>
    exact absurd ((OnBytes.Slice.isZeroE_iff _ (Part.MaskedSum.okE_add _ _)).1 hz) hv

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.val_ne_of_word
#print axioms VerifiableInference.Desc.First.K8.Honest.zzCol_at
#print axioms VerifiableInference.Desc.First.K8.Honest.readsLive_of
