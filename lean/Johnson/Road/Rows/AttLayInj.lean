-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttLayInj.lean: within a table of an attention sub-proof, two late entries with
different names have different places.

The dictionary between names of late entries and entries of the verifier's vector of tables sends
the name (T, r) to the entry number: where T begins, plus the place placeAtt of r in T. It can be
the address of a late entry only if it is one-to-one. This file shows the half that the shape
decides: for one table, placeAtt is one-to-one on the listed names (Cb/Pv/Att/End/Names.lean). The
proof goes through the cells: the place fixes the address of the entry's first cell
(Johnson/Road/Rows/AttLayNames.lean), and no two valid cells have one address
(Johnson/Road/Lane5AttInj.lean).

Main theorems: place_inj: for all 21 tables.

What the theorem takes as given: L5.Laid and Sizes. L5.Laid: from what shape returns and at least
one part of "as", which config tests (laid_of_shape); for the record that shapeHid returns no
theorem gives it yet. Sizes: sizes_of_shape, sizes_of_hid.

What is not claimed. The other half: that the 21 tables do not overlap in the vector. That is a fact
on the run of the verifier's function tables; it is tried at the small configuration in
Johnson/Road/Rows/TestAttPlaces.lean.


-/
import Johnson.Road.Rows.AttLayNames
import Johnson.Road.Lane5AttInj

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

open OnBytes.Attention (Shape)
open Inst.Model.AttSeg (Raw)
open Cb.Pv.Att.End (AttTab namesOf name_valid of_mem_row of_mem_long of_mem_col)

variable {S : Shape}

/-- A listed name of a table on ah is its own cell at position 0. -/
theorem row_first (n : ℕ) (mk : ℕ → ℕ → ℕ → Raw) (hmk : ∀ a b c, (mk a b c).atPos 0 = mk a b c)
    {r : Raw} (h : r ∈ Cb.Pv.Att.End.rowNames (L5.dimOf S) n mk) : r.atPos 0 = r := by
  obtain ⟨a, b, c, -, -, -, rfl⟩ := of_mem_row h
  exact hmk a b c

/-- A listed name of a table on blocks of features is its own cell number 0. -/
theorem long_first (n cnt : ℕ) (mk : ℕ → ℕ → ℕ → Raw)
    (hmk : ∀ a b c x, (((mk a b c).addN x).addN 0).atPos 0 = (mk a b c).addN x) {r : Raw}
    (h : r ∈ Cb.Pv.Att.End.longNames (L5.dimOf S) S.ls n cnt mk) : (r.addN 0).atPos 0 = r := by
  obtain ⟨a, b, c, x, -, -, -, -, rfl⟩ := of_mem_long h
  exact hmk a b c _

/-- Within a table the places are one-to-one. -/
theorem place_inj (La : L5.Laid S) (Z : Sizes S) {T : AttTab} {r r' : Raw}
    (h : r ∈ namesOf (L5.dimOf S) S.ls S.cf.lmS T) (h' : r' ∈ namesOf (L5.dimOf S) S.ls S.cf.lmS T)
    (e : placeAtt S T r = placeAtt S T r') : r = r' := by
  have hM : S.cf.lmS ≤ S.nM := lmS_le_nM S La.norm Z
  have elM : (L5.dimOf S).lM = S.nM := La.norm.nM.symm
  have elD : (L5.dimOf S).lD = S.nD := La.norm.nD.symm
  have hT : 0 < S.T := by rw [Z.T]; exact Nat.two_pow_pos _
  have hTD : 0 < (L5.dimOf S).T := by rw [La.T]; exact hT
  have hv : ∀ {x : Raw}, x ∈ namesOf (L5.dimOf S) S.ls S.cf.lmS T → x.Valid (L5.dimOf S) :=
    fun hx => name_valid hTD Z.ls (by rw [elM]; exact hM) (by rw [elD]; exact Z.lmS) hx
  have hk : 0 < 2 ^ S.ls * S.T := Nat.mul_pos (Nat.two_pow_pos _) hT
  -- the three kinds
  have row : T ∈ rowTabs → r.atPos 0 = r → r'.atPos 0 = r' → r = r' := by
    intro hT' f f'
    have a := names_row S hT' h 0
    have a' := names_row S hT' h' 0
    rw [e, ← a', f, f'] at a
    exact L5.addrA_inj_laid La (hv h) (hv h') a
  have qa : T ∈ qaTabs → (r.addN 0).atPos 0 = r → (r'.addN 0).atPos 0 = r' → r = r' := by
    intro hT' f f'
    have a := names_qa S La.norm Z hT' h hk
    have a' := names_qa S La.norm Z hT' h' hk
    rw [Nat.zero_div, Nat.zero_mod] at a a'
    rw [e, ← a', f, f'] at a
    exact L5.addrA_inj_laid La (hv h) (hv h') a
  have col : T ∈ colTabs → r = r' := by
    intro hT'
    have a := names_col S La.norm Z hT' h (Nat.two_pow_pos S.cf.lmS)
    have a' := names_col S La.norm Z hT' h' (Nat.two_pow_pos S.cf.lmS)
    rw [e, ← a'] at a
    have f : ∀ x : Raw, x ∈ namesOf (L5.dimOf S) S.ls S.cf.lmS T → x.addX 0 = x := by
      intro x hx
      cases x <;> rfl
    rw [f r h, f r' h'] at a
    exact L5.addrA_inj_laid La (hv h) (hv h') a
  cases T with
  | tA => exact col (by simp [colTabs])
  | tVM => exact col (by simp [colTabs])
  | tVD => exact col (by simp [colTabs])
  | tMm =>
    exact row (by simp [rowTabs])
      (row_first 4 (fun k b g => .mx k b g 0) (fun _ _ _ => rfl) h)
      (row_first 4 (fun k b g => .mx k b g 0) (fun _ _ _ => rfl) h')
  | tMd =>
    exact row (by simp [rowTabs])
      (row_first 4 (fun k b g => .mx k b g 0) (fun _ _ _ => rfl) h)
      (row_first 4 (fun k b g => .mx k b g 0) (fun _ _ _ => rfl) h')
  | hT =>
    exact row (by simp [rowTabs])
      (row_first 4 (fun k b g => .mx k b g 0) (fun _ _ _ => rfl) h)
      (row_first 4 (fun k b g => .mx k b g 0) (fun _ _ _ => rfl) h')
  | hW =>
    exact row (by simp [rowTabs])
      (row_first 4 (fun k b g => .den k b g 0) (fun _ _ _ => rfl) h)
      (row_first 4 (fun k b g => .den k b g 0) (fun _ _ _ => rfl) h')
  | hE =>
    exact row (by simp [rowTabs])
      (row_first 4 (fun k b g => .den k b g 0) (fun _ _ _ => rfl) h)
      (row_first 4 (fun k b g => .den k b g 0) (fun _ _ _ => rfl) h')
  | hX =>
    exact row (by simp [rowTabs])
      (row_first _ (fun k b g => .ib k b g 0) (fun _ _ _ => rfl) h)
      (row_first _ (fun k b g => .ib k b g 0) (fun _ _ _ => rfl) h')
  | hPi =>
    exact row (by simp [rowTabs])
      (row_first _ (fun k b g => .ib k b g 0) (fun _ _ _ => rfl) h)
      (row_first _ (fun k b g => .ib k b g 0) (fun _ _ _ => rfl) h')
  | hR2 =>
    exact row (by simp [rowTabs])
      (row_first _ (fun k b g => .ib k b g 0) (fun _ _ _ => rfl) h)
      (row_first _ (fun k b g => .ib k b g 0) (fun _ _ _ => rfl) h')
  | qO =>
    exact qa (by simp [qaTabs])
      (long_first 2 _ (fun k b g => .out k b g 0 0) (fun _ _ _ _ => rfl) h)
      (long_first 2 _ (fun k b g => .out k b g 0 0) (fun _ _ _ _ => rfl) h')
  | tQm =>
    exact qa (by simp [qaTabs])
      (long_first 2 _ (fun k b g => .qry k b g 0 0) (fun _ _ _ _ => rfl) h)
      (long_first 2 _ (fun k b g => .qry k b g 0 0) (fun _ _ _ _ => rfl) h')
  | tQd =>
    exact qa (by simp [qaTabs])
      (long_first 2 _ (fun k b g => .qry k b g 0 0) (fun _ _ _ _ => rfl) h)
      (long_first 2 _ (fun k b g => .qry k b g 0 0) (fun _ _ _ _ => rfl) h')
  | qF =>
    exact qa (by simp [qaTabs])
      (long_first 2 _ (fun k b g => .qry k b g 0 0) (fun _ _ _ _ => rfl) h)
      (long_first 2 _ (fun k b g => .qry k b g 0 0) (fun _ _ _ _ => rfl) h')
  | tKm =>
    exact qa (by simp [qaTabs])
      (long_first 2 _ (fun k b g => .key k b g 0 0) (fun _ _ _ _ => rfl) h)
      (long_first 2 _ (fun k b g => .key k b g 0 0) (fun _ _ _ _ => rfl) h')
  | tKd =>
    exact qa (by simp [qaTabs])
      (long_first 2 _ (fun k b g => .key k b g 0 0) (fun _ _ _ _ => rfl) h)
      (long_first 2 _ (fun k b g => .key k b g 0 0) (fun _ _ _ _ => rfl) h')
  | qKx =>
    exact qa (by simp [qaTabs])
      (long_first 2 _ (fun k b g => .key k b g 0 0) (fun _ _ _ _ => rfl) h)
      (long_first 2 _ (fun k b g => .key k b g 0 0) (fun _ _ _ _ => rfl) h')
  | qVM =>
    exact qa (by simp [qaTabs])
      (long_first 2 _ (fun k b g => .val k b g 0 0) (fun _ _ _ _ => rfl) h)
      (long_first 2 _ (fun k b g => .val k b g 0 0) (fun _ _ _ _ => rfl) h')
  | qVD =>
    exact qa (by simp [qaTabs])
      (long_first 2 _ (fun k b g => .val k b g 0 0) (fun _ _ _ _ => rfl) h)
      (long_first 2 _ (fun k b g => .val k b g 0 0) (fun _ _ _ _ => rfl) h')
  | tO =>
    have a := names_tO S La.norm Z h hk
    have a' := names_tO S La.norm Z h' hk
    rw [Nat.zero_div, Nat.zero_mod] at a a'
    have f : ∀ x : Raw, x ∈ namesOf (L5.dimOf S) S.ls S.cf.lmS .tO → (x.addN 0).atPos 0 = x := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact long_first 1 _ (fun _ b g => .qh b g 0 0) (fun _ _ _ _ => rfl) hx
      · exact long_first 1 _ (fun _ b g => .qh' b g 0 0) (fun _ _ _ _ => rfl) hx
    rw [e, ← a', f r h, f r' h'] at a
    exact L5.addrA_inj_laid La (hv h) (hv h') a

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.place_inj
