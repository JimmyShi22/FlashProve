-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Runnable/Small.lean: the helpers of the array program (ArrayProgram,
IntegerModel/Runnable/ArrayModel.lean), its norm and its hidden unit compared with the library's
(Inst/Model/Program.lean), and its rotary step written out over the library's tables C, S.
-/
import IntegerModel.Runnable.Tools
import IntegerModel.Runnable.Defs

set_option autoImplicit false

namespace IntegerModel.Runnable

open Inst.Model

/-! ## Helpers -/

theorem shiftRound_eq (a : ℤ) (k : ℕ) : ArrayProgram.shiftRound a k = rhu a k := rfl
theorem clamp_eq (c a : ℤ) : ArrayProgram.clamp c a = clamp c a := rfl
theorem row_eq (n : ℕ) (f : ℕ → ℤ) : ArrayProgram.row n f = tabl n f := rfl

theorem fits16_iff (a : ℤ) : ArrayProgram.fits16 a = true ↔ Fits16 a := by
  unfold ArrayProgram.fits16 Fits16
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

theorem dot_eq (a : Array ℤ) (w : ℕ → ℤ) : ArrayProgram.dot a w = dot a.size (fun j => a[j]!) w :=
  foldl_sum (fun j => a[j]! * w j) a.size

theorem dot_tabl (n : ℕ) (f w : Vec) : ArrayProgram.dot (tabl n f) w = dot n f w := by
  rw [dot_eq, tabl_size]
  exact Finset.sum_congr rfl fun j hj => by
    show (tabl n f)[j]! * w j = f j * w j
    rw [tabl_get f (Finset.mem_range.1 hj)]

theorem dot_congr {n : ℕ} {a w w' : Vec} (h : ∀ j < n, w j = w' j) : dot n a w = dot n a w' :=
  Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.1 hj)]

theorem argmax_eq (a : Array ℤ) :
    ArrayProgram.argmaxFirst a = argTo (fun j => a[j]!) (a.size - 1) :=
  foldl_arg' (fun j => a[j]!) a.size

theorem argmax_tabl (n : ℕ) (f : Vec) : ArrayProgram.argmaxFirst (tabl n f) = argTo f (n - 1) := by
  rw [argmax_eq, tabl_size]
  cases n with
  | zero => rfl
  | succ n => exact argTo_congr n fun j hj => tabl_get f (Nat.lt_succ_of_le hj)

theorem at2_tabl {T n : ℕ} (F : ℕ → Vec) {i c : ℕ} (hi : i < T) (hc : c < n) :
    ArrayProgram.at2 (tabl T fun i => tabl n (F i)) i c = F i c := by
  unfold ArrayProgram.at2
  rw [tabl_get _ hi, tabl_get _ hc]

theorem isqrt_eq (n : ℕ) : ArrayProgram.isqrt n = Nat.sqrt n := bits_sqrt_eq n

theorem checked_is (n : ℕ) (f : Vec) :
    Is (ArrayProgram.checked (tabl n f)) (∀ c < n, Fits16 (f c))
      (tabl n fun c => clamp 2047 (f c)) := by
  have h :=
    Is.ofBool ((tabl n f).all ArrayProgram.fits16) ((tabl n f).map (ArrayProgram.clamp 2047))
  exact (h.iff ((tabl_all _ _ _).trans (forall₂_congr fun c _ => fits16_iff _))).val
    fun _ => tabl_map _ _ _

theorem project_tabl (d : ℕ) (x : Vec) (W : Mat) (n k : ℕ) :
    ArrayProgram.project (tabl d x) W n k = tabl n fun c => rhu (dot d x fun j => W j c) k :=
  tabl_congr fun c _ => by rw [dot_tabl]; rfl

/-! ## The norm -/

theorem rmsNorm_is (np : NormPar) (d : ℕ) (x : Vec) :
    Is (ArrayProgram.rmsNorm (normOf np) (tabl d x))
      (NORM.OK np d x) (tabl d (NORM.out np d x)) := by
  have hss : (tabl d x).foldl (fun s v => s + v ^ 2) 0 = NORM.V d x := by
    rw [tabl_foldl]
    exact foldl_sum (fun j => x j ^ 2) d
  have hsig : ((ArrayProgram.isqrt (NORM.V d x + np.eps).toNat : ℕ) : ℤ) = NORM.sig np d x := by
    rw [isqrt_eq]; rfl
  have hw : (tabl d x).map (fun v =>
        ArrayProgram.shiftRound (v * ((2 ^ np.M + NORM.sig np d x / 2) / NORM.sig np d x)) np.K) =
      tabl d (NORM.yw np d x) := tabl_map _ _ _
  have e : ArrayProgram.rmsNorm (normOf np) (tabl d x) =
      if (decide (NORM.V d x + np.eps < 2 ^ 78) &&
            (tabl d (NORM.yw np d x)).all ArrayProgram.fits16) = true then
        some ((tabl d (NORM.yw np d x)).map (ArrayProgram.clamp 2047))
      else none := by
    rw [← hw, ← hsig, ← hss]
    rfl
  rw [e]
  have h := Is.ofBool
    (decide (NORM.V d x + np.eps < 2 ^ 78) && (tabl d (NORM.yw np d x)).all ArrayProgram.fits16)
    ((tabl d (NORM.yw np d x)).map (ArrayProgram.clamp 2047))
  refine (h.iff ?_).val fun _ => tabl_map _ _ _
  rw [Bool.and_eq_true, decide_eq_true_eq, tabl_all]
  exact and_congr Iff.rfl (forall₂_congr fun c _ => fits16_iff _)

/-! ## One hidden unit -/

theorem unit_is (t : ArrayProgram.Tables) (tb : Tables) (hs : t.silu = tb.SILU)
    (d : ℕ) (z wg wu : Vec) (k k' : ℕ) {wg' wu' : Vec}
    (hg : ∀ j < d, wg' j = wg j) (hu : ∀ j < d, wu' j = wu j) :
    Is (ArrayProgram.unit t (tabl d z) wg' wu' k k')
      (UNIT.OK d z wg wu k k') (UNIT.hh tb d z wg wu k k') := by
  have e : ArrayProgram.unit t (tabl d z) wg' wu' k k' =
      if (decide (-2 ^ 14 ≤ UNIT.gh d z wg k) && decide (UNIT.gh d z wg k < 2 ^ 14) &&
            ArrayProgram.fits16 (UNIT.up d z wu k')) = true then
        some (UNIT.hh tb d z wg wu k k')
      else none := by
    unfold ArrayProgram.unit
    rw [dot_tabl, dot_tabl, dot_congr hg, dot_congr hu, hs]
    rfl
  rw [e]
  refine (Is.ofBool _ _).iff ?_
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, fits16_iff]
  exact Iff.rfl

/-! ## The rotary step -/

theorem succ_lt_of_even {ch n c : ℕ} (h2 : 2 ∣ ch) (hn : ch ∣ n)
    (hc : c < n) (he : c % ch % 2 = 0) : c + 1 < n := by
  obtain ⟨a, rfl⟩ := hn
  have hch : 0 < ch := by
    rcases Nat.eq_zero_or_pos ch with h | h
    · subst h; simp at hc
    · exact h
  have hq : c / ch < a := Nat.div_lt_of_lt_mul hc
  have h1 : ch * (c / ch + 1) ≤ ch * a := Nat.mul_le_mul_left _ hq
  rw [Nat.mul_succ] at h1
  have h3 := Nat.div_add_mod c ch
  have h4 := Nat.mod_lt c hch
  omega

/-- the program's rotary step on a row of whole heads, under the hypotheses below -/
theorem rotate_tabl (S : ArrayProgram.Shape) (t : ArrayProgram.Tables) (tb : Tables)
    (L : ℕ) (rows : ℤ) (hT : TabRel t tb L rows) (h2 : 2 ∣ S.headDim) (i n : ℕ)
    (hn : S.headDim ∣ n) (F : Vec) :
    ArrayProgram.rotate S t L i (tabl n F) = tabl n fun c =>
      if c % S.headDim % 2 = 0 then
        tb.C L i (c % S.headDim / 2) * F c - tb.S L i (c % S.headDim / 2) * F (c + 1)
      else tb.S L i (c % S.headDim / 2) * F (c - 1) + tb.C L i (c % S.headDim / 2) * F c := by
  unfold ArrayProgram.rotate
  rw [tabl_size]
  refine tabl_congr fun c hc => ?_
  rw [← hT.cos, ← hT.sin]
  by_cases he : c % S.headDim % 2 = 0
  · rw [if_pos he]
    show (if (c % S.headDim % 2 == 0) = true then _ else _) = _
    rw [if_pos (by rw [he]; rfl), tabl_get F hc, tabl_get F (succ_lt_of_even h2 hn hc he)]
  · rw [if_neg he]
    show (if (c % S.headDim % 2 == 0) = true then _ else _) = _
    rw [if_neg (by simpa using he), tabl_get F hc, tabl_get F (lt_of_le_of_lt (Nat.sub_le c 1) hc)]

end IntegerModel.Runnable
