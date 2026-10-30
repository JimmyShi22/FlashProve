-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/GenTie.lean: THE PROGRAM's GENERATOR ROW, READ, IS THE LIBRARY's GENERATOR
MATRIX (OnBytes/Slice/LinkAt.lean: genOf, at the format's record of the program's code:
OnBytes/Slice/ProgCodes.lean: codeOf): entry by entry the powers of the position's point, the tail's
entries first.

  gl_ofF          a word of the base field, lifted by the program and read.
  bitsK_squares, bitsK_gen   the product of a point's repeated squares at a number's bits is a
                  power.
  gen_msg, gen_tail   the two sorts of entries.
  full2           the full message that a vector holds, on ONE range of places: the tail first.
  mulVec_tie      the library's matrix applied to full2 is the program's row, read, applied to the
                  full message on the sum of the two ranges (fullOf).

What is not claimed. For codes of at most 2 ^ 32 positions. Nothing on distances or lists. No
soundness of a verifier.

-/
import Johnson.Desc.K14.Law.TypedIx
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain

/-- A word of the base field, lifted by the program and read, is the word read and lifted. -/
theorem gl_ofF (a : F) :
    OnBytes.Model.Reading.gl.val (OnBytes.ofF a) = algebraMap Cb.Gl.F Cb.Gl.E (toF a) :=
  toE_ofF a

/-- The product of repeated squares at a number's bits is a power. -/
theorem bitsK_squares : ∀ (n : Nat) (z : F) (j : Nat),
    bitsK ((squaresOf n z).map fun a => OnBytes.Model.Reading.gl.val (OnBytes.ofF a)) j =
      algebraMap Cb.Gl.F Cb.Gl.E (toF z ^ (j % 2 ^ n))
  | 0, z, j => by simp [squaresOf_zero, bitsK, Nat.mod_one]
  | n + 1, z, j => by
    have split : j % 2 ^ (n + 1) = j % 2 + 2 * (j / 2 % 2 ^ n) := by
      rw [pow_succ', Nat.mod_mul]
    rw [squaresOf_succ, List.map_cons, bitsK, bitsK_squares n, toF_mulF, split, pow_add, pow_mul,
      map_mul, gl_ofF, ← pow_two]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h]

/-- The factors of a generator row, read, at a number below the count that they spell. -/
theorem bitsK_gen (c : OnBytes.Code) (x k n j : Nat) (hn : n ≤ 2 ^ k) (hd : n ≤ 2 ^ c.logDim)
    (hj : j < n) :
    bitsK (((generatorAt c x).f.map fun a =>
      OnBytes.Model.Reading.gl.val (OnBytes.ofF a)).take k) j =
      algebraMap Cb.Gl.F Cb.Gl.E (toF (codePoint c.logN x) ^ j) := by
  have hm : n ≤ 2 ^ min k c.logDim := by
    rcases Nat.le_total k c.logDim with h | h
    · rw [Nat.min_eq_left h]; exact hn
    · rw [Nat.min_eq_right h]; exact hd
  rw [← List.map_take, generatorAt_f, take_squaresOf, bitsK_squares,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hj hm)]

/-- An entry at a place of the message. -/
theorem gen_msg (S : FoldeqShape) (ha : S.index.code.logN ≤ 32)
    (x : Fin (2 ^ S.index.code.logN)) (j : Fin S.index.code.ell) :
    genMatrix OnBytes.Model.Reading.gl S x (.inl j) =
      genOf (codeOf S.index.code) x (Fin.natAdd S.index.code.r j) := by
  show OnBytes.Model.Reading.gl.val (OnBytes.ofF (generatorAt S.index.code x.val).messageScale) *
      bitsK (((generatorAt S.index.code x.val).f.map fun a =>
        OnBytes.Model.Reading.gl.val (OnBytes.ofF a)).take S.index.code.logEll) j.val =
    algebraMap Cb.Gl.F Cb.Gl.E
      (toF (Fmt.M1.point S.index.code.logN x.val) ^ (S.index.code.r + j.val))
  rw [gl_ofF, toF_messageScale _ _ (Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt),
    bitsK_gen S.index.code x.val S.index.code.logEll S.index.code.ell j.val
      (le_two_pow_ceilLog2 _)
      (ell_le_logDim _) j.isLt,
    toF_codePoint _ _ ha x.isLt, ← map_mul, ← pow_add]

/-- An entry at a place of the tail. -/
theorem gen_tail (S : FoldeqShape) (ha : S.index.code.logN ≤ 32)
    (x : Fin (2 ^ S.index.code.logN)) (q : Fin S.index.code.r) :
    genMatrix OnBytes.Model.Reading.gl S x (.inr q) =
      genOf (codeOf S.index.code) x (Fin.castAdd S.index.code.ell q) := by
  show OnBytes.Model.Reading.gl.val (OnBytes.ofF (generatorAt S.index.code x.val).tailScale) *
      bitsK (((generatorAt S.index.code x.val).f.map fun a =>
        OnBytes.Model.Reading.gl.val (OnBytes.ofF a)).take S.index.code.logR) q.val =
    algebraMap Cb.Gl.F Cb.Gl.E (toF (Fmt.M1.point S.index.code.logN x.val) ^ q.val)
  rw [gl_ofF, toF_tailScale, map_one, one_mul,
    bitsK_gen S.index.code x.val S.index.code.logR S.index.code.r q.val
      (le_two_pow_ceilLog2 _)
      (r_le_logDim _) q.isLt,
    toF_codePoint _ _ ha x.isLt]

/-- The full message that a vector holds, on one range of places: the tail first. -/
def full2 (S : FoldeqShape) (U : Nat → Cb.Gl.E) :
    Fin (S.index.code.r + S.index.code.ell) → Cb.Gl.E :=
  Fin.addCases (fun q => U (S.tailFirst + q.val)) fun j => U j.val

/-- **The library's matrix applied to the full message is the program's row, read, applied to
it.** -/
theorem mulVec_tie (S : FoldeqShape) (ha : S.index.code.logN ≤ 32) (U : Nat → Cb.Gl.E)
    (x : Fin (2 ^ S.index.code.logN)) :
    (genOf (codeOf S.index.code)).mulVec (full2 S U) x =
      (genMatrix OnBytes.Model.Reading.gl S).mulVec (fullOf S U) x := by
  show ∑ k : Fin (S.index.code.r + S.index.code.ell),
      genOf (codeOf S.index.code) x k * full2 S U k =
    ∑ k : Fin S.index.code.ell ⊕ Fin S.index.code.r,
      genMatrix OnBytes.Model.Reading.gl S x k * fullOf S U k
  rw [Fin.sum_univ_add, Fintype.sum_sum_type, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [gen_msg S ha x j]
    show _ * full2 S U (Fin.natAdd S.index.code.r j) = _ * U j.val
    unfold full2
    rw [Fin.addCases_right]
    rfl
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [gen_tail S ha x q]
    show _ * full2 S U (Fin.castAdd S.index.code.ell q) = _ * U (S.tailFirst + q.val)
    unfold full2
    rw [Fin.addCases_left]
    rfl

end Desc.K14.Law
