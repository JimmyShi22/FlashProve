-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Law/CubeKitY.lean: CONDITIONAL. Two definitions, and statements with their
proofs.

What is here. Tools for the law on `polyInY`: the program's lists of coefficients read as
polynomials; its differences; its loop.

  `polyOf_addP`, `polyOf_scale`, `polyOf_mulP`   sums, multiples and products of lists
  `addP_length`, `mulP_two_length`, `diffs_length`   lengths
  `diffs_read`   the program's differences read as `dseq`
  `stepY`, `polyInY_eq`   the loop's step by name
  `fold_poly`, `fold_length`   what the loop returns, as a polynomial; how long it is
  Beside these, smaller steps: `diffL` (a definition), `diffL_length`, `diffL_getD`, `gl_neg`,
  `stepY_basis`, `maskedEnds_zero_aux` (stated again, with named binders, as `maskedEnds_zero`,
  CubeInY.lean, which calls it).

Limits. The loop's law is at the reading `Reading.gl` alone. HYPOTHESES: k + l.length < 2 ^ 64
(`fold_poly`; k + 1 < 2 ^ 64 at `stepY_basis`), and that the second list reads as `binomP k`; as
many mask entries as end values (`polyInY_eq`, `maskedEnds_zero_aux`); n ≤ l.length, and the
readings at every i < l.length (`diffs_read`); s.2.length = s.1.length + 1 (`fold_length`); the
first list is not empty (`mulP_two_length`); i + 1 < l.length (`diffL_getD`).

Kin. `polyOf_addP`, `polyOf_mulP` and `addP_length` STAND TO THE LETTER IN ANOTHER KIND's FILE, AT
THAT KIND's OWN `addP` AND `mulP`: `polyOf_addP`, `polyOf_mulP`, `length_addP`
(Johnson/Desc/K5/Honest/Law/Poly.lean): two kinds' texts of one arithmetic on lists of coefficients;
other constants, so neither can call the other. Near them: `mulP_two_length` is that file's
`length_mulP_pair`, the binders in another order; `polyOf_scale` is its `polyOf_scaleP` and the
frame's `polyOf_scaleL` (Johnson/Desc/ProofFile/Honest/SumLaw/Lists.lean) with their `scaleP` |
`scaleL` unfolded; the frame has the laws on sums at its own `addL` (`polyOf_addL`, in the same file
of the frame's; `addL_length`, Johnson/Desc/ProofFile/Honest/SumLaw/Fits.lean). This file builds on
none of these. `gl_neg` is the library's `OnBytes.Slice.readE_neg` under another name; at every
reading the library has `neg_val` (OnBytes/Tie/Pv/Lookup/Forest/FoPlaneClaims.lean),
on which this file does not build. That the reading takes an inverse to the inverse is the library's
`OnBytes.Slice.readE_inv`, called inside the proof of `stepY_basis`; the library states it again in
other files (`gl_inv`, Johnson/Road/Rows/LayerEnds34Ref.lean;
`rd_inv`, Johnson/Desc/Kinds/Law/Base.lean; `gl_inverse`,
Johnson/Road/HeadKit.lean).

No property is claimed.
-/
import Johnson.Desc.K4.Honest.Law.CubeKitN
import Johnson.Road.HeadLookMet
import OnBytes.Slice.ProgField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest.CubeLaw
open OnBytes (E addE subE mulE negE invE ofF zeroE oneE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Part.MaskedSum (polyOf)
open Polynomial

section General
variable {K : Type} [Field K] (ρ : Reading K)

theorem polyOf_addP : ∀ a b : List E, polyOf ρ (addP a b) = polyOf ρ a + polyOf ρ b
  | [], b => by simp [addP, polyOf]
  | x :: a, [] => by simp [addP, polyOf]
  | x :: a, y :: b => by
    simp only [addP, polyOf]
    rw [polyOf_addP a b, ρ.add, C_add]
    ring

theorem polyOf_scale (k : E) : ∀ l : List E, polyOf ρ (l.map (mulE k)) = C (ρ.val k) * polyOf ρ l
  | [] => by simp [polyOf]
  | x :: l => by
    simp only [List.map_cons, polyOf]
    rw [polyOf_scale k l, ρ.mul, C_mul]
    ring

theorem polyOf_mulP : ∀ a b : List E, polyOf ρ (mulP a b) = polyOf ρ a * polyOf ρ b
  | [], b => by simp [mulP, polyOf]
  | x :: a, b => by
    rw [mulP, polyOf_addP, polyOf_scale]
    simp only [polyOf]
    rw [polyOf_mulP a b, ρ.zero, C_0]
    ring

/-- The differences of neighbours. -/
def diffL (l : List E) : List E := ((l.drop 1).zip l).map fun y => subE y.1 y.2

theorem diffL_length (l : List E) : (diffL l).length = l.length - 1 := by
  simp only [diffL, List.length_map, List.length_zip, List.length_drop]
  omega

theorem diffL_getD : ∀ (l : List E) (i : ℕ), i + 1 < l.length →
    (diffL l).getD i zeroE = subE (l.getD (i + 1) zeroE) (l.getD i zeroE)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | [_], i, h => by
    simp only [List.length_cons, List.length_nil] at h
    omega
  | _ :: _ :: _, 0, _ => rfl
  | _ :: b :: t, i + 1, h =>
    diffL_getD (b :: t) i (by simp only [List.length_cons] at h ⊢; omega)

/-- **The program's differences read as the differences of the readings.** -/
theorem diffs_read : ∀ (n : ℕ) (l : List E) (v : ℕ → K), n ≤ l.length →
    (∀ i, i < l.length → ρ.val (l.getD i zeroE) = v i) → (diffs n l).map ρ.val = dseq n v
  | 0, _, _, _, _ => rfl
  | n + 1, l, v, hn, hv => by
    have h0 : ρ.val (l.headD zeroE) = v 0 := by
      have := hv 0 (by omega)
      cases l with
      | nil => exact this
      | cons a t => exact this
    have ih := diffs_read n (diffL l) (fun i => v (i + 1) - v i)
      (by rw [diffL_length]; omega) (fun i hi => by
        rw [diffL_length] at hi
        rw [diffL_getD l i (by omega), ρ.sub, hv (i + 1) (by omega), hv i (by omega)])
    show ρ.val (l.headD zeroE) :: (diffs n (diffL l)).map ρ.val = v 0 :: dseq n _
    rw [h0, ih]

end General

theorem diffs_length : ∀ (n : ℕ) (l : List E), (diffs n l).length = n
  | 0, _ => rfl
  | n + 1, l => by rw [diffs, List.length_cons, diffs_length n]

theorem addP_length : ∀ a b : List E, (addP a b).length = max a.length b.length
  | [], b => by simp [addP]
  | x :: a, [] => by simp [addP]
  | x :: a, y :: b => by
    simp only [addP, List.length_cons]
    rw [addP_length a b]
    omega

theorem mulP_two_length (u w : E) : ∀ a : List E, a ≠ [] → (mulP a [u, w]).length = a.length + 1
  | [], h => absurd rfl h
  | [x], _ => by
    simp only [mulP, addP_length, List.length_map, List.length_cons, List.length_nil]
    omega
  | x :: y :: a, _ => by
    rw [mulP, addP_length, List.length_cons, mulP_two_length u w (y :: a) (by simp)]
    simp only [List.length_map, List.length_cons, List.length_nil]
    omega

/-! ## The loop -/

/-- One turn of `polyInY`'s loop. s: the sum so far and the next basis polynomial. d: a difference
and its number. -/
def stepY (s : List E × List E) (d : E × ℕ) : List E × List E :=
  (addP s.1 (s.2.map (mulE d.1)),
    (mulP s.2 [negE (ofF d.2.toUInt64), oneE]).map (mulE (invE (ofF (d.2 + 1).toUInt64))))

theorem polyInY_eq (dY : ℕ) (f : List E → E) (ends masks : List E)
    (hl : ends.length = masks.length) :
    polyInY dY f ends masks =
      (((diffs (dY + 1) ((List.range (dY + 1)).map fun k =>
        f (maskedEnds ends masks (ofF k.toUInt64)))).zipIdx 0).foldl stepY ([], [oneE])).1 := by
  unfold polyInY
  rw [if_neg (by simp [hl])]
  rfl

theorem gl_neg (a : E) : Reading.gl.val (negE a) = -Reading.gl.val a := OnBytes.Slice.readE_neg a

theorem stepY_basis (s : List E × List E) (d : E) (k : ℕ) (hk : k + 1 < 2 ^ 64)
    (hs : polyOf Reading.gl s.2 = binomP k) :
    polyOf Reading.gl (stepY s (d, k)).2 = binomP (k + 1) := by
  simp only [stepY, polyOf_scale, polyOf_mulP, hs, polyOf, binomP]
  have gl_inv : ∀ a : E, Reading.gl.val (invE a) = (Reading.gl.val a)⁻¹ := OnBytes.Slice.readE_inv
  rw [gl_inv, gl_neg, OnBytes.Road.Hd.gl_nat hk, OnBytes.Road.Hd.gl_nat (Nat.lt_of_succ_lt hk),
    Reading.gl.one, Nat.cast_succ, C_neg, C_1]
  ring

/-- **What the loop returns, as a polynomial.** -/
theorem fold_poly : ∀ (l : List E) (k : ℕ) (s : List E × List E), k + l.length < 2 ^ 64 →
    polyOf Reading.gl s.2 = binomP k →
    polyOf Reading.gl ((l.zipIdx k).foldl stepY s).1 =
      polyOf Reading.gl s.1 + newtonP (l.map Reading.gl.val) k
  | [], k, s, _, _ => by simp [newtonP]
  | d :: l, k, s, hk, hs => by
    rw [List.length_cons] at hk
    rw [List.zipIdx_cons, List.foldl_cons,
      fold_poly l (k + 1) (stepY s (d, k)) (by omega) (stepY_basis s d k (by omega) hs)]
    simp only [stepY, polyOf_addP, polyOf_scale, hs, List.map_cons, newtonP]
    ring

theorem fold_length : ∀ (l : List E) (k : ℕ) (s : List E × List E),
    s.2.length = s.1.length + 1 →
    ((l.zipIdx k).foldl stepY s).1.length = s.1.length + l.length
  | [], _, _, _ => by simp
  | d :: l, k, s, hs => by
    have hne : s.2 ≠ [] := by
      intro e
      rw [e] at hs
      simp at hs
    have h1 : (stepY s (d, k)).1.length = s.1.length + 1 := by
      simp only [stepY, addP_length, List.length_map]
      omega
    have h2 : (stepY s (d, k)).2.length = s.2.length + 1 := by
      simp only [stepY, List.length_map]
      exact mulP_two_length _ _ s.2 hne
    rw [List.zipIdx_cons, List.foldl_cons, fold_length l (k + 1) (stepY s (d, k)) (by omega), h1,
      List.length_cons]
    omega

theorem maskedEnds_zero_aux : ∀ ends masks : List E, ends.length = masks.length →
    (maskedEnds ends masks zeroE).map Reading.gl.val = ends.map Reading.gl.val
  | [], _, _ => by simp [maskedEnds]
  | _ :: _, [], h => by simp at h
  | a :: e, b :: m, h => by
    have ih := maskedEnds_zero_aux e m (by simpa using h)
    simp only [maskedEnds, List.zip_cons_cons, List.map_cons] at ih ⊢
    rw [ih, Reading.gl.add, Reading.gl.mul, Reading.gl.zero, zero_mul, add_zero]

end OnBytes.Desc.First.K4.Honest.CubeLaw

#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.polyOf_addP
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.polyOf_scale
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.polyOf_mulP
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.diffL
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.diffL_length
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.diffL_getD
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.diffs_read
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.diffs_length
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.addP_length
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.mulP_two_length
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.stepY
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.polyInY_eq
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.gl_neg
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.stepY_basis
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.fold_poly
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.fold_length
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.maskedEnds_zero_aux
