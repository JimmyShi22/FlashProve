-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/Vec.lean: the vectors and sums of the two sumchecks on the norms of a group of layers,
in the names of Inst/Model/FF/Objects.lean.

Inst/Model/FF/Objects.lean names, for a feed-forward segment, the vector Pv of the squares' layer
over the indices (norm | feature | position), the vector of squares HVt, the honest values Wt and
pvt of the sums W_s and of the row products, and the summand GV of the sumcheck over the positions.
This file has identities on these; no function of a verifier stands in a statement.

Main definitions: xCube (the vector of the squares' layer with letters for its sizes and weights,
0 at the norms and features that are padding); rowsS (the summand of the sumcheck over the positions
as a polynomial of degree 2 in four values for each norm).

Main theorems.
 - xCube_congr; xCube_Pv, ext_xCube_Pv: on the cube, where every number of a norm is below n, xCube
   at the powers of γ and the library's number of feature bits is Pv.
 - ext_squares: the extension of the sum of the squares is the batch of the values Wt.
 - Pv_at; sum_HVt: HVt, summed over a norm's features, is that batch.
 - squares_law: for one norm, that batch times h to the number of feature bits is the extension over
   (feature | position) of the square of Pv, at a point whose feature coordinates all equal h.
 - ext_Pv_sq: the extension of the square of Pv at a point whose feature coordinates all equal h,
   with 1 - h = h: h to the number of feature bits, times the sum over the norms, under the equality
   weights of the point's first coordinates, of that batch at the point's last coordinates.
 - ext_Pv_point: the extension of Pv at a point, as one sum over (norm | block of features | limb).
 - rowsS_GV: rowsS on the extensions of the four numbers of each norm's ledger is GV.

Limits: identities alone. Five limbs.


-/
import Inst.Model.Common.LedgerSound
import Inst.Model.FF.Objects
import Cb.Pv.Lay.End.Cube

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Finset
open Inst.Model.FFSeg (Dim Cell led bS Pv HVt Wt GV lDd)
open Blocks (ext eqN)

variable {K : Type} [Field K]

/-- The vector of the product layer of the squares at the index X = (norm | feature | position), of
which the feature has lPd bits and the position D.lT: the nl limbs of the stream under the weights
gl, for a norm below n and a feature below d; else 0. -/
def xCube (D : Dim) (t : Cell → K) (gl : ℕ → K) (n d nl lPd X : ℕ) : K :=
  if X / 2 ^ (lPd + D.lT) < n ∧ X / 2 ^ D.lT % 2 ^ lPd < d then
    ∑ l ∈ range nl, gl l *
      bS D t (X / 2 ^ (lPd + D.lT)) l (X / 2 ^ D.lT % 2 ^ lPd) (X % 2 ^ D.lT)
  else 0

/-- xCube reads its weights below nl alone. -/
theorem xCube_congr (D : Dim) (t : Cell → K) {gl gl' : ℕ → K} (n d nl lPd X : ℕ)
    (h : ∀ l, l < nl → gl l = gl' l) : xCube D t gl n d nl lPd X = xCube D t gl' n d nl lPd X := by
  unfold xCube
  by_cases hc : X / 2 ^ (lPd + D.lT) < n ∧ X / 2 ^ D.lT % 2 ^ lPd < d
  · rw [if_pos hc, if_pos hc]
    exact sum_congr rfl fun l hl => by rw [h l (mem_range.mp hl)]
  · rw [if_neg hc, if_neg hc]

/-- On the cube, where every number of a norm is below n, xCube is the library's Pv. -/
theorem xCube_Pv (D : Dim) (t : Cell → K) (γ : K) (n lNI X : ℕ) (hn : 2 ^ lNI ≤ n)
    (hX : X < 2 ^ (lNI + (lDd D + D.lT))) :
    xCube D t (fun l => γ ^ l) n D.d 5 (lDd D) X = Pv D t γ X := by
  have e1 : X / 2 ^ (lDd D + D.lT) = X / D.T / 2 ^ lDd D := by
    rw [Nat.div_div_eq_div_mul]
    congr 1
    show 2 ^ (lDd D + D.lT) = 2 ^ D.lT * 2 ^ lDd D
    rw [pow_add, Nat.mul_comm]
  have hν : X / 2 ^ (lDd D + D.lT) < n :=
    lt_of_lt_of_le (Nat.div_lt_of_lt_mul (by
      rw [pow_add] at hX
      rw [Nat.mul_comm]
      exact hX)) hn
  unfold xCube Inst.Model.FFSeg.Pv
  by_cases hj : X / 2 ^ D.lT % 2 ^ lDd D < D.d
  · rw [if_pos ⟨hν, hj⟩, if_pos (show X / D.T % 2 ^ lDd D < D.d from hj), e1]
    rfl
  · rw [if_neg (fun k => hj k.2), if_neg (show ¬ X / D.T % 2 ^ lDd D < D.d from hj)]

/-- So the two have the same extension. -/
theorem ext_xCube_Pv (D : Dim) (t : Cell → K) (γ : K) (n lNI : ℕ) (hn : 2 ^ lNI ≤ n)
    (z : ℕ → K) :
    ext (lNI + (lDd D + D.lT)) (xCube D t (fun l => γ ^ l) n D.d 5 (lDd D)) z =
      ext (lNI + (lDd D + D.lT)) (Pv D t γ) z :=
  Blocks.ext_congr (fun X hX => xCube_Pv D t γ n lNI X hn hX) z

/-- The extension of the sum of the squares is the batch of the honest values of the sums W_s. -/
theorem ext_squares (D : Dim) (t : Cell → K) (g : K) (ν : ℕ) (uP : ℕ → K) :
    ext D.lT (fun i => ∑ j ∈ range D.d, (∑ l ∈ range 5, g ^ l * bS D t ν l j i) ^ 2) uP =
      ∑ s ∈ range 9, g ^ s * Wt D t uP ν s := by
  have e : (fun i => ∑ j ∈ range D.d, (∑ l ∈ range 5, g ^ l * bS D t ν l j i) ^ 2) =
      fun i => ∑ s ∈ range 9,
        g ^ s * Inst.Model.Ledger.Wsum D.d (fun l j => bS D t ν l j i) s :=
    funext fun i => (Inst.Model.Ledger.sum_pow_Wsum g D.d fun l j => bS D t ν l j i).symm
  rw [e, Blocks.ext_sum]
  exact sum_congr rfl fun s _ => Blocks.ext_smul _ _ _ _

/-- The library's Pv at the index (ν | j | i). -/
theorem Pv_at (D : Dim) (t : Cell → K) (γ : K) (ν j i : ℕ) (hj : j < 2 ^ lDd D) (hi : i < D.T) :
    Pv D t γ ((ν * 2 ^ lDd D + j) * D.T + i) =
      if j < D.d then ∑ l ∈ range 5, γ ^ l * bS D t ν l j i else 0 := by
  unfold Inst.Model.FFSeg.Pv
  rw [(div_mod_at (ν * 2 ^ lDd D + j) i D.T hi).1, (div_mod_at (ν * 2 ^ lDd D + j) i D.T hi).2,
    (div_mod_at ν j (2 ^ lDd D) hj).1, (div_mod_at ν j (2 ^ lDd D) hj).2]

/-- The width of the stream is at most two to the library's number of feature bits. -/
theorem d_le (D : Dim) : D.d ≤ 2 ^ lDd D := Nat.le_pow_clog (by norm_num) _

/-- The library's vector of squares HVt, summed over the features of norm ν, is the batch of the
honest values Wt of the sums W_s under the powers of γ. -/
theorem sum_HVt (D : Dim) (t : Cell → K) (γ : K) (pV : ℕ → K) (ν : ℕ) :
    ∑ j ∈ range (2 ^ lDd D), HVt D t pV γ (ν * 2 ^ lDd D + j) =
      ∑ s ∈ range 9, γ ^ s * Wt D t pV ν s := by
  calc ∑ j ∈ range (2 ^ lDd D), HVt D t pV γ (ν * 2 ^ lDd D + j)
      = ext D.lT (fun i => ∑ j ∈ range (2 ^ lDd D),
          Pv D t γ ((ν * 2 ^ lDd D + j) * D.T + i) ^ 2) pV := (Blocks.ext_sum _ _ _ _).symm
    _ = ext D.lT (fun i => ∑ j ∈ range D.d, (∑ l ∈ range 5, γ ^ l * bS D t ν l j i) ^ 2) pV := by
        refine Blocks.ext_congr (fun i hi => ?_) pV
        rw [← sum_pad (d_le D)]
        refine sum_congr rfl fun j hj => ?_
        rw [Pv_at D t γ ν j i (mem_range.mp hj) hi]
        by_cases h : j < D.d
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h]
          ring
    _ = _ := ext_squares D t γ ν pV

/-- For one norm ν: the batch of the honest values Wt, times h to the number of feature bits, is the
extension over (feature | position) of the square of Pv on the norm's part of the cube, at a point z
whose feature coordinates all equal h, with 1 - h = h. -/
theorem squares_law (D : Dim) (t : Cell → K) (c h : K) (z : ℕ → K) (hh : 1 - h = h)
    (hz : ∀ j, j < lDd D → z j = h) (ν : ℕ) :
    h ^ lDd D * ∑ s ∈ range 9, c ^ s * Wt D t (fun j => z (lDd D + j)) ν s =
      ext (lDd D + D.lT) (fun x => Pv D t c (ν * 2 ^ (lDd D + D.lT) + x) *
        Pv D t c (ν * 2 ^ (lDd D + D.lT) + x)) z := by
  rw [ext_half (lDd D) D.lT _ z h hh hz, ← sum_HVt]
  congr 1
  rw [Blocks.ext_sum]
  refine sum_congr rfl fun j _ => ?_
  unfold Inst.Model.FFSeg.HVt
  refine Blocks.ext_congr (fun i _ => ?_) _
  have e : ν * 2 ^ (lDd D + D.lT) + (j * 2 ^ D.lT + i) = (ν * 2 ^ lDd D + j) * D.T + i := by
    show _ = (ν * 2 ^ lDd D + j) * 2 ^ D.lT + i
    rw [pow_add]
    ring
  rw [e]
  ring

/-- The sum over the cube on which the product layer of the squares runs. At a point z whose
feature coordinates all equal h, with 1 - h = h, and for 2^lNI norms. -/
theorem ext_Pv_sq (D : Dim) (t : Cell → K) (γ h : K) (z : ℕ → K) (lNI : ℕ) (hh : 1 - h = h)
    (hz : ∀ j, j < lDd D → z (lNI + j) = h) :
    ext (lNI + (lDd D + D.lT)) (fun X => Pv D t γ X ^ 2) z =
      h ^ lDd D * ∑ ν ∈ range (2 ^ lNI), eqN lNI 0 z ν *
        ∑ s ∈ range 9, γ ^ s * Wt D t (fun j => z (lNI + lDd D + j)) ν s := by
  have e : ext (lNI + (lDd D + D.lT)) (fun X => Pv D t γ X ^ 2) z =
      ext (lNI + (lDd D + D.lT))
        (fun X => xCube D t (fun l => γ ^ l) (2 ^ lNI) D.d 5 (lDd D) X ^ 2) z :=
    Blocks.ext_congr (fun X hX => by rw [xCube_Pv D t γ (2 ^ lNI) lNI X le_rfl hX]) z
  rw [e]
  refine (cube_squares lNI (lDd D) D.lT (2 ^ lNI) D.d le_rfl (d_le D)
    (fun ν j i => ∑ l ∈ range 5, γ ^ l * bS D t ν l j i) z h hh hz).trans ?_
  congr 1
  exact sum_congr rfl fun ν _ => by rw [ext_squares]

/-- The extension of Pv at a point z, block by block. b: the bits of a block's number; s: those of a
feature in its block; B: the number of blocks in use. -/
theorem ext_Pv_point (D : Dim) (t : Cell → K) (γ : K) (z : ℕ → K) (lNI b s B : ℕ)
    (hl : lDd D = b + s) (hd : D.d = B * 2 ^ s) (hB : B ≤ 2 ^ b) :
    ext (lNI + ((b + s) + D.lT)) (Pv D t γ) z =
      ∑ i ∈ range (2 ^ lNI * B * 5),
        eqN (lNI + b) 0 z (i / 5 / B * 2 ^ b + i / 5 % B) * γ ^ (i % 5) *
          ∑ r ∈ range (2 ^ s), eqN s (lNI + b) z r *
            ext D.lT (fun p => bS D t (i / 5 / B) (i % 5) (i / 5 % B * 2 ^ s + r) p)
              (fun j => z (lNI + (b + s) + j)) := by
  have e : ext (lNI + ((b + s) + D.lT)) (Pv D t γ) z =
      ext (lNI + ((b + s) + D.lT))
        (xCube D t (fun l => γ ^ l) (2 ^ lNI) (B * 2 ^ s) 5 (b + s)) z := by
    rw [← hl, ← hd]
    exact (ext_xCube_Pv D t γ (2 ^ lNI) lNI le_rfl z).symm
  rw [e]
  exact cube_point lNI b s D.lT (2 ^ lNI) B 5 le_rfl hB (fun l => γ ^ l)
    (fun ν l j p => bS D t ν l j p) z

/-- The summand as a polynomial of degree 2 in four values a, b, lo, hi for each of n norms: the
seven products of each norm's values, product x % 7 of norm x / 7 under the weight om x. -/
def rowsS (om : ℕ → K) (n : ℕ) (a b lo hi : ℕ → K) : K :=
  ∑ x ∈ range (7 * n), om x *
    Inst.Model.Ledger.prodsOf (a (x / 7)) (b (x / 7)) (lo (x / 7)) (hi (x / 7)) (x % 7)

/-- rowsS on the extensions of the four numbers of each norm's ledger, at a point X, is the
library's summand GV, under the weights ω ν n = om (7 ν + n). -/
theorem rowsS_GV (D : Dim) (t : Cell → K) (om : ℕ → K) (X : ℕ → K) :
    rowsS om D.nNu (fun ν => ext D.lT (fun i => Inst.Model.Ledger.sa (led t ν i)) X)
        (fun ν => ext D.lT (fun i => Inst.Model.Ledger.sb (led t ν i)) X)
        (fun ν => ext D.lT (fun i => Inst.Model.Ledger.Rlo (led t ν i)) X)
        (fun ν => ext D.lT (fun i => Inst.Model.Ledger.Rhi (led t ν i)) X) =
      GV D t (fun ν n => om (7 * ν + n)) X := by
  unfold rowsS Inst.Model.FFSeg.GV
  rw [Nat.mul_comm 7, Alg.sum_range_mul_add]
  refine sum_congr rfl fun ν _ => sum_congr rfl fun j hj => ?_
  beta_reduce
  rw [(div_mod_at ν j 7 (mem_range.mp hj)).1, (div_mod_at ν j 7 (mem_range.mp hj)).2,
    Nat.mul_comm ν 7]

end Cb.Pv.Lay.End
