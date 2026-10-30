-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Inst/Model/Att/KeyFormsExt/Cube.lean: `eqPt` and `ones` on a segment of a vertex of the cube, and
`sumPhi` as a sum of table values.

Part of the proof that the key forms of an attention segment, at the rule values, are the
multilinear extensions of the calls' vectors of looked-up values (`kfExt`,
Inst/Model/Att/KeyFormsExt/All.lean). Statements with their proofs. No protocol and no probability:
algebra of extensions (`Blocks.ext`, Blocks/Ext.lean).
Main names:
  `seg_cubePt`: n coordinates of a vertex of G variables, from the offset off on, are the vertex of
    n variables with the number X / 2^r % 2^n, where off + n + r = G.
  `eqPt_seg`: `eqPt` there is `Blocks.eqN` of that number. `ones_eq`: `ones n u`
    (Inst/Model/Att/Points.lean) is `Blocks.eqN n 0 u (2^n - 1)`. `eqN_cube`: the equality weight of
    Y at the vertex s is [s = Y]. `ones_seg`: `ones` on a segment is [the number is 2^n - 1].
  `sumPhi_cube`: `sumPhi D C p t s` (Inst/Model/Att/Sums.lean) is the sum over b and over the
    vertices X of W_b(vertex X) A_b[X] B_b[X].
  `ext_ext_sum`: for a product of a function of i and a function of j, summed over n, the two
    extensions come apart.
Limits: no hypothesis on sizes. Coordinate 0 of a point belongs to the most significant bit, as in
Blocks/Ext.lean.
-/
import Inst.Model.Att.KeyFormsExt.Call3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Inst.Model.AttSeg.KeyFormsExt
open Inst.Model Inst.Model.AttSeg Finset

variable {E : Type} [Field E]

theorem seg_cubePt (G off n r X : ℕ) (hG : off + n + r = G) {k : ℕ} (hk : k < n) :
    AttSeg.sh (Blocks.cubePt G X : ℕ → E) off k = (Blocks.cubePt n (X / 2 ^ r % 2 ^ n) : ℕ → E) k :=
        by
  show (Blocks.cubePt G X : ℕ → E) (off + k) = _
  rw [cubePt_apply _ _ (by omega), cubePt_apply _ _ hk, Nat.testBit_mod_two_pow,
      Nat.testBit_div_two_pow]
  have e : G - 1 - (off + k) = n - 1 - k + r := by omega
  have l : n - 1 - k < n := by omega
  rw [e]
  simp [l]

theorem eqPt_congr (n : ℕ) (u : ℕ → E) {ξ ξ' : ℕ → E} (h : ∀ k < n, ξ k = ξ' k) :
    AttSeg.eqPt n u ξ = AttSeg.eqPt n u ξ' := by
  unfold AttSeg.eqPt
  exact Finset.prod_congr rfl fun k hk => by rw [h k (Finset.mem_range.1 hk)]

theorem eqPt_cube (n : ℕ) (u : ℕ → E) (s : ℕ) : AttSeg.eqPt n u (Blocks.cubePt n s) =
    Blocks.eqN n 0 u s := by
  have h := eqPt_hi n 0 u s
  rwa [Nat.add_zero, pow_zero, Nat.div_one] at h

theorem eqPt_seg (G off n r X : ℕ) (hG : off + n + r = G) (u : ℕ → E) :
    AttSeg.eqPt n u (AttSeg.sh (Blocks.cubePt G X) off) = Blocks.eqN n 0 u (X / 2 ^ r % 2 ^ n) := by
  rw [eqPt_congr n u fun k hk => seg_cubePt G off n r X hG hk, eqPt_cube]

/-- ones is the equality weight of the last index -/
theorem ones_eq (n : ℕ) (u : ℕ → E) : AttSeg.ones n u = Blocks.eqN n 0 u (2 ^ n - 1) := by
  unfold AttSeg.ones Blocks.eqN
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  rw [Nat.testBit_two_pow_sub_one, Nat.zero_add]
  simp [show n - 1 - k < n by omega]

/-- the equality weight of Y at the vertex s is [s = Y] -/
theorem eqN_cube (n : ℕ) {s Y : ℕ} (hs : s < 2 ^ n) (hY : Y < 2 ^ n) :
    Blocks.eqN n 0 (Blocks.cubePt n s : ℕ → E) Y = if s = Y then 1 else 0 := by
  have h := Blocks.ext_cubePt (E := E) n (fun X => if X = Y then 1 else 0) hs
  rw [ext_def] at h
  have h' : (∑ X ∈ range (2 ^ n), Blocks.eqN n 0 (Blocks.cubePt n s : ℕ → E) X * if X =
      Y then 1 else 0) =
      if s = Y then 1 else 0 := h
  rw [← h', Finset.sum_eq_single Y]
  · rw [if_pos rfl, mul_one]
  · intro X _ hX
    rw [if_neg hX, mul_zero]
  · intro hn
    exact absurd (Finset.mem_range.2 hY) hn

theorem ones_congr (n : ℕ) {ξ ξ' : ℕ → E} (h : ∀ k < n, ξ k = ξ' k) : AttSeg.ones n ξ =
    AttSeg.ones n ξ' := by
  unfold AttSeg.ones
  exact Finset.prod_congr rfl fun k hk => h k (Finset.mem_range.1 hk)

theorem ones_seg (G off n r X : ℕ) (hG : off + n + r = G) :
    AttSeg.ones n (AttSeg.sh (Blocks.cubePt G X : ℕ → E) off) = if X / 2 ^ r % 2 ^ n = 2 ^ n -
        1 then 1 else 0 := by
  rw [ones_congr n fun k hk => seg_cubePt G off n r X hG hk, ones_eq,
    eqN_cube n (Nat.mod_lt _ (Nat.two_pow_pos n)) (Nat.sub_lt (Nat.two_pow_pos n) Nat.one_pos)]

variable (D : AttSeg.Dim) (C : AttSeg.Calls) (p : AttSeg.Pub E) (t : AttSeg.Raw → E)

/-- sumPhi, in table values -/
theorem sumPhi_cube (s : AttSeg.Step) :
    AttSeg.sumPhi D C p t s = ∑ b ∈ range D.nb, ∑ X ∈ range (2 ^ s.g D),
      AttSeg.Wb D C p s b (Blocks.cubePt (s.g D) X) * AttSeg.Acube D C p t s b X *
          AttSeg.Bcube D C p t s b X := by
  unfold AttSeg.sumPhi AttSeg.Phi
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun X hX => ?_
  have hX' := Finset.mem_range.1 hX
  have hA : AttSeg.Aext D C p t s b (Blocks.cubePt (s.g D) X) = AttSeg.Acube D C p t s b X :=
      Blocks.ext_cubePt _ _ hX'
  have hB : AttSeg.Bext D C p t s b (Blocks.cubePt (s.g D) X) = AttSeg.Bcube D C p t s b X :=
      Blocks.ext_cubePt _ _ hX'
  rw [hA, hB]

/-- conB is an extension over the positions of a block; conN over the channels -/
theorem conB_ext (v a : ℕ → E) : AttSeg.conB D v a = Blocks.ext D.lB a v := rfl
theorem conN_ext (v a : ℕ → E) : AttSeg.conN D v a = Blocks.ext D.ln a v := rfl

/-- a product of a function of i' and a function of j', summed over n: the two extensions come apart
-/
theorem ext_ext_sum (g g' : ℕ) (N : ℕ) (a a' : ℕ → ℕ → E) (v v' : ℕ → E) :
    Blocks.ext g (fun i => Blocks.ext g' (fun j => ∑ n ∈ range N, a i n * a' j n) v') v =
      ∑ n ∈ range N, Blocks.ext g (fun i => a i n) v * Blocks.ext g' (fun j => a' j n) v' := by
  have h1 : ∀ i, Blocks.ext g' (fun j => ∑ n ∈ range N, a i n * a' j n) v' =
      ∑ n ∈ range N, a i n * Blocks.ext g' (fun j => a' j n) v' := by
    intro i
    rw [Blocks.ext_sum]
    exact Finset.sum_congr rfl fun n _ => Blocks.ext_smul _ _ _ _
  simp only [h1]
  rw [Blocks.ext_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Blocks.ext_congr (w := fun i => Blocks.ext g' (fun j => a' j n) v' * a i n)
      (fun i _ => mul_comm _ _),
    Blocks.ext_smul, mul_comm]

end Inst.Model.AttSeg.KeyFormsExt
