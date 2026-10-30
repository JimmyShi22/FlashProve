-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttWb14.lean: the public weights of four sumchecks of an attention segment are the
multilinear extensions of their values on the cube.

The library writes the public weight of a step as a polynomial in the point (Wb in
Inst/Model/Att/Sums.lean). Cb/Pv/Att/Steps.lean, which puts the steps into the general sumcheck of
products, takes in its place the multilinear extension of the weight's values on the cube. This file
shows that the two agree at every point, for the steps s6b, s6d, s8 and s11.

The way. A function of a point that reads the first g coordinates alone and has degree at most 1 in
each of them is the extension of its values on the cube (ext_of_deg, from Alg.DegLE.eq_mle). Each
weight is a product of factors that read stretches of coordinates which do not meet; a factor has
degree at most 1 in the coordinates of its stretch and 0 in the others (dBlk, deg_block).

Main theorems: ext_of_deg; deg_eqPt, deg_ones, deg_eqN; wbExt8, wbExt6d, wbExt6b, wbExt11.

All of it is algebra on the library's definitions. Nothing is said about a verifier.


-/
import Inst.Model.Att.KeyForms
import Blocks.ProductBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

open Finset Blocks
open Inst.Model.AttSeg

variable {E : Type} [Field E]

/-! ## A function of degree 1 is the extension of its values on the cube -/

/-- A function of a point that reads the first g coordinates alone and has degree at most 1 in each
is the multilinear extension of its values on the cube. -/
theorem ext_of_deg {g : ℕ} (f : (ℕ → E) → E)
    (hloc : ∀ ξ ξ' : ℕ → E, (∀ k < g, ξ k = ξ' k) → f ξ = f ξ')
    (hdeg : Alg.DegLE (fun _ => 1) fun x : Fin g → E => f (nat x)) (ξ : ℕ → E) :
    Blocks.ext g (fun X => f (cubePt g X)) ξ = f ξ := by
  rw [Blocks.PL.ext_eq_mleN, Alg.mleN_eq_mle]
  have e : (fun b : Fin g → Bool => f (cubePt g (Alg.num b))) =
      fun b => (fun x : Fin g → E => f (nat x)) (Alg.corner b) := by
    funext b
    unfold cubePt
    rw [Alg.bits_num]
  rw [e, ← hdeg.eq_mle (fun _ => le_refl 1)]
  exact hloc _ _ fun k hk => by simp [nat, hk]

/-! ## Stretches of coordinates -/

/-- The bound 1 on the coordinates a, .., a + n - 1 and 0 on the others. -/
def dBlk (g a n : ℕ) : Fin g → ℕ := fun i => if a ≤ i.val ∧ i.val < a + n then 1 else 0

/-- A function of the n coordinates from a on, of degree at most 1 in each. -/
theorem deg_block {g a n : ℕ} (h : a + n ≤ g) (G : (Fin n → E) → E)
    (hG : Alg.DegLE (fun _ => 1) G) :
    Alg.DegLE (dBlk g a n) fun x : Fin g → E =>
      G fun k => x ⟨a + k.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left k.isLt a) h⟩ :=
  hG.comp (fun k : Fin n => (⟨a + k.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left k.isLt a) h⟩ :
      Fin g))
    (fun k k' e => Fin.ext (by
      have e' := congrArg Fin.val e
      simp only at e'
      omega))
    (dBlk g a n)
    (fun v => by
      unfold dBlk
      rw [if_pos ⟨Nat.le_add_right _ _, Nat.add_lt_add_left v.isLt a⟩])

/-- A coordinate of a stretch of a vector. -/
theorem sh_nat {g a : ℕ} (x : Fin g → E) {k : ℕ} (h : a + k < g) :
    sh (nat x) a k = x ⟨a + k, h⟩ := by
  simp [sh, nat, h]

/-- The equality polynomial of a point u and a stretch. -/
theorem deg_eqPt {g a n : ℕ} (h : a + n ≤ g) (u : ℕ → E) :
    Alg.DegLE (dBlk g a n) fun x : Fin g → E => eqPt n u (sh (nat x) a) := by
  have e : (fun x : Fin g → E => eqPt n u (sh (nat x) a)) = fun x : Fin g → E =>
      (fun y : Fin n → E => Alg.eqPt (fun k : Fin n => u k) y) fun k =>
        x ⟨a + k.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left k.isLt a) h⟩ := by
    funext x
    unfold eqPt Alg.eqPt
    rw [← Fin.prod_univ_eq_prod_range (fun k => eq1 (u k) (sh (nat x) a k)) n]
    refine prod_congr rfl fun k _ => ?_
    rw [sh_nat x (Nat.lt_of_lt_of_le (Nat.add_lt_add_left k.isLt a) h)]
    rfl
  rw [e]
  exact deg_block h _ (Alg.DegLE.eqPt _)

/-- The product of the coordinates of a stretch. -/
theorem deg_ones {g a n : ℕ} (h : a + n ≤ g) :
    Alg.DegLE (dBlk g a n) fun x : Fin g → E => ones n (sh (nat x) a) := by
  have e : (fun x : Fin g → E => ones n (sh (nat x) a)) =
      fun x : Fin g → E => eqPt n (fun _ => 1) (sh (nat x) a) := by
    funext x
    unfold ones eqPt eq1
    exact prod_congr rfl fun k _ => by ring
  rw [e]
  exact deg_eqPt h _

/-- The equality weight of a stretch at an index. -/
theorem deg_eqN {g a n : ℕ} (h : a + n ≤ g) (P : ℕ) :
    Alg.DegLE (dBlk g a n) fun x : Fin g → E => eqN n 0 (sh (nat x) a) P := by
  have e : (fun x : Fin g → E => eqN n 0 (sh (nat x) a) P) = fun x : Fin g → E =>
      (fun y : Fin n → E => Alg.eqk y (Alg.bits n P)) fun k =>
        x ⟨a + k.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left k.isLt a) h⟩ := by
    funext x
    rw [eqN_eq]
    unfold Alg.eqN
    congr 1
    funext k
    rw [Nat.zero_add, sh_nat x (Nat.lt_of_lt_of_le (Nat.add_lt_add_left k.isLt a) h)]
  rw [e]
  exact deg_block h _ (Alg.DegLE.eqk _)

/-- The equality polynomial of a point u and the first coordinates. -/
theorem deg_eqPt0 {g n : ℕ} (h : n ≤ g) (u : ℕ → E) :
    Alg.DegLE (dBlk g 0 n) fun x : Fin g → E => eqPt n u (nat x) := by
  have e : (fun x : Fin g → E => eqPt n u (nat x)) =
      fun x : Fin g → E => eqPt n u (sh (nat x) 0) := by
    funext x
    unfold eqPt sh
    exact prod_congr rfl fun k _ => by rw [Nat.zero_add]
  rw [e]
  exact deg_eqPt (by omega) u

/-! ## What a factor reads -/

/-- The equality polynomial reads n coordinates of its second point. -/
theorem eqPt_reads {n : ℕ} (u : ℕ → E) {ξ ξ' : ℕ → E} (h : ∀ k < n, ξ k = ξ' k) :
    eqPt n u ξ = eqPt n u ξ' := by
  unfold eqPt
  exact prod_congr rfl fun k hk => by rw [h k (mem_range.mp hk)]

/-- The product of coordinates reads n coordinates. -/
theorem ones_reads {n : ℕ} {ξ ξ' : ℕ → E} (h : ∀ k < n, ξ k = ξ' k) : ones n ξ = ones n ξ' := by
  unfold ones
  exact prod_congr rfl fun k hk => h k (mem_range.mp hk)

/-- The equality weight reads n coordinates. -/
theorem eqN_reads {n : ℕ} {ξ ξ' : ℕ → E} (h : ∀ k < n, ξ k = ξ' k) (P : ℕ) :
    eqN n 0 ξ P = eqN n 0 ξ' P := by
  unfold eqN
  exact prod_congr rfl fun k hk => by rw [Nat.zero_add, h k (mem_range.mp hk)]

omit [Field E] in
/-- A stretch of two points that agree on the first g coordinates. -/
theorem sh_reads {g a n : ℕ} (h : a + n ≤ g) {ξ ξ' : ℕ → E} (hξ : ∀ k < g, ξ k = ξ' k) :
    ∀ k < n, sh ξ a k = sh ξ' a k := fun k hk => hξ (a + k) (by omega)

variable (D : Dim) (C : Calls) (p : Pub E)

/-! ## The four weights -/

/-- The weight of step s8 is the extension of its values on the cube. -/
theorem wbExt8 (b : ℕ) (ξ : ℕ → E) :
    Blocks.ext (Step.s8.g D) (fun X => Wb D C p .s8 b (cubePt (Step.s8.g D) X)) ξ =
      Wb D C p .s8 b ξ := by
  refine ext_of_deg (g := D.lg + D.lT) (fun ξ => Wb D C p .s8 b ξ) (fun ξ ξ' h => ?_) ?_ ξ
  · show _ * eqPt D.lg _ ξ * eqPt D.lT _ (sh ξ D.lg) =
      _ * eqPt D.lg _ ξ' * eqPt D.lT _ (sh ξ' D.lg)
    rw [eqPt_reads _ (fun k hk => h k (by omega)), eqPt_reads _ (sh_reads (le_refl _) h)]
  · exact (((deg_eqPt0 (Nat.le_add_right _ _) (yg D C p.z)).const_mul (wp D C p.z .w3 b)).mul
      (deg_eqPt (le_refl _) (yi D C p.z))).mono fun i => by
        unfold dBlk
        split_ifs <;> omega

/-- The weight of step s6d is the extension of its values on the cube. -/
theorem wbExt6d (b : ℕ) (ξ : ℕ → E) :
    Blocks.ext (Step.s6d.g D) (fun X => Wb D C p .s6d b (cubePt (Step.s6d.g D) X)) ξ =
      Wb D C p .s6d b ξ := by
  refine ext_of_deg (g := D.lg + (D.lP + 1) + D.ln) (fun ξ => Wb D C p .s6d b ξ)
    (fun ξ ξ' h => ?_) ?_ ξ
  · show _ * eqPt D.lg _ ξ * eqPt (D.lP + 1) _ (sh ξ D.lg) =
      _ * eqPt D.lg _ ξ' * eqPt (D.lP + 1) _ (sh ξ' D.lg)
    rw [eqPt_reads _ (fun k hk => h k (by omega)),
      eqPt_reads _ (sh_reads (Nat.le_add_right _ _) h)]
  · exact (((deg_eqPt0 (by omega) (zgD D C p.z)).const_mul (wp D C p.z .d1 b)).mul
      (deg_eqPt (Nat.le_add_right _ _) (zID D C p.z))).mono fun i => by
        unfold dBlk
        split_ifs <;> omega

/-- The weight of step s6b is the extension of its values on the cube. -/
theorem wbExt6b (b : ℕ) (ξ : ℕ → E) :
    Blocks.ext (Step.s6b.g D) (fun X => Wb D C p .s6b b (cubePt (Step.s6b.g D) X)) ξ =
      Wb D C p .s6b b ξ := by
  refine ext_of_deg (g := D.lg + D.lP + (D.lP + 1) + D.ln) (fun ξ => Wb D C p .s6b b ξ)
    (fun ξ ξ' h => ?_) ?_ ξ
  · show _ * eqPt D.lg _ ξ * eqPt D.lP _ (sh ξ D.lg) *
        (eqPt (D.lP + 1) _ (sh ξ (D.lg + D.lP)) - _ * ones (D.lP + 1) (sh ξ (D.lg + D.lP))) =
      _ * eqPt D.lg _ ξ' * eqPt D.lP _ (sh ξ' D.lg) *
        (eqPt (D.lP + 1) _ (sh ξ' (D.lg + D.lP)) - _ * ones (D.lP + 1) (sh ξ' (D.lg + D.lP)))
    rw [eqPt_reads _ (fun k hk => h k (by omega)),
      eqPt_reads (n := D.lP) _ (sh_reads (by omega) h),
      eqPt_reads (n := D.lP + 1) _ (sh_reads (Nat.le_add_right _ _) h),
      ones_reads (sh_reads (Nat.le_add_right _ _) h)]
  · exact ((((deg_eqPt0 (by omega) (zg D C p.z)).const_mul (wp D C p.z .m1 b)).mul
      (deg_eqPt (by omega) (zP D C p.z))).mul
      ((deg_eqPt (Nat.le_add_right _ _) (zs D C p.z)).sub
        ((deg_ones (Nat.le_add_right _ _)).const_mul (ones (D.lP + 1) (zs D C p.z))))).mono
      fun i => by
        unfold dBlk
        split_ifs <;> omega

/-- The weight of step s11 is the extension of its values on the cube. -/
theorem wbExt11 (b : ℕ) (ξ : ℕ → E) :
    Blocks.ext (Step.s11.g D) (fun X => Wb D C p .s11 b (cubePt (Step.s11.g D) X)) ξ =
      Wb D C p .s11 b ξ := by
  refine ext_of_deg (g := D.lg + D.lP + (D.lP + 1) + D.lB) (fun ξ => Wb D C p .s11 b ξ)
    (fun ξ ξ' h => ?_) ?_ ξ
  · show _ * eqPt D.lg _ ξ * (∑ P ∈ range D.hP, ∑ s ∈ range (D.nBlk - 1),
        eqN D.lP 0 (sh ξ D.lg) P * eqN (D.lP + 1) 0 (sh ξ (D.lg + D.lP)) s * _) =
      _ * eqPt D.lg _ ξ' * (∑ P ∈ range D.hP, ∑ s ∈ range (D.nBlk - 1),
        eqN D.lP 0 (sh ξ' D.lg) P * eqN (D.lP + 1) 0 (sh ξ' (D.lg + D.lP)) s * _)
    rw [eqPt_reads _ (fun k hk => h k (by omega))]
    congr 1
    refine sum_congr rfl fun P _ => sum_congr rfl fun s _ => ?_
    rw [eqN_reads (n := D.lP) (sh_reads (by omega) h) P,
      eqN_reads (n := D.lP + 1) (sh_reads (Nat.le_add_right _ _) h) s]
  · exact (((deg_eqPt0 (by omega) (yg D C p.z)).const_mul (wp D C p.z .w3 b)).mul
      (Alg.DegLE.sum (range D.hP) fun P _ => Alg.DegLE.sum (range (D.nBlk - 1)) fun s _ =>
        ((deg_eqN (g := D.lg + D.lP + (D.lP + 1) + D.lB) (a := D.lg) (n := D.lP) (by omega) P).mul
          (deg_eqN (a := D.lg + D.lP) (n := D.lP + 1) (Nat.le_add_right _ _) s)).mul_const
          (eqN (D.lP + 1) 0 (yI D C p.z) (D.rowBlk P s)))).mono fun i => by
        unfold dBlk
        split_ifs <;> omega

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.wbExt8
#print axioms OnBytes.Road.Rows.wbExt6d
#print axioms OnBytes.Road.Rows.wbExt6b
#print axioms OnBytes.Road.Rows.wbExt11
