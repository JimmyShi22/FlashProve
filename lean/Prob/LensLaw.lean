-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Prob/LensLaw.lean: a uniform element seen through a lens.

A lens is a getter tst : C → Z with a setter set : Z → C → C such that what is set is read back,
setting what is read changes nothing, and the last setting counts (`Lens.OK`). Then, under the
uniform distribution on C (C and Z finite and non-empty), tst c is uniform on Z (`map_tst`), set z c
is uniform on C for independent uniform z (`map_set`), and what the lens shows is independent of the
rest (`map_pair`, `pr_indep`). The proofs use that (z, c) ↦ (tst c, set z c) is an involution of
Z × C (`swap`).

Without a lens: the b lowest bits of a uniform number below 2^b are b uniform bits (`map_bitsOf`);
`bind_congr_on`; `fibres_unique`.

No oracle occurs in this file. It is used in Compile/Batch/LoopLaw.lean.

Notation: `tst`, `set`: in `lens` there the fields of `GrW` (Iop/BatchWire.lean): `tst`: the test
bits of a verifier message; `set`: the verifier message with other test bits; so there C is the type
of verifier messages and Z is `Fin b → Bool`.
-/
import Prob.Linear
import Prob.LawKit

open scoped ENNReal

namespace Prob
namespace Lens

variable {C Z : Type} (tst : C → Z) (set : Z → C → C)

/-- the laws of a lens -/
structure OK : Prop where
  tst_set : ∀ z c, tst (set z c) = z
  set_tst : ∀ c, set (tst c) c = c
  set_set : ∀ z z' c, set z (set z' c) = set z c

variable {tst set}

/-- Under `OK`, (z, c) ↦ (tst c, set z c) is an involution. -/
def swap (h : OK tst set) : Z × C ≃ Z × C where
  toFun p := (tst p.2, set p.1 p.2)
  invFun p := (tst p.2, set p.1 p.2)
  left_inv p := by
    show (tst (set p.1 p.2), set (tst p.2) (set p.1 p.2)) = p
    rw [h.tst_set, h.set_set, h.set_tst]
  right_inv p := by
    show (tst (set p.1 p.2), set (tst p.2) (set p.1 p.2)) = p
    rw [h.tst_set, h.set_set, h.set_tst]

variable [Fintype C] [Nonempty C] [Fintype Z] [Nonempty Z]

omit tst set in
theorem map_snd : (unif (Z × C)).map Prod.snd = unif C := by
  rw [map_unif_prod]
  show (unif Z).bind (fun _ => (unif C).map id) = _
  rw [PMF.map_id, PMF.bind_const]

omit tst set in
theorem map_fst : (unif (Z × C)).map Prod.fst = unif Z := by
  rw [map_unif_prod]
  have e : ∀ a : Z, ((unif C).map fun b => ((a, b) : Z × C).1) = PMF.pure a := fun a =>
    PMF.map_const _ a
  rw [funext e, PMF.bind_pure]

/-- Under `OK`, for independent uniform z and c: set z c is uniform. -/
theorem map_set (h : OK tst set) : (unif (Z × C)).map (fun p => set p.1 p.2) = unif C := by
  have e : (fun p : Z × C => set p.1 p.2) = Prod.snd ∘ swap h := rfl
  rw [e, ← PMF.map_comp, map_unif_equiv]
  exact map_snd

/-- Under `OK`, tst c is uniform for uniform c. -/
theorem map_tst (h : OK tst set) : (unif C).map tst = unif Z := by
  have e1 : (unif (Z × C)).map (fun p => tst p.2) = unif Z := by
    have e : (fun p : Z × C => tst p.2) = Prod.fst ∘ swap h := rfl
    rw [e, ← PMF.map_comp, map_unif_equiv]
    exact map_fst
  have e2 : (fun p : Z × C => tst p.2) = tst ∘ Prod.snd := rfl
  rw [e2, ← PMF.map_comp, map_snd] at e1
  exact e1

/-- Under `OK`, (tst c, set z₀ c) has the distribution of (z, set z₀ c) for independent uniform z
and c: what the lens shows is independent of the rest. -/
theorem map_pair (h : OK tst set) (z₀ : Z) :
    (unif C).map (fun c => (tst c, set z₀ c)) = (unif (Z × C)).map fun p => (p.1, set z₀ p.2) := by
  rw [← map_set h, PMF.map_comp]
  refine congrArg (fun f => (unif (Z × C)).map f) (funext fun p => ?_)
  show (tst (set p.1 p.2), set z₀ (set p.1 p.2)) = _
  rw [h.tst_set, h.set_set]

/-- `map_pair` as a product of probabilities: an event A on what the lens shows, and an event B on
the element with z₀ written over what the lens shows. -/
theorem pr_indep (h : OK tst set) (z₀ : Z) (A : Set Z) (B : Set C) :
    pr (unif C) {c | set z₀ c ∈ B ∧ tst c ∈ A} =
      pr (unif C) {c | set z₀ c ∈ B} * pr (unif C) {c | tst c ∈ A} := by
  have e1 : pr (unif C) {c | set z₀ c ∈ B ∧ tst c ∈ A} =
      pr ((unif C).map fun c => (tst c, set z₀ c)) (A ×ˢ B) := by
    rw [pr_map]
    exact congrArg _ (Set.ext fun c => and_comm)
  have e2 : pr ((unif (Z × C)).map fun p => (p.1, set z₀ p.2)) (A ×ˢ B) =
      pr (unif Z) A * pr (unif C) {c | set z₀ c ∈ B} := by
    rw [pr_map, unif_prod]
    exact pr_prod_rect (unif Z) (unif C) A {c | set z₀ c ∈ B}
  have e3 : pr (unif C) {c | tst c ∈ A} = pr (unif Z) A := by
    rw [← map_tst h, pr_map]
    rfl
  rw [e1, map_pair h z₀, e2, e3, mul_comm]

end Lens

/-! ## Bits of a number; a congruence for bind -/

/-- the b lowest bits of a number -/
def bitsOf (b : ℕ) (r : Fin (2 ^ b - 1 + 1)) : Fin b → Bool := fun i => r.val.testBit i.val

theorem bitsOf_bijective (b : ℕ) : Function.Bijective (bitsOf b) := by
  have hp : 2 ^ b - 1 + 1 = 2 ^ b := Nat.sub_add_cancel Nat.one_le_two_pow
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun x y hxy => ?_, by simp [hp]⟩
  refine Fin.ext (Nat.eq_of_testBit_eq fun i => ?_)
  by_cases hi : i < b
  · exact congrFun hxy ⟨i, hi⟩
  · have hx : x.val < 2 ^ i :=
      lt_of_lt_of_le (lt_of_lt_of_eq x.isLt hp)
        (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hi))
    have hy : y.val < 2 ^ i :=
      lt_of_lt_of_le (lt_of_lt_of_eq y.isLt hp)
        (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hi))
    rw [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]

/-- The bits of a uniform number are uniform bits. -/
theorem map_bitsOf (b : ℕ) : (unif (Fin (2 ^ b - 1 + 1))).map (bitsOf b) = unif (Fin b → Bool) :=
  map_unif_of_bijective (bitsOf_bijective b)

/-- p.bind f = p.bind g if f and g agree on the support of p. -/
theorem bind_congr_on {α β : Type} (p : PMF α) {f g : α → PMF β} (h : ∀ a ∈ p.support, f a = g a) :
    p.bind f = p.bind g := by
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : p a = 0
  · rw [ha, zero_mul, zero_mul]
  · rw [h a ((PMF.mem_support_iff _ _).2 ha)]

/-! ## Families of distributions with disjoint supports -/

/-- Two families of distributions, the z-th supported on {χ = z}, with the same mixture under the
uniform distribution on Z, are the same. -/
theorem fibres_unique {R Z : Type} [Fintype Z] [Nonempty Z] [DecidableEq Z] (χ : R → Z)
    (μ ν : Z → PMF R) (hμ : ∀ z x, x ∈ (μ z).support → χ x = z)
    (hν : ∀ z x, x ∈ (ν z).support → χ x = z) (h : (unif Z).bind μ = (unif Z).bind ν) (z : Z) :
    μ z = ν z := by
  ext x
  by_cases hx : χ x = z
  · have key : ∀ κ : Z → PMF R, (∀ z x, x ∈ (κ z).support → χ x = z) →
        ((unif Z).bind κ) x = (Fintype.card Z : ℝ≥0∞)⁻¹ * κ z x := by
      intro κ hκ
      rw [PMF.bind_apply, tsum_eq_single z, PMF.uniformOfFintype_apply]
      intro z' hz'
      have : κ z' x = 0 := by
        by_contra hne
        exact hz' ((hκ z' x ((PMF.mem_support_iff _ _).2 hne)).symm.trans hx)
      rw [this, mul_zero]
    have e := congrArg (fun p : PMF R => p x) h
    simp only [key μ hμ, key ν hν] at e
    exact (ENNReal.mul_right_inj
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)) (ENNReal.inv_ne_top.2 (by simp))).1 e
  · have a1 : μ z x = 0 := by
      by_contra hne
      exact hx (hμ z x ((PMF.mem_support_iff _ _).2 hne))
    have a2 : ν z x = 0 := by
      by_contra hne
      exact hx (hν z x ((PMF.mem_support_iff _ _).2 hne))
    rw [a1, a2]

end Prob
