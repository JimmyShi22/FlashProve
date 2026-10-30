-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Code/Field.lean: the base field `FGold`, the extension field `EGold`, and cubic extensions.

  `FGold`, `EGold`  The integers modulo p = 2^64 - 2^32 + 1, and FGold[x] / (x^3 - 7). Proved: p is
                    prime (`pGold_prime`), 7 is not a cube, and the numbers of elements.
  `Cubic K c`       The ring K[x] / (x^3 - c) for any commutative ring K, as triples (c0, c1, c2) =
                    c0 + c1 x + c2 x^2 with explicit operations. For a non-trivial K the
                    homomorphism of K-algebras `Cubic.toQuot` into Mathlib's quotient
                    `AdjoinRoot (X^3 - C c)` is bijective (`toQuot_injective`, `toQuot_surjective`).
                    `Cubic K c` is a field if K is a field in which c is not a cube; it has (card
                    K)^3 elements and the characteristic of K.
  `powMod`          a^n mod m by repeated squaring, so that Lean's kernel can evaluate a power with
                    a 64-bit exponent.

Most numbers are checked by `decide +kernel`: Lean's kernel evaluates both sides with its own
arithmetic of long numbers. This adds no axiom.

Notation: `digits` (`powMod m digits a n`): a natural number; `powMod` is a^n mod m for an exponent
n of at most "digits" binary digits.

Limits: for `FGold`, `EGold` the bound p^3 < 2^192 is not proved here.
-/
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Prime
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Code

open Polynomial

/-! ## 1. The ring K[x] / (x^3 - c) as triples -/

/-- The ring K[x] / (x^3 - c). An element is a triple (c0, c1, c2) that stands for c0 + c1 x + c2
x^2. -/
@[ext] structure Cubic (K : Type) (c : K) where
  c0 : K
  c1 : K
  c2 : K

namespace Cubic

variable {K : Type} {c : K}

/-- The bijection between K[x] / (x^3 - c) and triples of elements of K. -/
def equivProd : Cubic K c ≃ K × K × K where
  toFun a := (a.c0, a.c1, a.c2)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [DecidableEq K] : DecidableEq (Cubic K c) := equivProd.decidableEq

/-- The enumeration of all elements. It is marked irreducible so that the elaborator never unfolds
the number of elements into an enumeration; proofs use Cubic.card. -/
@[irreducible] def fintype [Fintype K] : Fintype (Cubic K c) := Fintype.ofEquiv _ equivProd.symm

instance [Fintype K] : Fintype (Cubic K c) := fintype

/-- K[x] / (x^3 - c) has (card K)^3 elements. -/
theorem card [Fintype K] : Fintype.card (Cubic K c) = Fintype.card K ^ 3 := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod, Fintype.card_prod]
  ring

section Ring

variable [CommRing K]

instance : Zero (Cubic K c) := ⟨⟨0, 0, 0⟩⟩
instance : One (Cubic K c) := ⟨⟨1, 0, 0⟩⟩
instance : Add (Cubic K c) := ⟨fun a b => ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩⟩
instance : Neg (Cubic K c) := ⟨fun a => ⟨-a.c0, -a.c1, -a.c2⟩⟩
instance : Sub (Cubic K c) := ⟨fun a b => ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2⟩⟩
/-- The product of two polynomials of degree at most 2, reduced with x^3 = c. -/
instance : Mul (Cubic K c) := ⟨fun a b => ⟨a.c0 * b.c0 + c * (a.c1 * b.c2 + a.c2 * b.c1),
  a.c0 * b.c1 + a.c1 * b.c0 + c * (a.c2 * b.c2), a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0⟩⟩
instance : SMul ℕ (Cubic K c) := ⟨fun n a => ⟨n • a.c0, n • a.c1, n • a.c2⟩⟩
instance : SMul ℤ (Cubic K c) := ⟨fun n a => ⟨n • a.c0, n • a.c1, n • a.c2⟩⟩
instance : NatCast (Cubic K c) := ⟨fun n => ⟨n, 0, 0⟩⟩
instance : IntCast (Cubic K c) := ⟨fun n => ⟨n, 0, 0⟩⟩

@[simp] theorem zero_c0 : (0 : Cubic K c).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Cubic K c).c1 = 0 := rfl
@[simp] theorem zero_c2 : (0 : Cubic K c).c2 = 0 := rfl
@[simp] theorem one_c0 : (1 : Cubic K c).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Cubic K c).c1 = 0 := rfl
@[simp] theorem one_c2 : (1 : Cubic K c).c2 = 0 := rfl
@[simp] theorem add_c0 (a b : Cubic K c) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Cubic K c) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem add_c2 (a b : Cubic K c) : (a + b).c2 = a.c2 + b.c2 := rfl
@[simp] theorem neg_c0 (a : Cubic K c) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Cubic K c) : (-a).c1 = -a.c1 := rfl
@[simp] theorem neg_c2 (a : Cubic K c) : (-a).c2 = -a.c2 := rfl
@[simp] theorem sub_c0 (a b : Cubic K c) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : Cubic K c) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem sub_c2 (a b : Cubic K c) : (a - b).c2 = a.c2 - b.c2 := rfl
@[simp] theorem mul_c0 (a b : Cubic K c) :
    (a * b).c0 = a.c0 * b.c0 + c * (a.c1 * b.c2 + a.c2 * b.c1) := rfl
@[simp] theorem mul_c1 (a b : Cubic K c) :
    (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 + c * (a.c2 * b.c2) := rfl
@[simp] theorem mul_c2 (a b : Cubic K c) : (a * b).c2 = a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 :=
  rfl
@[simp] theorem nsmul_c0 (n : ℕ) (a : Cubic K c) : (n • a).c0 = n • a.c0 := rfl
@[simp] theorem nsmul_c1 (n : ℕ) (a : Cubic K c) : (n • a).c1 = n • a.c1 := rfl
@[simp] theorem nsmul_c2 (n : ℕ) (a : Cubic K c) : (n • a).c2 = n • a.c2 := rfl
@[simp] theorem zsmul_c0 (n : ℤ) (a : Cubic K c) : (n • a).c0 = n • a.c0 := rfl
@[simp] theorem zsmul_c1 (n : ℤ) (a : Cubic K c) : (n • a).c1 = n • a.c1 := rfl
@[simp] theorem zsmul_c2 (n : ℤ) (a : Cubic K c) : (n • a).c2 = n • a.c2 := rfl
@[simp] theorem natCast_c0 (n : ℕ) : (n : Cubic K c).c0 = n := rfl
@[simp] theorem natCast_c1 (n : ℕ) : (n : Cubic K c).c1 = 0 := rfl
@[simp] theorem natCast_c2 (n : ℕ) : (n : Cubic K c).c2 = 0 := rfl
@[simp] theorem intCast_c0 (n : ℤ) : (n : Cubic K c).c0 = n := rfl
@[simp] theorem intCast_c1 (n : ℤ) : (n : Cubic K c).c1 = 0 := rfl
@[simp] theorem intCast_c2 (n : ℤ) : (n : Cubic K c).c2 = 0 := rfl

/-- K[x] / (x^3 - c) is a commutative ring, for every commutative ring K and every c. -/
instance instCommRing : CommRing (Cubic K c) where
  add_assoc a b d := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp <;> ring
  neg_add_cancel a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp <;> ring
  nsmul := (· • ·)
  nsmul_zero a := by ext <;> simp
  nsmul_succ n a := by ext <;> simp <;> ring
  zsmul := (· • ·)
  zsmul_zero' a := by ext <;> simp
  zsmul_succ' n a := by ext <;> simp <;> ring
  zsmul_neg' n a := by ext <;> simp <;> ring
  mul_assoc a b d := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  mul_comm a b := by ext <;> simp <;> ring
  left_distrib a b d := by ext <;> simp <;> ring
  right_distrib a b d := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  natCast_zero := by ext <;> simp
  natCast_succ n := by ext <;> simp
  intCast_ofNat n := by ext <;> simp
  intCast_negSucc n := by ext <;> simp

@[simp] theorem ofNat_c0 (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : Cubic K c).c0 = OfNat.ofNat n :=
  rfl
@[simp] theorem ofNat_c1 (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : Cubic K c).c1 = 0 := rfl
@[simp] theorem ofNat_c2 (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : Cubic K c).c2 = 0 := rfl

/-- The embedding of K, v ↦ (v, 0, 0). -/
def ofBase : K →+* Cubic K c where
  toFun v := ⟨v, 0, 0⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp
  map_zero' := rfl
  map_add' a b := by ext <;> simp

instance instAlgebra : Algebra K (Cubic K c) := ofBase.toAlgebra

@[simp] theorem algebraMap_c0 (v : K) : (algebraMap K (Cubic K c) v).c0 = v := rfl
@[simp] theorem algebraMap_c1 (v : K) : (algebraMap K (Cubic K c) v).c1 = 0 := rfl
@[simp] theorem algebraMap_c2 (v : K) : (algebraMap K (Cubic K c) v).c2 = 0 := rfl
@[simp] theorem smul_c0 (v : K) (a : Cubic K c) : (v • a).c0 = v * a.c0 := by
  simp [Algebra.smul_def]
@[simp] theorem smul_c1 (v : K) (a : Cubic K c) : (v • a).c1 = v * a.c1 := by
  simp [Algebra.smul_def]
@[simp] theorem smul_c2 (v : K) (a : Cubic K c) : (v • a).c2 = v * a.c2 := by
  simp [Algebra.smul_def]

/-- The embedding of K is injective. -/
theorem algebraMap_injective : Function.Injective (algebraMap K (Cubic K c)) :=
  fun _ _ h => congrArg Cubic.c0 h

/-- K[x] / (x^3 - c) has the characteristic of K. -/
instance (p : ℕ) [CharP K p] : CharP (Cubic K c) p :=
  charP_of_injective_algebraMap algebraMap_injective p

/-! ### The isomorphism with Mathlib's quotient K[X] / (X^3 - c) -/

/-- The polynomial X^3 - c. -/
abbrev poly (c : K) : K[X] := X ^ 3 - C c

/-- The class of X in Mathlib's quotient. -/
abbrev root (c : K) : AdjoinRoot (poly c) := AdjoinRoot.root (poly c)

theorem root_cube : root c ^ 3 = algebraMap K (AdjoinRoot (poly c)) c := by
  have h := AdjoinRoot.eval₂_root (X ^ 3 - C c : K[X])
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
  exact h

/-- For a non-trivial K, the powers 1, X, X^2 of the class of X are a basis of Mathlib's
quotient. -/
theorem exists_basis_adjoinRoot [Nontrivial K] :
    ∃ b : Module.Basis (Fin 3) K (AdjoinRoot (poly c)), ∀ i : Fin 3, b i = root c ^ (i : ℕ) := by
  have hm : (poly c).Monic := monic_X_pow_sub_C c (by norm_num)
  have hd : (poly c).natDegree = 3 := natDegree_X_pow_sub_C
  have hdim : (AdjoinRoot.powerBasis' hm).dim = 3 := by rw [AdjoinRoot.powerBasis'_dim, hd]
  refine ⟨(AdjoinRoot.powerBasis' hm).basis.reindex (finCongr hdim), fun i => ?_⟩
  rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis'_gen]
  rfl

/-- The homomorphism (c0, c1, c2) ↦ c0 + c1 X + c2 X^2 into Mathlib's quotient K[X] / (X^3 - c). -/
def toQuot : Cubic K c →ₐ[K] AdjoinRoot (poly c) where
  toFun a := algebraMap K _ a.c0 + algebraMap K _ a.c1 * root c + algebraMap K _ a.c2 * root c ^ 2
  map_one' := by simp
  map_zero' := by simp
  map_add' a b := by simp only [add_c0, add_c1, add_c2, map_add]; ring
  map_mul' a b := by
    have h3 := root_cube (c := c)
    have h4 : root c ^ 4 = algebraMap K (AdjoinRoot (poly c)) c * root c := by rw [pow_succ, h3]
    simp only [mul_c0, mul_c1, mul_c2, map_add, map_mul]
    linear_combination (algebraMap K (AdjoinRoot (poly c)) a.c1 *
            algebraMap K (AdjoinRoot (poly c)) b.c2 +
          algebraMap K (AdjoinRoot (poly c)) a.c2 * algebraMap K (AdjoinRoot (poly c)) b.c1) *
        (-h3) +
      (algebraMap K (AdjoinRoot (poly c)) a.c2 * algebraMap K (AdjoinRoot (poly c)) b.c2) * (-h4)
  commutes' v := by simp

theorem toQuot_apply (a : Cubic K c) :
    toQuot a =
      algebraMap K _ a.c0 + algebraMap K _ a.c1 * root c + algebraMap K _ a.c2 * root c ^ 2 := rfl

theorem toQuot_injective [Nontrivial K] : Function.Injective (toQuot (c := c)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨b, hb⟩ := exists_basis_adjoinRoot (c := c)
  have hli := Fintype.linearIndependent_iff.mp b.linearIndependent ![a.c0, a.c1, a.c2] (by
    simp only [Fin.sum_univ_three, hb, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Algebra.smul_def]
    simpa [toQuot_apply] using ha)
  ext
  · exact hli 0
  · exact hli 1
  · exact hli 2

theorem toQuot_surjective [Nontrivial K] : Function.Surjective (toQuot (c := c)) := by
  intro y
  obtain ⟨b, hb⟩ := exists_basis_adjoinRoot (c := c)
  refine ⟨⟨b.repr y 0, b.repr y 1, b.repr y 2⟩, ?_⟩
  have h := b.sum_repr y
  simp only [Fin.sum_univ_three, hb, Algebra.smul_def] at h
  refine Eq.trans ?_ h
  simp [toQuot_apply]

/-! ### The norm -/

/-- For a = c0 + c1 x + c2 x^2, the element A + B x + C x^2 with A = c0^2 - c c1 c2, B = c c2^2 - c0
c1, C = c1^2 - c0 c2.
Its product with a is the norm of a (mul_adj). -/
def adj (a : Cubic K c) : Cubic K c :=
  ⟨a.c0 ^ 2 - c * (a.c1 * a.c2), c * a.c2 ^ 2 - a.c0 * a.c1, a.c1 ^ 2 - a.c0 * a.c2⟩

/-- The norm of a, an element of K: c0 A + c (c1 C + c2 B). -/
def nrm (a : Cubic K c) : K := a.c0 * (adj a).c0 + c * (a.c1 * (adj a).c2 + a.c2 * (adj a).c1)

theorem mul_adj (a : Cubic K c) : a * adj a = algebraMap K (Cubic K c) (nrm a) := by
  ext <;> simp only [mul_c0, mul_c1, mul_c2, algebraMap_c0, algebraMap_c1, algebraMap_c2, adj, nrm]
    <;> ring

end Ring

section Field

variable [Field K]

/-- Over a field in which c is not a cube, X^3 - c is irreducible: a cubic without a root is
irreducible. -/
theorem poly_irreducible (hc : ∀ a : K, a ^ 3 ≠ c) : Irreducible (poly c) := by
  have hmonic : (X ^ 3 - C c : K[X]).Monic := monic_X_pow_sub_C c (by norm_num)
  have hdeg : (X ^ 3 - C c : K[X]).natDegree = 3 := natDegree_X_pow_sub_C
  show Irreducible (X ^ 3 - C c : K[X])
  rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three
      (by rw [hdeg]; norm_num) (by rw [hdeg])]
  refine Multiset.eq_zero_of_forall_notMem fun a ha => ?_
  rw [mem_roots hmonic.ne_zero, IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at ha
  exact hc a ha

/-- If c is not a cube, the norm of a non-zero element is not zero. -/
theorem nrm_ne_zero (hc : ∀ a : K, a ^ 3 ≠ c) {a : Cubic K c} (ha : a ≠ 0) : nrm a ≠ 0 := by
  intro hN
  haveI : Fact (Irreducible (poly c)) := ⟨poly_irreducible hc⟩
  letI : Field (AdjoinRoot (poly c)) := AdjoinRoot.instField
  have h0 : toQuot a * toQuot (adj a) = 0 := by rw [← map_mul, mul_adj, hN, map_zero, map_zero]
  have hadj : adj a = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (toQuot_injective (h.trans (map_zero _).symm)) ha
    · exact toQuot_injective (h.trans (map_zero _).symm)
  have hA : a.c0 ^ 2 - c * (a.c1 * a.c2) = 0 := congrArg Cubic.c0 hadj
  have hB : c * a.c2 ^ 2 - a.c0 * a.c1 = 0 := congrArg Cubic.c1 hadj
  have hC : a.c1 ^ 2 - a.c0 * a.c2 = 0 := congrArg Cubic.c2 hadj
  by_cases h2 : a.c2 = 0
  · rw [h2] at hA hC
    have h1 : a.c1 = 0 := by simpa using hC
    have h0 : a.c0 = 0 := by simpa using hA
    exact ha (by ext <;> simp [h2, h1, h0])
  · refine hc (a.c1 / a.c2) ?_
    rw [div_pow, div_eq_iff (pow_ne_zero 3 h2)]
    linear_combination a.c1 * hC - a.c2 * hB

/-- The inverse, computed from the norm: a⁻¹ = adj a / nrm a. -/
instance : Inv (Cubic K c) :=
  ⟨fun a => ⟨(adj a).c0 * (nrm a)⁻¹, (adj a).c1 * (nrm a)⁻¹, (adj a).c2 * (nrm a)⁻¹⟩⟩

theorem inv_eq (a : Cubic K c) : a⁻¹ = adj a * algebraMap K (Cubic K c) (nrm a)⁻¹ := by
  ext <;> simp [Inv.inv]

/-- If c is not a cube in the field K, then K[x] / (x^3 - c) is a field. -/
instance instField [hc : Fact (∀ a : K, a ^ 3 ≠ c)] : Field (Cubic K c) where
  exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (α := K) (congrArg Cubic.c0 h)⟩
  mul_inv_cancel a ha := by
    rw [inv_eq, ← mul_assoc, mul_adj, ← map_mul, mul_inv_cancel₀ (nrm_ne_zero hc.out ha), map_one]
  inv_zero := by
    rw [inv_eq]
    ext <;> simp [adj]
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

end Field

end Cubic

/-- In a ring of characteristic p, a natural number strictly between 0 and p is not zero. In a field
it is then invertible. -/
theorem natCast_ne_zero_of_lt
    (R : Type) [AddMonoidWithOne R] (p : ℕ) [CharP R p] {n : ℕ} (h0 : n ≠ 0) (hn : n < p) :
    (n : R) ≠ 0 := by
  intro h
  have hd := (CharP.cast_eq_zero_iff R p n).mp h
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd) (not_le.mpr hn)

/-! ## 2. Powers modulo m by repeated squaring -/

/-- a^n mod m by repeated squaring, for an exponent n of at most "digits" binary digits. -/
def powMod (m : ℕ) : (digits a n : ℕ) → ℕ
  | 0, _, _ => 1 % m
  | digits + 1, a, n => (if n % 2 = 1 then a else 1) * powMod m digits (a * a % m) (n / 2) % m

theorem powMod_eq (m : ℕ) : ∀ (digits a n : ℕ), n < 2 ^ digits → powMod m digits a n = a ^ n % m
  | 0, a, n, h => by
    have hn : n = 0 := by simpa using h
    simp [powMod, hn]
  | digits + 1, a, n, h => by
    have hlt : n / 2 < 2 ^ digits := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      rwa [pow_succ] at h
    have hsplit : a ^ n = a ^ (n % 2) * (a * a) ^ (n / 2) := by
      rw [← pow_two, ← pow_mul, ← pow_add, Nat.mod_add_div]
    have hbit : (if n % 2 = 1 then a else 1) = a ^ (n % 2) := by
      rcases Nat.mod_two_eq_zero_or_one n with h2 | h2 <;> simp [h2]
    rw [powMod, powMod_eq m digits _ _ hlt, hbit, hsplit, ← Nat.pow_mod, Nat.mul_mod_mod]

/-- The value of a power in the integers modulo m, from an evaluation of powMod. -/
theorem natCast_pow_eq {m digits a n v : ℕ} (hn : n < 2 ^ digits) (hv : powMod m digits a n = v) :
    ((a : ℕ) : ZMod m) ^ n = ((v : ℕ) : ZMod m) := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_natCast_iff', ← hv, powMod_eq m digits a n hn, Nat.mod_mod]

/-- Under the hypotheses below, a power in the integers modulo m is not 1, from an evaluation of
powMod. -/
theorem natCast_pow_ne_one {m digits a n v : ℕ} (hn : n < 2 ^ digits) (hv : powMod m digits a n = v)
    (h1 : v % m ≠ 1 % m) : ((a : ℕ) : ZMod m) ^ n ≠ 1 := by
  rw [natCast_pow_eq hn hv]
  intro h
  have h' : ((v : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by rw [h, Nat.cast_one]
  exact h1 ((ZMod.natCast_eq_natCast_iff' v 1 m).mp h')

/-- Modulo a prime p with 3 ∣ p - 1, a non-zero c with c^((p-1)/3) ≠ 1 is not a cube, by Fermat's
little theorem. -/
theorem not_cube_of_pow_ne_one {p : ℕ} [Fact p.Prime] {c : ZMod p} (h0 : c ≠ 0) (h3 : 3 ∣ p - 1)
    (hc : c ^ ((p - 1) / 3) ≠ 1) : ∀ a : ZMod p, a ^ 3 ≠ c := by
  intro a ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at ha
    exact h0 ha.symm
  apply hc
  rw [← ha, ← pow_mul, Nat.mul_div_cancel' h3]
  exact ZMod.pow_card_sub_one_eq_one ha0

/-! ## 3. The fields `FGold` and `EGold`: p = 2^64 - 2^32 + 1 and x^3 = 7 -/

/-- The prime 2^64 - 2^32 + 1. -/
def pGold : ℕ := 2 ^ 64 - 2 ^ 32 + 1

theorem pGold_eq : pGold = 18446744069414584321 := by decide +kernel

/-- p - 1 = 2^32 · 3 · 5 · 17 · 257 · 65537. -/
theorem pGold_sub_one : pGold - 1 = 2 ^ 32 * 3 * 5 * 17 * 257 * 65537 := by decide +kernel

/-- 2^64 - 2^32 + 1 is prime, by Lucas' test: 7 has order exactly p - 1 modulo p. -/
theorem pGold_prime : Nat.Prime pGold := by
  have h7 : ((7 : ℕ) : ZMod pGold) ^ (pGold - 1) = 1 := by
    have h := natCast_pow_eq (m := pGold) (digits := 64) (a := 7) (n := pGold - 1) (v := 1)
      (by decide +kernel) (by decide +kernel)
    simpa using h
  refine lucas_primality pGold ((7 : ℕ) : ZMod pGold) h7 fun q hq hdvd => ?_
  have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 17 ∨ q = 257 ∨ q = 65537 := by
    rw [pGold_sub_one] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
          · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
            · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
            · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h))
          · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h)))
        · exact Or.inr
            (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h))))
      · exact Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h)))))
    · exact Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h)))))
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact natCast_pow_ne_one (digits := 64) (v := 18446744069414584320) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact natCast_pow_ne_one (digits := 64) (v := 18446744065119617025) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact natCast_pow_ne_one (digits := 64) (v := 1373043270956696022) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact natCast_pow_ne_one (digits := 64) (v := 16301593560560007290) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact natCast_pow_ne_one (digits := 64) (v := 995085315851368103) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact natCast_pow_ne_one (digits := 64) (v := 8478886009461009681) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

instance : Fact (Nat.Prime pGold) := ⟨pGold_prime⟩

/-- The base field: the integers modulo 2^64 - 2^32 + 1. -/
abbrev FGold : Type := ZMod pGold

/-- 7^((p-1)/3) = 2^64 - 2^33 + 1 in `FGold`. -/
theorem seven_pow_third_pGold :
    (7 : FGold) ^ ((pGold - 1) / 3) = ((2 ^ 64 - 2 ^ 33 + 1 : ℕ) : FGold) := by
  have h := natCast_pow_eq (m := pGold) (digits := 64) (a := 7) (n := (pGold - 1) / 3)
    (v := 2 ^ 64 - 2 ^ 33 + 1) (by decide +kernel) (by decide +kernel)
  rw [← h]
  norm_num

/-- 7 is not a cube modulo 2^64 - 2^32 + 1. -/
theorem seven_not_cube_pGold : ∀ a : FGold, a ^ 3 ≠ 7 := by
  have h7 : ((7 : ℕ) : FGold) = 7 := by norm_num
  rw [← h7]
  refine not_cube_of_pow_ne_one
    (natCast_ne_zero_of_lt FGold pGold (by norm_num) (by decide +kernel)) (by decide +kernel) ?_
  exact natCast_pow_ne_one (digits := 64) (v := 18446744065119617025) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

instance : Fact (∀ a : FGold, a ^ 3 ≠ 7) := ⟨seven_not_cube_pGold⟩

/-- A cubic extension of `FGold`: FGold[x] / (x^3 - 7). -/
abbrev EGold : Type := Cubic FGold 7

theorem card_FGold : Fintype.card FGold = pGold := ZMod.card pGold

theorem card_EGold : Fintype.card EGold = pGold ^ 3 := by rw [Cubic.card, card_FGold]

/-- 2 is invertible in `EGold`. -/
theorem two_ne_zero_EGold : (2 : EGold) ≠ 0 := by
  simpa using natCast_ne_zero_of_lt EGold pGold (n := 2) (by norm_num) (by decide +kernel)

/-! ## The instances that the rest of the library needs of a pair of fields -/

example : Field EGold := inferInstance
example : Algebra FGold EGold := inferInstance

end Code
