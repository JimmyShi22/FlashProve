-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gl/GlField.lean: the prime p = 2^64 - 2^32 + 1, the cubic extension by x^3 = 2, and the subgroup
of order 2^32 with a named generator.

Definitions, statements (in `Cb.Gl.Spec`) and proofs. No code, no protocol occurs here; the file
imports Code/Field.lean and Mathlib only.

From Code/Field.lean: `Code.pGold` = 2^64 - 2^32 + 1 with `Code.pGold_prime` (Lucas' test: 7 has
order exactly p - 1; p - 1 = 2^32 · 3 · 5 · 17 · 257 · 65537; each power by repeated squaring,
evaluated by Lean's kernel). That file has the extension by x^3 = 7; here: x^3 = 2.

Main names:
  `F`, `E`: the integers modulo p; F[x] / (x^3 - 2).
  `Spec.gl_prime`: p is prime (restated with the number written out).
  `Spec.gl_two_pow`, `Spec.gl_two_not_cube`: 2^((p-1)/3) = 2^32 - 1 in F, which is not 1: so 2 is no
    cube modulo p, and E is a field (instance).
  `Spec.gl_card`: F has p elements, E has p^3, and 2^191 < p^3 < 2^192.
  `gen`: the named generator: 1,753,635,133,440,165,772 = 7^((p-1)/2^32) (`Spec.gl_gen_eq`).
  `root a`, `Spec.gl_root_order`, `Spec.gl_root_primitive`: gen^(2^(32-a)): of order exactly 2^a, a
    primitive 2^a-th root of unity, for every a ≤ 32.
  `pts a`: the points of length 2^a: i ↦ (root a)^i, i < 2^a.
  `Spec.gl_pts_pow`, `Spec.gl_pts_nest`: for a ≤ 32 each is a 2^a-th root of unity; for a < 32 the
    points of length 2^a are the points of length 2^(a+1) with even number.

How numbers are checked: "decide +kernel": Lean's kernel evaluates both sides with its own
arithmetic of long numbers. This adds no axiom.

Limits: this file says nothing on lengths above 2^32 (unions of cosets), but for
`Spec.gl_pts_ne_zero`, which does not ask a ≤ 32. It says nothing on speed of arithmetic.
-/
import Code.Field
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option autoImplicit false

namespace Cb.Gl
open Code

/-- The prime, and (next) the integers modulo it. -/
abbrev p : ℕ := Code.pGold
abbrev F : Type := Code.FGold

/-- The named generator of the subgroup of order 2^32. -/
def gen : F := ((1753635133440165772 : ℕ) : F)

/-- For a ≤ 32, a generator of the subgroup of order 2^a. -/
def root (a : ℕ) : F := gen ^ 2 ^ (32 - a)

/-- The points of length 2^a. -/
def pts (a : ℕ) : Fin (2 ^ a) → F := fun i => root a ^ (i : ℕ)

namespace Spec

def gl_prime : Prop := Nat.Prime (2 ^ 64 - 2 ^ 32 + 1)

def gl_two_pow : Prop := (2 : F) ^ ((p - 1) / 3) = ((2 ^ 32 - 1 : ℕ) : F)

/-- 2 is no cube modulo p. -/
def gl_two_not_cube : Prop := ∀ a : F, a ^ 3 ≠ 2

def gl_gen_eq : Prop := gen = (7 : F) ^ ((p - 1) / 2 ^ 32)

/-- The generator has order exactly 2^32. -/
def gl_gen_order : Prop := orderOf gen = 2 ^ 32

def gl_root_order : Prop := ∀ a, a ≤ 32 → orderOf (root a) = 2 ^ a

def gl_root_primitive : Prop := ∀ a, a ≤ 32 → IsPrimitiveRoot (root a) (2 ^ a)

/-- For a ≤ 32 the points are distinct. -/
def gl_pts_inj : Prop := ∀ a, a ≤ 32 → Function.Injective (pts a)

/-- No point is 0. -/
def gl_pts_ne_zero : Prop := ∀ a i, pts a i ≠ 0

def gl_pts_pow : Prop := ∀ a, a ≤ 32 → ∀ i, pts a i ^ 2 ^ a = 1

def gl_pts_nest : Prop :=
  ∀ a, a < 32 →
    ∀ (i : Fin (2 ^ a)) (j : Fin (2 ^ (a + 1))), (j : ℕ) = 2 * (i : ℕ) → pts a i = pts (a + 1) j

end Spec

theorem gl_prime : Spec.gl_prime := Code.pGold_prime

theorem gl_two_pow : Spec.gl_two_pow := by
  have h := natCast_pow_eq (m := pGold) (digits := 64) (a := 2) (n := (pGold - 1) / 3)
    (v := 2 ^ 32 - 1) (by decide +kernel) (by decide +kernel)
  show (2 : FGold) ^ ((pGold - 1) / 3) = ((2 ^ 32 - 1 : ℕ) : FGold)
  rw [← h]
  norm_num

theorem gl_two_not_cube : Spec.gl_two_not_cube := by
  have h2 : ((2 : ℕ) : FGold) = 2 := by norm_num
  show ∀ a : FGold, a ^ 3 ≠ 2
  rw [← h2]
  refine not_cube_of_pow_ne_one
    (natCast_ne_zero_of_lt FGold pGold (by norm_num) (by decide +kernel)) (by decide +kernel) ?_
  exact natCast_pow_ne_one (digits := 64) (v := 4294967295) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

instance : Fact (∀ a : F, a ^ 3 ≠ 2) := ⟨gl_two_not_cube⟩

/-- The challenge field: F[x] / (x^3 - 2). -/
abbrev E : Type := Cubic F 2

namespace Spec
/-- The numbers of elements. -/
def gl_card : Prop :=
  Fintype.card F = p ∧ Fintype.card E = p ^ 3 ∧ 2 ^ 191 < p ^ 3 ∧ p ^ 3 < 2 ^ 192
end Spec

theorem gl_card : Spec.gl_card :=
  ⟨card_FGold,
    (Cubic.card (K := F) (c := 2)).trans (congrArg (· ^ 3) card_FGold),
    by decide +kernel, by decide +kernel⟩

theorem gl_gen_eq : Spec.gl_gen_eq := by
  have h := natCast_pow_eq (m := pGold) (digits := 64) (a := 7) (n := (pGold - 1) / 2 ^ 32)
    (v := 1753635133440165772) (by decide +kernel) (by decide +kernel)
  show ((1753635133440165772 : ℕ) : FGold) = (7 : FGold) ^ ((pGold - 1) / 2 ^ 32)
  rw [← h]
  norm_num

theorem gen_pow_top : gen ^ 2 ^ (31 + 1) = 1 := by
  have h := natCast_pow_eq (m := pGold) (digits := 33) (a := 1753635133440165772)
    (n := 2 ^ (31 + 1)) (v := 1) (by decide +kernel) (by decide +kernel)
  simpa using h

theorem gen_pow_half : ¬ gen ^ 2 ^ 31 = 1 :=
  natCast_pow_ne_one (m := pGold) (digits := 32) (a := 1753635133440165772) (n := 2 ^ 31)
    (v := 18446744069414584320) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem gl_gen_order : Spec.gl_gen_order := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow gen_pow_half gen_pow_top

theorem gl_root_order : Spec.gl_root_order := by
  intro a ha
  unfold root
  rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num))
        (by rw [gl_gen_order]; exact pow_dvd_pow 2 (Nat.sub_le 32 a)),
    gl_gen_order, Nat.pow_div (Nat.sub_le 32 a) (by norm_num), Nat.sub_sub_self ha]

theorem gl_root_primitive : Spec.gl_root_primitive := by
  intro a ha
  have h := IsPrimitiveRoot.orderOf (root a)
  rwa [gl_root_order a ha] at h

theorem gl_pts_inj : Spec.gl_pts_inj := by
  intro a ha i j hij
  have hi : (i : ℕ) ∈ Set.Iio (orderOf (root a)) := by rw [gl_root_order a ha]; exact i.2
  have hj : (j : ℕ) ∈ Set.Iio (orderOf (root a)) := by rw [gl_root_order a ha]; exact j.2
  exact Fin.ext (pow_injOn_Iio_orderOf hi hj hij)

theorem gen_ne_zero : gen ≠ 0 := by
  intro h
  have h1 := gen_pow_top
  rw [h, zero_pow (pow_ne_zero _ (by norm_num))] at h1
  exact zero_ne_one h1

theorem gl_pts_ne_zero : Spec.gl_pts_ne_zero := fun _ _ => pow_ne_zero _ (pow_ne_zero _ gen_ne_zero)

theorem gl_pts_pow : Spec.gl_pts_pow := by
  intro a ha i
  have h : root a ^ 2 ^ a = 1 := by
    have h0 := pow_orderOf_eq_one (root a)
    rwa [gl_root_order a ha] at h0
  unfold pts
  rw [← pow_mul, mul_comm, pow_mul, h, one_pow]

theorem gl_pts_nest : Spec.gl_pts_nest := by
  intro a ha i j hj
  unfold pts root
  rw [hj, ← pow_mul, ← pow_mul, ← mul_assoc, ← pow_succ]
  congr 3
  omega

example : Field F := inferInstance
example : Fintype F := inferInstance
example : DecidableEq F := inferInstance
example : Field E := inferInstance
example : Fintype E := inferInstance
example : DecidableEq E := inferInstance
example : Algebra F E := inferInstance
example : CharP E p := inferInstance

end Cb.Gl
