-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpNumProofs.lean: proofs for Cb/Ld/LdLkpNum.lean (numbers and corners of a cube, lowest bit
first; the levels of a forest of product trees as tables on cubes).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Defined in Cb/Ld/LdLkpNum.lean: `numLE`: the number of a corner, lowest bit first (`Alg.num` of
Alg/Mle.lean lists the top bit first); `cutOne`: the factors, cut off: 1 from N on; `cubeLvl`: level
l of a forest, as a table on the cube in g + l variables.

Main names (statements and hypotheses: Cb/Ld/LdLkpNum.lean):
  `ldLkpNum_snoc`: a further last coordinate: a further top bit.
  `ldLkpNum_rev`: numLE x = Alg.num (x read backwards).
  `ldLkpNum_lt`: numLE x < 2^k. `ldLkpNum_inj`: `numLE`, injective on the corners of a cube.
  `ldLkpNum_sum`, `ldLkpNum_prod`: sums and products over the cube: those over the numbers below
    2^k.
  `ldLkpNum_step`: an entry of a level: the product of the two entries above it, at every level.
  `ldLkpNum_lvl`: for l ≤ n: `Blocks.lvl` (Blocks/LookupRel.lean) at the number of the corner.
  `ldLkpNum_top`: level n: the factors. `ldLkpNum_root`: level 0: the products of the trees.
  `ldLkpNum_rootK`, `ldLkpNum_rootT`: the products in the lookup's identity.
  `ldLkpNum_topK`, `ldLkpNum_topT`: the leaves: λ - key; 1 + bit (λ - 1 - entry).
  `ldLkpNum_ext`: the multilinear extension of the table x ↦ a (numLE x): `Blocks.ext`
    (Blocks/Ext.lean) at the point read backwards.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpNum
import Blocks.EqN

set_option autoImplicit false

namespace Cb
open Finset Cb.LdLkp Cb.Lkp

theorem ldLkpNum_snoc : Spec.ldLkpNum_snoc := by
  intro k x b
  unfold numLE
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]

theorem numLE_ofBits : ∀ (k : ℕ) (x : Fin k → Bool), numLE x = Nat.ofBits x := by
  intro k
  induction k with
  | zero => intro x; simp [numLE, Nat.ofBits]
  | succ k ih =>
      intro x
      rw [Nat.ofBits_succ, ← ih]
      unfold numLE
      rw [Fin.sum_univ_succ, Finset.mul_sum, Nat.add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Function.comp, Fin.val_succ, pow_succ]
        split_ifs <;> ring
      · cases x 0 <;> simp

theorem ldLkpNum_rev : Spec.ldLkpNum_rev := by
  intro k x
  unfold Alg.num
  simp only [Fin.rev_rev]
  exact numLE_ofBits k x

theorem ldLkpNum_lt : Spec.ldLkpNum_lt := fun k x => by
  rw [ldLkpNum_rev]
  exact Alg.num_lt _

theorem ldLkpNum_inj : Spec.ldLkpNum_inj := by
  intro k x y h
  rw [ldLkpNum_rev, ldLkpNum_rev] at h
  have h' := congrArg (Alg.bits k) h
  rw [Alg.bits_num, Alg.bits_num] at h'
  funext i
  have := congrFun h' i.rev
  simpa only [Fin.rev_rev] using this

/-- a corner read backwards -/
def revCube (k : ℕ) : (Fin k → Bool) ≃ (Fin k → Bool) := Fin.revPerm.arrowCongr (Equiv.refl Bool)

theorem num_revCube (k : ℕ) (x : Fin k → Bool) : Alg.num (revCube k x) = numLE x := by
  rw [ldLkpNum_rev]
  rfl

theorem numLE_revCube (k : ℕ) (x : Fin k → Bool) : numLE (revCube k x) = Alg.num x := by
  rw [ldLkpNum_rev]
  congr 1
  funext i
  show x (Fin.rev (Fin.rev i)) = x i
  rw [Fin.rev_rev]

theorem ldLkpNum_prod : Spec.ldLkpNum_prod := by
  intro N _ k f
  calc
    ∏ x : Fin k → Bool, f (numLE x) = ∏ x : Fin k → Bool, f (numLE (revCube k x)) :=
      ((revCube k).prod_comp fun x => f (numLE x)).symm
    _ = ∏ x : Fin k → Bool, f ((Alg.cubeEquiv k x : Fin (2 ^ k)) : ℕ) :=
      Finset.prod_congr rfl fun x _ => by rw [numLE_revCube]; rfl
    _ = ∏ c : Fin (2 ^ k), f c := (Alg.cubeEquiv k).prod_comp fun c : Fin (2 ^ k) => f c
    _ = ∏ c ∈ range (2 ^ k), f c := Fin.prod_univ_eq_prod_range f (2 ^ k)

theorem ldLkpNum_sum : Spec.ldLkpNum_sum := by
  intro N _ k f
  rw [← Alg.sum_num f, ← (revCube k).sum_comp fun x => f (numLE x)]
  exact Finset.sum_congr rfl fun x _ => by rw [numLE_revCube]

section Levels
variable {E : Type} [CommMonoid E]

theorem lvl_ge (s n : ℕ) (A : ℕ → E) {l : ℕ} (h : n ≤ l) (X : ℕ) : Blocks.lvl s n A l X = A X := by
  simp [Blocks.lvl, Nat.sub_eq_zero_of_le h]

theorem lvl_cutOne (g n : ℕ) (A : ℕ → E) {l : ℕ} (h : l ≤ n) {X : ℕ} (hX : X < 2 ^ (g + l)) :
    Blocks.lvl g n (cutOne (2 ^ (n + g)) A) l X = Blocks.lvl g n A l X := by
  unfold Blocks.lvl
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj' : j + 1 ≤ 2 ^ (n - l) := Finset.mem_range.1 hj
  have h1 : (j + 1) * 2 ^ (l + g) ≤ 2 ^ (n - l) * 2 ^ (l + g) := Nat.mul_le_mul_right _ hj'
  rw [← pow_add, show n - l + (l + g) = n + g by omega, Nat.succ_mul] at h1
  rw [Nat.add_comm g l] at hX
  unfold cutOne
  rw [if_pos (by omega)]

end Levels

theorem ldLkpNum_lvl : Spec.ldLkpNum_lvl := fun _ _ g n A _ x h =>
  lvl_cutOne g n A h (ldLkpNum_lt _ x)

theorem ldLkpNum_step : Spec.ldLkpNum_step := by
  intro E _ g n A l x
  unfold cubeLvl
  rw [ldLkpNum_snoc, ldLkpNum_snoc]
  simp only [Bool.false_eq_true, if_false, if_true, Nat.add_zero]
  by_cases h : l < n
  · rw [Blocks.lvl_step g n _ h, Nat.add_comm l g]
  · have h1 : n ≤ l := Nat.le_of_not_lt h
    rw [lvl_ge g n _ h1, lvl_ge g n _ (Nat.le_succ_of_le h1), lvl_ge g n _ (Nat.le_succ_of_le h1)]
    have h2 : 2 ^ (n + g) ≤ 2 ^ (g + l) := Nat.pow_le_pow_right (by decide) (by omega)
    have h3 : cutOne (2 ^ (n + g)) A (numLE x + 2 ^ (g + l)) = 1 := by
      unfold cutOne
      rw [if_neg (by omega)]
    rw [h3, mul_one]

theorem ldLkpNum_top : Spec.ldLkpNum_top := fun E _ g n A x => by
  rw [ldLkpNum_lvl E g n A n x (Nat.le_refl n), Blocks.lvl_top]

theorem ldLkpNum_root : Spec.ldLkpNum_root := fun E _ g n A θ => by
  rw [ldLkpNum_lvl E g n A 0 θ (Nat.zero_le n), Blocks.lvl_zero]

theorem ldLkpNum_rootK : Spec.ldLkpNum_rootK := by
  intro E _ v key al θ
  have h0 : numLE θ = 0 := by
    have := ldLkpNum_lt _ θ
    simpa using this
  rw [ldLkpNum_root, h0]
  simp [facK, keyProd]

theorem ldLkpNum_rootT : Spec.ldLkpNum_rootT := by
  intro E _ w d t M al θ
  have hX : numLE θ < 2 ^ w := ldLkpNum_lt _ θ
  rw [ldLkpNum_root]
  unfold tabProd facT
  refine Finset.prod_congr rfl fun j _ => ?_
  have h1 : (j * 2 ^ w + numLE θ) / 2 ^ w = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos w),
      Nat.div_eq_of_lt hX, Nat.zero_add]
  have h2 : (j * 2 ^ w + numLE θ) % 2 ^ w = numLE θ := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hX]
  rw [h1, h2]

theorem ldLkpNum_topK : Spec.ldLkpNum_topK := fun E _ v key al x => by
  rw [ldLkpNum_top]
  rfl

theorem ldLkpNum_topT : Spec.ldLkpNum_topT := fun E _ w d t M al x => by
  rw [ldLkpNum_top]
  rfl

theorem ldLkpNum_ext : Spec.ldLkpNum_ext := by
  intro E _ k a z
  have h1 : Blocks.ext k a (Blocks.nat fun i : Fin k => z i.rev) =
      Alg.mle (fun b : Fin k → Bool => a (Alg.num b)) fun i : Fin k => z i.rev := by
    unfold Blocks.ext
    simp only [Blocks.eqN_nat]
    exact Alg.mleN_eq_mle a _
  rw [h1, ← Alg.mle_equiv Fin.revPerm (fun x : Fin k → Bool => a (numLE x)) z]
  congr 1
  funext b
  rw [ldLkpNum_rev]
  congr 2
  funext i
  simp [Fin.revPerm]

end Cb
