-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/NormBridge/TotExt.lean: A JOINT between two ways of writing a multilinear extension:
  the masked sumcheck's law (OnBytes/Desc/First/P1/SumMle.lean): a table is a function on LISTS OF
    BITS, the first bit for the first variable that is summed; "tot" sums it under two-point
    weights,
    "mle" extends it at a list of challenges;
  the library (Blocks/Ext.lean): a vector is a function on NUMBERS, a point a function on numbers,
    coordinate 0 belongs to the TOP bit of an index; "ext".
Where the rounds run in the order of the coordinates, the two agree with no permutation: the first
bit is the top bit. Algebra over a field; no text of a verifier. Definitions, statements, proofs.

  numFrom a b: the number that the bits b spell behind the number a, top bit first.
  wts zs: the two-point weights (1 - z, z) of a list of coordinates.
  coords pt off n: the n coordinates of a point from number off on, as a list.
  tot_coords: THE JOINT, from any offset and behind any number a.
  tot_ext: at offset 0 and a = 0: tot (wts (coords pt 0 n)) (G after numFrom 0) = ext n G pt.
  mle_eq_tot: mle n A rs = tot (wts rs) A for n challenges.
  mle_ext: mle n (G after numFrom 0) (coords pt 0 n) = ext n G pt.
  coords_ofList: the coordinates of a list's point are the list.

LIBRARY LEMMAS TAKEN: Blocks/EqN.lean eqN_append; Blocks/Basic.lean eqN, ofList.
NOT CLAIMED: anything for rounds that run in another order than the coordinates.
-/
import OnBytes.Desc.First.P1.SumMle
import Blocks.Ext

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D6.Bridge
open Finset
open Blocks (ext eqN)
open OnBytes.Desc.First.P1 (tot mle)

variable {K : Type} [Field K]

/-- The number that the bits b spell behind a, top bit first. -/
def numFrom (a : ℕ) (b : List Bool) : ℕ := b.foldl (fun x β => 2 * x + β.toNat) a

theorem numFrom_cons (a : ℕ) (β : Bool) (b : List Bool) :
    numFrom a (β :: b) = numFrom (2 * a + β.toNat) b := rfl

/-- The two-point weights of a list of coordinates. -/
def wts (zs : List K) : List (K × K) := zs.map fun z => (1 - z, z)

/-- The n coordinates of a point from number off on. -/
def coords (pt : ℕ → K) : ℕ → ℕ → List K
  | _, 0 => []
  | off, n + 1 => pt off :: coords pt (off + 1) n

omit [Field K] in
theorem coords_length (pt : ℕ → K) : ∀ (n off : ℕ), (coords pt off n).length = n
  | 0, _ => rfl
  | n + 1, off => by
    show (coords pt (off + 1) n).length + 1 = n + 1
    rw [coords_length pt n]

theorem sum_range_two_pow_succ {M : Type} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ Y ∈ range (2 ^ (n + 1)), f Y =
      ∑ X ∈ range (2 ^ n), f X + ∑ X ∈ range (2 ^ n), f (2 ^ n + X) := by
  rw [pow_succ, mul_two, sum_range_add]

theorem eqN_one_zero (off : ℕ) (a : ℕ → K) : eqN 1 off a 0 = 1 - a off := by
  simp [Blocks.eqN]

theorem eqN_one_one (off : ℕ) (a : ℕ → K) : eqN 1 off a 1 = a off := by
  have t1 : (1 : ℕ).testBit 0 = true := by decide
  simp [Blocks.eqN, t1]

theorem eqN_succ_lo (n off : ℕ) (a : ℕ → K) {X : ℕ} (hX : X < 2 ^ n) :
    eqN (n + 1) off a X = (1 - a off) * eqN n (off + 1) a X := by
  have h := Blocks.eqN_append 1 n off a 0 hX
  rw [Nat.mul_zero, Nat.zero_add, Nat.add_comm 1 n, eqN_one_zero] at h
  exact h

theorem eqN_succ_hi (n off : ℕ) (a : ℕ → K) {X : ℕ} (hX : X < 2 ^ n) :
    eqN (n + 1) off a (2 ^ n + X) = a off * eqN n (off + 1) a X := by
  have h := Blocks.eqN_append 1 n off a 1 hX
  rw [Nat.mul_one, Nat.add_comm 1 n, eqN_one_one] at h
  exact h

/-- **THE JOINT.** -/
theorem tot_coords (pt : ℕ → K) : ∀ (n off a : ℕ) (G : ℕ → K),
    tot (wts (coords pt off n)) (fun b => G (numFrom a b)) =
      ∑ X ∈ range (2 ^ n), eqN n off pt X * G (a * 2 ^ n + X)
  | 0, off, a, G => by
    show G a = _
    simp [Blocks.eqN]
  | n + 1, off, a, G => by
    have ih0 := tot_coords pt n (off + 1) (2 * a + 0) G
    have ih1 := tot_coords pt n (off + 1) (2 * a + 1) G
    have hlo : ∀ X ∈ range (2 ^ n), (1 - pt off) * (eqN n (off + 1) pt X *
        G ((2 * a + 0) * 2 ^ n + X)) = eqN (n + 1) off pt X * G (a * 2 ^ (n + 1) + X) := by
      intro X hX
      rw [eqN_succ_lo n off pt (mem_range.mp hX),
        show a * 2 ^ (n + 1) + X = (2 * a + 0) * 2 ^ n + X by ring]
      ring
    have hhi : ∀ X ∈ range (2 ^ n), pt off * (eqN n (off + 1) pt X *
        G ((2 * a + 1) * 2 ^ n + X)) =
          eqN (n + 1) off pt (2 ^ n + X) * G (a * 2 ^ (n + 1) + (2 ^ n + X)) := by
      intro X hX
      rw [eqN_succ_hi n off pt (mem_range.mp hX),
        show a * 2 ^ (n + 1) + (2 ^ n + X) = (2 * a + 1) * 2 ^ n + X by ring]
      ring
    calc tot (wts (coords pt off (n + 1))) (fun b => G (numFrom a b))
        = (1 - pt off) * tot (wts (coords pt (off + 1) n)) (fun b => G (numFrom (2 * a + 0) b)) +
            pt off * tot (wts (coords pt (off + 1) n)) (fun b => G (numFrom (2 * a + 1) b)) := rfl
      _ = (1 - pt off) * ∑ X ∈ range (2 ^ n), eqN n (off + 1) pt X * G ((2 * a + 0) * 2 ^ n + X) +
            pt off * ∑ X ∈ range (2 ^ n), eqN n (off + 1) pt X * G ((2 * a + 1) * 2 ^ n + X) := by
          rw [ih0, ih1]
      _ = ∑ X ∈ range (2 ^ n), eqN (n + 1) off pt X * G (a * 2 ^ (n + 1) + X) +
            ∑ X ∈ range (2 ^ n),
              eqN (n + 1) off pt (2 ^ n + X) * G (a * 2 ^ (n + 1) + (2 ^ n + X)) := by
          rw [mul_sum, mul_sum, sum_congr rfl hlo, sum_congr rfl hhi]
      _ = _ := (sum_range_two_pow_succ n
            fun Y => eqN (n + 1) off pt Y * G (a * 2 ^ (n + 1) + Y)).symm

/-- At offset 0, behind 0: the library's extension. -/
theorem tot_ext (pt : ℕ → K) (n : ℕ) (G : ℕ → K) :
    tot (wts (coords pt 0 n)) (fun b => G (numFrom 0 b)) = ext n G pt := by
  rw [tot_coords pt n 0 0 G]
  unfold Blocks.ext
  exact sum_congr rfl fun X _ => by rw [Nat.zero_mul, Nat.zero_add]

/-- An extension at n challenges is the sum under their two-point weights. -/
theorem mle_eq_tot : ∀ (n : ℕ) (A : List Bool → K) (rs : List K), rs.length = n →
    mle n A rs = tot (wts rs) A
  | 0, _, [], _ => rfl
  | 0, _, _ :: _, h => by simp at h
  | _ + 1, _, [], h => by simp at h
  | n + 1, A, r :: rs, h => by
    have hl : rs.length = n := by simpa using h
    show (1 - r) * mle n (fun b => A (false :: b)) rs + r * mle n (fun b => A (true :: b)) rs =
      (1 - r) * tot (wts rs) (fun b => A (false :: b)) + r * tot (wts rs) (fun b => A (true :: b))
    rw [mle_eq_tot n _ rs hl, mle_eq_tot n _ rs hl]

/-- The sumcheck's extension of a vector's table at a point's coordinates is the library's. -/
theorem mle_ext (pt : ℕ → K) (n : ℕ) (G : ℕ → K) :
    mle n (fun b => G (numFrom 0 b)) (coords pt 0 n) = ext n G pt := by
  rw [mle_eq_tot n _ _ (coords_length pt n 0), tot_ext]

/-- The coordinates of a list's point, from any place on. -/
theorem coords_drop (l : List K) : ∀ (n off : ℕ), off + n = l.length →
    coords (Blocks.ofList l) off n = l.drop off
  | 0, off, h => by
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | n + 1, off, h => by
    have hlt : off < l.length := by omega
    show Blocks.ofList l off :: coords (Blocks.ofList l) (off + 1) n = l.drop off
    rw [coords_drop l n (off + 1) (by omega), List.drop_eq_getElem_cons hlt]
    congr 1
    unfold Blocks.ofList
    rw [List.getD_eq_getElem _ _ hlt]

/-- The coordinates of a list's point are the list. -/
theorem coords_ofList (l : List K) : coords (Blocks.ofList l) 0 l.length = l := by
  rw [coords_drop l l.length 0 (by omega), List.drop_zero]

end D6.Bridge

#print axioms D6.Bridge.tot_ext
#print axioms D6.Bridge.mle_ext
#print axioms D6.Bridge.coords_ofList
