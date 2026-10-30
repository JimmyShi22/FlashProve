-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/DrawOf.lean: the challenge sampler of a set of challenges that is built from a field E,
positions, products and vectors, found by instance. (Sampler: `BS`, Iop/Draw.lean; words of this
library: lean/GLOSSARY.md.)

A challenge of the interactive protocols is a tuple of elements of E and of positions (numbers below
the length of a code), indexed by finite types. Given a sampler bE for E, the class `DrawOf bE sl C`
builds the sampler of C coordinate by coordinate, as Mathlib's `FinEnum` builds a numbering:
    Unit                 no block
    E                    bE
    Fin n                `BS.pos`: the binary value of one block modulo n, as long as 1 < n and
                         ⌈log₂ n⌉ + sl < lam; for n = 2^L these are the low L bits of the block.
    Bool                 a number below 2: the lowest bit of one block (if 1 + sl < lam). One block
                         for a bit: tables of bits do not belong here (`Iop.BS.bits`;
                         Blocks/ChalK.lean has the coefficients of a range proof)
    C × D                the blocks of C, then those of D
    Fin n → C            coordinate i reads the blocks i · b, .., i · b + b − 1 (`Iop.BS.vec`): by
                         definition, through no enumeration
    ι → C, ∀ i, C i      for any other enumerated index type ι (∀ i, C i: for Fin n too): the
                         coordinates in the order of the enumeration, each with its own blocks
If E itself is Unit, Fin n, Bool or a product, the sampler bE is taken (the instance `self` has a
higher priority than theirs). Of the instances for function types `pi` has a lower priority than
`self`, `fn` the same, `vec` a higher one.
The order of the coordinates is explicit, except for the enumerations of index types, which are data
of the caller (Mathlib's `FinEnum`).
The condition (`DrawBase`): 0 < lam, and bE of b blocks satisfies `BS.Good` with (1 + 2^-sl)^b.
`BS.pos_good`, `BS.fnE_good`, `BS.piE_good`: the same bound for a position and, if the coordinates'
samplers have it, for the samplers on enumerated index types. sl is the slack of a position: a
number below n > 1 is computed from at least ⌈log₂ n⌉ + sl bits, so that its bias is at most 2^-sl;
if n divides 2^lam the bias of a position is 0 (`Iop.BS.modN_exact`), and `BS.pos_good` does
not say so.
Limits: this file does not say which types occur in which round, or that the sampler that an
instance finds satisfies `BS.Good` with (1 + 2^-sl)^(number of its blocks).
-/
import Iop.DrawProofs
import Mathlib.Data.FinEnum
noncomputable section -- Lean tags what it cannot compile

namespace Iop
open Prob
open scoped ENNReal

namespace BS
variable {lam : ℕ}

/-- the number of blocks for a number below n: none if n = 1 -/
def posK (lam sl n : ℕ) : ℕ := if n = 1 then 0 else (Nat.clog 2 n + sl) / lam + 1

/-- a number below n -/
def pos (lam sl n : ℕ) (h : 0 < n) : BS lam (Fin n) := modN lam n (posK lam sl n) h

/-- a vector on an enumerated index type: the coordinates in the order of the enumeration -/
def fnE {ι C : Type} [FinEnum ι] (s : BS lam C) : BS lam (ι → C) :=
  (s.vec (FinEnum.card ι)).map (Equiv.arrowCongr (FinEnum.equiv (α := ι)) (Equiv.refl C)).symm

/-- coordinates of several kinds on an enumerated index type -/
def piE {ι : Type} [FinEnum ι] {C : ι → Type} (s : ∀ i, BS lam (C i)) : BS lam (∀ i, C i) :=
  (BS.pi fun k : Fin (FinEnum.card ι) => s ((FinEnum.equiv (α := ι)).symm k)).map
    (Equiv.piCongrLeft' C (FinEnum.equiv (α := ι))).symm

end BS

/-- The challenge sampler of C, from the sampler bE of E and the slack sl of positions. -/
class DrawOf {lam : ℕ} {E : Type} (bE : BS lam E) (sl : ℕ) (C : Type) where
  bs : BS lam C

namespace DrawOf
variable {lam : ℕ} {E : Type} (bE : BS lam E) (sl : ℕ)

instance unit : DrawOf bE sl Unit := ⟨BS.unit⟩
instance (priority := high) self : DrawOf bE sl E := ⟨bE⟩
instance fin (n : ℕ) [h : Nonempty (Fin n)] : DrawOf bE sl (Fin n) :=
  ⟨BS.pos lam sl n (Fin.pos_iff_nonempty.mpr h)⟩
instance bool : DrawOf bE sl Bool := ⟨(BS.pos lam sl 2 Nat.two_pos).map finTwoEquiv⟩
instance prod {C D : Type} [a : DrawOf bE sl C] [b : DrawOf bE sl D] : DrawOf bE sl (C × D) :=
  ⟨a.bs.prod b.bs⟩
instance pi {ι : Type} [FinEnum ι] {C : ι → Type} [a : ∀ i, DrawOf bE sl (C i)] :
    DrawOf bE sl (∀ i, C i) :=
  ⟨BS.piE fun i => (a i).bs⟩
instance (priority := high) fn {ι C : Type} [FinEnum ι] [a : DrawOf bE sl C] :
    DrawOf bE sl (ι → C) := ⟨BS.fnE a.bs⟩
instance (priority := high + 1) vec (n : ℕ) {C : Type} [a : DrawOf bE sl C] :
    DrawOf bE sl (Fin n → C) := ⟨a.bs.vec n⟩

end DrawOf

/-- the bias of one block, as a factor: 1 + 2^-sl (`DrawBase` takes its power `kapSl sl ^ b` as the
κ of `BS.Good`) -/
def kapSl (sl : ℕ) : ℝ≥0∞ := 1 + (2 ^ sl : ℝ≥0∞)⁻¹

theorem one_le_kapSl (sl : ℕ) : 1 ≤ kapSl sl := le_self_add

/-- a condition on the sampler of E. (`Iop.BS.Good` counts the elements of E by `Nat.card`:
for an infinite E it would say little; the fields of the library are finite.) -/
class DrawBase {lam : ℕ} {E : Type} (bE : BS lam E) (sl : ℕ) : Prop where
  lam_pos : 0 < lam
  good : bE.Good (kapSl sl ^ bE.b)

namespace BS
variable {lam : ℕ}

theorem pos_good (hlam : 0 < lam) (sl n : ℕ) (h : 0 < n) :
    (pos lam sl n h).Good (kapSl sl ^ (pos lam sl n h).b) := by
  show (modN lam n (posK lam sl n) h).Good (kapSl sl ^ posK lam sl n)
  unfold posK
  split_ifs with h1
  · rw [pow_zero]
    exact modN_exact lam n 0 h (by rw [h1]; exact one_dvd _)
  · have he : n * 2 ^ sl ≤ 2 ^ (lam * ((Nat.clog 2 n + sl) / lam + 1)) :=
      calc
        n * 2 ^ sl ≤ 2 ^ Nat.clog 2 n * 2 ^ sl :=
          Nat.mul_le_mul_right _ (Nat.le_pow_clog (by norm_num) n)
        _ = 2 ^ (Nat.clog 2 n + sl) := (pow_add _ _ _).symm
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (le_of_lt (Nat.lt_mul_div_succ _ hlam))
    refine (modN_good lam n _ h sl he).mono ?_
    calc kapSl sl = kapSl sl ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (one_le_kapSl sl) (Nat.le_add_left _ _)

theorem fnE_good {ι C : Type} [FinEnum ι] {s : BS lam C} {κ : ℝ≥0∞} (h : s.Good (κ ^ s.b)) :
    (fnE (ι := ι) s).Good (κ ^ (fnE (ι := ι) s).b) := by
  refine map_good _ ?_
  have := vec_good (FinEnum.card ι) h
  rwa [← pow_mul, Nat.mul_comm] at this

theorem piE_good {ι : Type} [FinEnum ι] {C : ι → Type} {s : ∀ i, BS lam (C i)}
    {κ : ℝ≥0∞} (h : ∀ i, (s i).Good (κ ^ (s i).b)) :
    (piE s).Good (κ ^ (piE s).b) := by
  refine map_good _ ?_
  have := pi_good (s := fun k : Fin (FinEnum.card ι) => s ((FinEnum.equiv (α := ι)).symm k))
    (fun k => h _)
  rwa [Finset.prod_pow_eq_pow_sum] at this

end BS

end Iop
