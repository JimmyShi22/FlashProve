-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/Idle.lean: planes of bits that are not live: a place that holds the constant 0 and
stands for no entry.

It imports the library and Cb/Pv/KeyLookup/Letters.lean alone (no file of the port).

Each row of the table has a count, written in bits; bit j of all 2^d counts is plane j. There are
2^mu places for planes; the first pl of them are live (`Pub.pl`, Letters.lean). The table's
levels, the closing and the test of the bits run over all mu + d variables, so they also meet the
corners of planes that are not live ("dead" below). This file fixes how a corner is read.
  `ext0 μ`        the entries μ : J → E read at a place of type `Option J`: μ j at `some j`, and the
                  constant 0 at `none`.
  `A.place u j`   the place of the bit (row u, plane j): `some (bAt u j)` if j < pl, else `none`.
  `A.cell c`      the same at a corner c of the cube; the plane's variables are the low ones.
So a block that reads the planes in this way needs no entry for a dead plane and reads none.
Whether anything is sent for a dead plane depends on the values of J and msg, which are the
caller's; it is not said here. A.J is any finite type and bAt is total.

The library's condition on places (`PlacesIn`, Cb/Ld/LdLkpAsm2Pull.lean) asks its clause bAt of all
u and j. Here the clause is `A.CellsIn G`: G holds of bAt u j for u < 2^d and j < pl alone.

Shown, for every state and all entries, with no condition unless one is written:
  `sum_ext0`, `row_pull0`, `rows_pull0`   a linear form on `Option J` at `ext0 μ` is its pull-back
                  along `some` at μ; no condition on supports, since the entry at `none` is 0.
  `bit_place`, `bitN_cell`   `A.bit` and `A.bitN` of Letters.lean are this reading.
  `bit_dead`, `plane_dead`   at pl ≤ j the bit is 0 and the plane's root is 1.
  `cell_none_iff`, `cell_live`   a corner has no cell exactly if its plane is dead; else its cell is
                  `some (bAt row plane)`.
  `cell_in`       under `A.CellsIn G`: a corner's cell, if it has one, lies in G.
  `tabU_zero`, `tabU_top`   at n < 2^mu, level 0 of the table's tree holds the root of plane n;
                  level d holds the leaves.
  `bts_iff`       "all are bits" (`A.Bts`, Letters.lean), corner by corner.
  `bts_live`      if pl ≤ 2^mu: the same on the live cells alone.
  `bitOn_ext0`    the library's `LkInst.bitOn n` is this reading at n + 1 live planes.
Not shown: anything on a block, a round or an error; anything on an honest prover.

-/
import Cb.Pv.KeyLookup.Letters
import Cb.Ld.LdLkpInst2
import Cb.Ld.LdLkpSupp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Cb Cb.LdLkp Cb.Lkp Finset

/-! ### entries read at a place that may stand for none -/
section Read
variable {E J : Type}

/-- The entries, read at a place that may stand for no entry: there the constant 0. -/
def ext0 [Zero E] (μ : J → E) : Option J → E
  | some j => μ j
  | none => 0

@[simp] theorem ext0_some [Zero E] (μ : J → E) (j : J) : ext0 μ (some j) = μ j := rfl
@[simp] theorem ext0_none [Zero E] (μ : J → E) : ext0 μ (none : Option J) = 0 := rfl

variable [Field E] [Fintype J]

theorem sum_ext0 (c : Option J → E) (μ : J → E) :
    ∑ o, c o * ext0 μ o = ∑ j, c (some j) * μ j := by
  rw [Fintype.sum_option, ext0_none, mul_zero, zero_add]
  rfl

/-- A row on `Option J`, brought to J: no condition on supports. -/
theorem row_pull0 (r : Row E (Option J)) (μ : J → E) :
    (r.pull some).Holds μ ↔ r.Holds (ext0 μ) := by
  unfold Row.Holds
  rw [sum_ext0]
  exact Iff.rfl

theorem rows_pull0 (rs : List (Row E (Option J))) (μ : J → E) :
    RowsHold (rs.map (Row.pull some)) μ ↔ RowsHold rs (ext0 μ) := by
  constructor
  · intro h r hr
    exact (row_pull0 r μ).1 (h _ (List.mem_map_of_mem hr))
  · intro h r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    exact (row_pull0 r' μ).2 (h r' hr')

end Read

/-! ### the places of the bits -/
namespace Dat
variable {E : Type} [Field E] [Fintype E] (A : Dat E)

/-- The place of the bit (row u, plane j): none at a dead plane. -/
def place (u j : ℕ) : Option A.J := if j < A.pl then some (A.bAt u j) else none

/-- The place at the number (plane | row) = plane + 2^mu row, and at a corner of the cube. -/
def placeN (n : ℕ) : Option A.J := A.place (n / 2 ^ A.mu) (n % 2 ^ A.mu)
def cell (c : Fin (A.mu + A.d) → Bool) : Option A.J := A.placeN (numLE c)

/-- The clause that stands for `PlacesIn.bAt`: on the live cells alone. -/
def CellsIn (G : A.J → Prop) : Prop := ∀ u < 2 ^ A.d, ∀ j < A.pl, G (A.bAt u j)

theorem bit_place (μ : A.J → E) (u j : ℕ) : A.bit μ u j = ext0 μ (A.place u j) := by
  unfold bit place
  split <;> rfl

theorem bitN_place (μ : A.J → E) (n : ℕ) : A.bitN μ n = ext0 μ (A.placeN n) := A.bit_place μ _ _

theorem bitN_cell (μ : A.J → E) (c : Fin (A.mu + A.d) → Bool) :
    A.bitN μ (numLE c) = ext0 μ (A.cell c) := A.bit_place μ _ _

theorem bit_dead (μ : A.J → E) (u : ℕ) {j : ℕ} (h : A.pl ≤ j) : A.bit μ u j = 0 :=
  if_neg (Nat.not_lt.mpr h)

theorem bit_live (μ : A.J → E) (u : ℕ) {j : ℕ} (h : j < A.pl) : A.bit μ u j = μ (A.bAt u j) :=
  if_pos h

/-- The root of a dead plane is 1, for all entries: each of its leaves is 1. -/
theorem plane_dead (st : A.St) (μ : A.J → E) (al : E) {j : ℕ} (h : A.pl ≤ j) :
    A.plane st μ al j = 1 := by
  unfold plane tabProd
  exact Finset.prod_eq_one fun u _ => by rw [A.bit_dead μ u h, zero_mul, add_zero]

theorem cell_none_iff (c : Fin (A.mu + A.d) → Bool) :
    A.cell c = none ↔ A.pl ≤ numLE c % 2 ^ A.mu := by
  unfold cell placeN place
  constructor
  · intro h
    by_contra hc
    rw [if_pos (Nat.lt_of_not_le hc)] at h
    exact Option.some_ne_none _ h
  · intro h
    exact if_neg (Nat.not_lt.mpr h)

theorem cell_live (c : Fin (A.mu + A.d) → Bool) (h : numLE c % 2 ^ A.mu < A.pl) :
    A.cell c = some (A.bAt (numLE c / 2 ^ A.mu) (numLE c % 2 ^ A.mu)) := if_pos h

theorem row_lt (c : Fin (A.mu + A.d) → Bool) : numLE c / 2 ^ A.mu < 2 ^ A.d := by
  have hb : numLE c < 2 ^ (A.mu + A.d) := ldLkpNum_lt _ c
  rw [pow_add] at hb
  exact Nat.div_lt_of_lt_mul hb

/-- Whatever a corner's cell names lies in G. -/
theorem cell_in {G : A.J → Prop} (hG : A.CellsIn G) (c : Fin (A.mu + A.d) → Bool) (j : A.J)
    (hc : A.cell c = some j) : G j := by
  by_cases h : numLE c % 2 ^ A.mu < A.pl
  · rw [A.cell_live c h] at hc
    exact Option.some.inj hc ▸ hG _ (A.row_lt c) _ h
  · rw [(A.cell_none_iff c).2 (Nat.le_of_not_lt h)] at hc
    exact absurd hc.symm (Option.some_ne_none j)

/-- Level 0 of the table's tree holds the planes' roots. -/
theorem tabU_zero (st : A.St) (μ : A.J → E) (al : E) {n : ℕ} (h : n < 2 ^ A.mu) :
    A.tabU st μ al 0 n = A.plane st μ al n := by
  unfold tabU plane tabProd leaf
  rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h, Nat.sub_zero]
  refine Finset.prod_congr rfl fun z _ => ?_
  rw [pow_zero, Nat.one_mul, Nat.zero_add]

/-- Level d holds the leaves. -/
theorem tabU_top (st : A.St) (μ : A.J → E) (al : E) (n : ℕ) :
    A.tabU st μ al A.d n = 1 + A.bitN μ n * (al - 1 - A.tab st (n / 2 ^ A.mu)) := by
  unfold tabU leaf bitN
  rw [Nat.sub_self, pow_zero, Finset.prod_range_one, Nat.mul_zero, Nat.add_zero]

/-- "All are bits", corner by corner. -/
theorem bts_iff (μ : A.J → E) :
    A.Bts μ ↔ ∀ c : Fin (A.mu + A.d) → Bool, ext0 μ (A.cell c) * (ext0 μ (A.cell c) - 1) = 0 := by
  constructor
  · intro h c
    rw [← A.bitN_cell μ c]
    exact h _ (A.row_lt c) _ (Nat.mod_lt _ (Nat.two_pow_pos A.mu))
  · intro h u hu j hj
    have hlt : u * 2 ^ A.mu + j < 2 ^ (A.mu + A.d) := by
      have h1 : (u + 1) * 2 ^ A.mu ≤ 2 ^ A.d * 2 ^ A.mu := Nat.mul_le_mul_right _ hu
      rw [← pow_add, Nat.add_comm A.d A.mu, Nat.succ_mul] at h1
      omega
    obtain ⟨b, hb⟩ := numLE_surj hlt
    have hq : numLE b / 2 ^ A.mu = u := by
      rw [hb, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos A.mu),
        Nat.div_eq_of_lt hj, Nat.zero_add]
    have hr : numLE b % 2 ^ A.mu = j := by
      rw [hb, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    have h2 := h b
    rw [← A.bitN_cell μ b] at h2
    unfold bitN at h2
    rw [hq, hr] at h2
    exact h2

/-- … and on the live cells alone. -/
theorem bts_live (hr : A.pl ≤ 2 ^ A.mu) (μ : A.J → E) :
    A.Bts μ ↔ ∀ u < 2 ^ A.d, ∀ j < A.pl, μ (A.bAt u j) * (μ (A.bAt u j) - 1) = 0 := by
  constructor
  · intro h u hu j hj
    have h1 := h u hu j (Nat.lt_of_lt_of_le hj hr)
    rw [A.bit_live μ u hj] at h1
    exact h1
  · intro h u hu j _
    by_cases hj : j < A.pl
    · rw [A.bit_live μ u hj]
      exact h u hu j hj
    · rw [A.bit_dead μ u (Nat.le_of_not_lt hj), zero_mul]

end Dat

/-- The library's bits with the public factor (Cb/Ld/LdLkpInst2.lean) are this reading, at n + 1
live planes. -/
theorem bitOn_ext0 {E : Type} [Field E] [Fintype E] (I : LkInst E) (n : ℕ) (m : I.J → E) (u j : ℕ) :
    I.bitOn n m u j = ext0 m (if j < n + 1 then some (I.bAt u j) else none) := by
  unfold LkInst.bitOn
  split <;> rfl

end Lk6
