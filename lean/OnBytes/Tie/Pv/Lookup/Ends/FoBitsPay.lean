-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoBitsPay.lean: the smallness test's three runs on the array BZ are the
sums of which the lookup's three claims on the planes speak.

The lookup's claims on the planes are written, as values, with planesK and countK over the columns'
sums colsK and pinColK of a matrix of cells (OnBytes/Tie/Pv/Lookup/Forest/FoPlane.lean,
OnBytes/Tie/Pv/Lookup/Forest/FoPlaneRows.lean, OnBytes/Tie/Pv/Lookup/Forest/FoPin.lean). For the
smallness test's own lookup that matrix is a virtual one, with one row for each plane (lm = 5):
row j, column c * 2^kT + t holds bit j of the count of row t of call c. The byte-level routine
writes runs on three virtual rows of BZ instead, where bit number X = (t * 2^cK + c) * 32 + j stands
in row X / 2^(kT + cK) at index X % 2^(kT + cK).

 - CellsBZ h ν B: the cells ν of the virtual matrix are BZ's entries B, by these two maps.
 - onBZ_five: then the flat function's places of the bits at lm = 5 read BZ's entries (OnBZ), if
   every number of cK bits is the number of a call.
 - pay_bits: planesK h 5 z (colsK h 5 z ν) is the run with the weights eqTabK (exL z 5 (5 + kT +
   cK)) on a virtual row of BZ that combines BZ's 32 rows under eqTabK (z.take 5).
 - pay_count: countK h 5 (pinColK 5 ν) is the constant -(2^v - padding) plus the run with the
   weights 2^(i mod 32) on a virtual row that adds BZ's 32 rows up.
The runs are written with runSum, as in the value of a run (OnBytes/Model/TreesLaws.lean).

Premises: FoNums.ok h = true; 2^cK = NC; ν reads 0 at the place that is no cell; CellsBZ; VirtRow
for the virtual row. pay_bits also asks that the point has 5 + (kT + cK) coordinates, and pay_count
that 5 ≤ kT + cK.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that VirtRow or CellsBZ hold of a committed array.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoReadsBZ
import OnBytes.Tie.Pv.Lookup.Ends.FoVirtRow

set_option autoImplicit false

namespace Fo
open TwV Finset FoNums Cb.Fo.Pin OnBytes.Model

section
variable {K : Type} [CommRing K]

/-- The cells of the virtual matrix with one row for each plane are BZ's entries. -/
def CellsBZ (h : Sh) (ν : Pl → K) (B : ℕ → ℕ → K) : Prop :=
  ∀ j t c, j < 32 → t < 2 ^ h.kT → c < 2 ^ h.cK →
    ν (.cell j (c * 2 ^ h.kT + t)) =
      B (((t * 2 ^ h.cK + c) * 32 + j) / 2 ^ (h.kT + h.cK))
        (((t * 2 ^ h.cK + c) * 32 + j) % 2 ^ (h.kT + h.cK))

theorem cellRC_five (h : Sh) (t c j : ℕ) : cellRC h 5 (t, c, j) = (j, c * 2 ^ h.kT + t) := by
  have e1 : (cellRC h 5 (t, c, j)).1 = j := by
    show (t % 2 ^ (5 - FoNums.w)) * FoNums.planes + j = j
    have : (2 : ℕ) ^ (5 - FoNums.w) = 1 := rfl
    rw [this, Nat.mod_one, Nat.zero_mul, Nat.zero_add]
  have e2 : (cellRC h 5 (t, c, j)).2 = c * 2 ^ h.kT + t := by
    show c * 2 ^ (h.kT + FoNums.w - 5) + t / 2 ^ (5 - FoNums.w) = _
    have h1 : (2 : ℕ) ^ (5 - FoNums.w) = 1 := rfl
    have h2 : h.kT + FoNums.w - 5 = h.kT := Nat.add_sub_cancel h.kT 5
    rw [h1, h2, Nat.div_one]
  exact Prod.ext e1 e2

theorem onBZ_five (h : Sh) (jLK : ℕ) (θ : K) (ν : Pl → K) (B : ℕ → ℕ → K)
    (hfull : 2 ^ h.cK = h.NC) (hB : CellsBZ h ν B) :
    OnBZ (numsF h 5 jLK θ) ν (h.kT + h.cK) B := by
  intro u j hu hj
  have hc : u % 2 ^ h.cK < 2 ^ h.cK := Nat.mod_lt _ (by positivity)
  have ht : u / 2 ^ h.cK < 2 ^ h.kT := by
    rw [pow_add] at hu
    exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hu)
  have e : (numsF h 5 jLK θ).bAt u j =
      .cell j (u % 2 ^ h.cK * 2 ^ h.kT + u / 2 ^ h.cK) := by
    show (match cellOf h u j with
      | some x => Pl.cell (cellRC h 5 x).1 (cellRC h 5 x).2
      | none => Pl.zero) = _
    unfold cellOf
    rw [if_pos (by rw [← hfull]; exact hc)]
    show Pl.cell (cellRC h 5 (u / 2 ^ h.cK, u % 2 ^ h.cK, j)).1
      (cellRC h 5 (u / 2 ^ h.cK, u % 2 ^ h.cK, j)).2 = _
    rw [cellRC_five]
  rw [e, hB j _ _ hj ht hc, Nat.div_add_mod']

omit [CommRing K] in
theorem exL_drop (z : List K) (m : ℕ) (hz : z.length = 5 + m) : exL z 5 (5 + m) = z.drop 5 := by
  unfold exL
  rw [List.take_of_length_le]
  rw [List.length_drop]
  omega

/-- The planes at a point: the claim's sum is the run on BZ's virtual row. -/
theorem pay_bits (h : Sh) (hok : ok h = true) (hfull : 2 ^ h.cK = h.NC) (ν : Pl → K)
    (h0 : ν .zero = 0) (B : ℕ → ℕ → K) (hB : CellsBZ h ν B) (z : List K)
    (hz : z.length = 5 + (h.kT + h.cK)) (entry : ℕ → ℕ → ℕ → K) (iBZ e : ℕ)
    (hV : VirtRow entry iBZ e (fun r => (eqTabK (z.take 5)).getD r 0) B 32 (2 ^ (h.kT + h.cK))) :
    planesK h 5 z (colsK h 5 z ν) =
      runSum (fun i => (eqTabK (exL z 5 (5 + h.kT + h.cK))).getD i 0 * entry iBZ e i)
        (2 ^ (h.kT + h.cK)) 0 := by
  have e1 := plane_sum_g h hok 5 0 (le_refl 5) (Nat.le_add_left 5 h.kT) (0 : K) ν h0 z.reverse
    (by rw [List.length_reverse, hz]; rfl)
  rw [List.reverse_reverse] at e1
  have e2 := bits_on_bz (numsF h 5 0 (0 : K)) ν (h.kT + h.cK) B rfl rfl
    (onBZ_five h 0 0 ν B hfull hB) z hz
  rw [run_virt hV, Nat.add_assoc, exL_drop z _ hz, ← e2, e1]
  rfl

/-- The counts' sum: the claim's value is the constant and the run on BZ's virtual row. -/
theorem pay_count (h : Sh) (hok : ok h = true) (hfull : 2 ^ h.cK = h.NC) (h5 : 5 ≤ h.kT + h.cK)
    (ν : Pl → K) (h0 : ν .zero = 0) (B : ℕ → ℕ → K) (hB : CellsBZ h ν B)
    (entry : ℕ → ℕ → ℕ → K) (iBZ e : ℕ)
    (hV : VirtRow entry iBZ e (fun _ => 1) B 32 (2 ^ (h.kT + h.cK))) :
    countK h 5 (pinColK 5 ν) = -((2 ^ h.v - h.padding : ℕ) : K) +
      runSum (fun i => (2 : K) ^ (i % 32) * entry iBZ e i) (2 ^ (h.kT + h.cK)) 0 := by
  have e1 := pin_sum h 5 0 (0 : K) ν h0 (ok_facts h hok).2.1 (le_refl 5) (Nat.le_add_left 5 h.kT)
  have e2 := count_on_bz (numsF h 5 0 (0 : K)) ν (h.kT + h.cK) B rfl rfl h5
    (onBZ_five h 0 0 ν B hfull hB)
  unfold countK
  rw [foldl_add_from, ← e1, e2, run_virt hV]
  simp only [one_mul]

end
end Fo
