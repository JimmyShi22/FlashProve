-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/CsAt.lean: the row that the format's code switch computes, read at the places of the
layout of the library's code switch.

The library names the coordinates of a new message: the old message, the old tails, free room
(OnBytes/Slice/CsData.lean). The format holds the new row as two arrays, on the main table and on
the mask table. This file reads the format's new row at the place of each named coordinate.

Main theorems.
 `cs_cols`: if the format's switch gives a row, the row is the sum of all rows under the powers of
   theta, with the column of every drawn position.
 `cs_at`: that row at an entry of the new tables is the old form there, the sample's row under
   theta, and the three rows of each draw under the next three powers.

Not claimed. Nothing on the library's own form: that the two agree is another file's statement.
-/
import OnBytes.Slice.CsData
import OnBytes.Slice.SimCs
import OnBytes.Slice.CsRow
import OnBytes.Slice.CsSmp

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run
open Fmt.M1 (Stage SRow GRow Col csStep csStepLit sumRows cp)

variable {s s' : Sg}

/-- If the format's switch gives a row, the row is the sum of all rows under the powers of
theta, made with the tree's own columns. -/
theorem cs_cols (old new : Stage) (R : SRow) (smp : GRow) (xs : List ℕ) (theta : Fmt.M1.E)
    (col : ℕ → Col) (cols : ℕ → Option Col) (hcols : ∀ x c, cols x = some c → c = col x)
    (G' : GRow) (h : csStep .two old new R smp xs theta cols = some G') :
    G' = sumRows .two theta (allRows .two old new R smp xs col) := by
  -- A drawn position without a column would leave no list of rows, so no row.
  have hall : ∀ x ∈ xs, cols x = some (col x) := by
    intro x hx
    cases hc : cols x with
    | some c => rw [hcols x c hc]
    | none =>
      exfalso
      rw [Fmt.M1.CsEq.csStep_eq] at h
      unfold csStepLit at h
      rw [csRows_none .two old new R smp xs cols x hx hc] at h
      cases h
  rw [csStep_some .two old new R smp xs theta cols col hall] at h
  exact (Option.some.inj h).symm

/-- The format's new row at an entry of the layout. -/
theorem cs_at (hf : CsFit s s') (R : SRow) (smp : GRow) (xs : List ℕ) (theta : Fmt.M1.E)
    (col : ℕ → Col) (n : CsK s ⊕ CsFree hf) :
    tabAt (sumRows .two theta (allRows .two s.st s'.st R smp xs col)) (outAt s' (csPlace hf n))
      = ldPad (ldPad (vecMid s R)) n + toE theta * tabAt smp (outAt s' (csPlace hf n))
        + ∑ i ∈ Finset.range xs.length, toE theta ^ (2 + 3 * i) *
          (ldPad (midRow s (xs.getD i 0) (.inl ())) n
            + toE theta * ldPad (midRow s (xs.getD i 0) (.inr (.inl ()))) n
            + toE theta ^ 2 * ldPad (midRow s (xs.getD i 0) (.inr (.inr ()))) n) := by
  have hfit : 2 * s.Z.l + s.C.r + 2 * s.Z.r ≤ 2 ^ s'.h * s'.Z.l := by
    have := hf.mask
    omega
  generalize hG : sumRows .two theta (allRows .two s.st s'.st R smp xs col) = G
  rcases n with k | p
  · -- An entry of the old full message: six stretches, each with its own formula.
    rw [csPlace_inl, outAt_csPut]
    rcases k with (j | j | j) | (q | q | q)
    · have key : vec G.c (j.val)
          = vec R.c j.val + toE theta * vec smp.c (j.val)
            + ∑ i ∈ Finset.range xs.length, toE theta ^ (2 + 3 * i) * wM s.C (xs.getD i 0) j.val :=
        hG ▸ cs_at_main s.st s'.st R smp xs theta col j.val j.isLt (hf.main.symm ▸ j.isLt)
      show vec G.c (j.val)
          = vec R.c j.val + toE theta * vec smp.c (j.val)
            + ∑ i ∈ Finset.range xs.length, toE theta ^ (2 + 3 * i) *
              (wM s.C (xs.getD i 0) j.val + toE theta * 0 + toE theta ^ 2 * 0)
      rw [key]
      exact congrArg (_ + ·) (Finset.sum_congr rfl fun i _ => by ring)
    · have key : vec G.d (j.val)
          = vec R.d0 j.val + toE theta * vec smp.d (j.val)
            + ∑ i ∈ Finset.range xs.length, toE theta ^ (3 + 3 * i) *
                wM s.Z (cp s.Z (xs.getD i 0)) j.val :=
        hG ▸ cs_at_mask s.st s'.st R smp xs theta col hfit j.val j.isLt
      show vec G.d (j.val)
          = vec R.d0 j.val + toE theta * vec smp.d (j.val)
            + ∑ i ∈ Finset.range xs.length, toE theta ^ (2 + 3 * i) *
              (0 + toE theta * wM s.Z (cp s.Z (xs.getD i 0)) j.val + toE theta ^ 2 * 0)
      rw [key]
      exact congrArg (_ + ·) (Finset.sum_congr rfl fun i _ => by ring)
    · have key : vec G.d (s.Z.l + j.val)
          = vec R.d1 j.val + toE theta * vec smp.d (s.Z.l + j.val)
            + ∑ i ∈ Finset.range xs.length, toE theta ^ (4 + 3 * i) *
                wM s.Z (cp s.Z (xs.getD i 0)) j.val :=
        hG ▸ cs_at_fresh s.st s'.st R smp xs theta col hfit j.val j.isLt
      show vec G.d (s.Z.l + j.val)
          = vec R.d1 j.val + toE theta * vec smp.d (s.Z.l + j.val)
            + ∑ i ∈ Finset.range xs.length, toE theta ^ (2 + 3 * i) *
              (0 + toE theta * 0 + toE theta ^ 2 * wM s.Z (cp s.Z (xs.getD i 0)) j.val)
      rw [key]
      exact congrArg (_ + ·) (Finset.sum_congr rfl fun i _ => by ring)
    · have key : vec G.d (2 * s.Z.l + q.val)
          = toE theta * vec smp.d (2 * s.Z.l + q.val)
            + ∑ i ∈ Finset.range xs.length, toE theta ^ (2 + 3 * i) * wT s.C (xs.getD i 0) q.val :=
        hG ▸ cs_at_tail s.st s'.st R smp xs theta col hfit q.val q.isLt
      show vec G.d (2 * s.Z.l + q.val)
          = 0 + toE theta * vec smp.d (2 * s.Z.l + q.val)
            + ∑ i ∈ Finset.range xs.length, toE theta ^ (2 + 3 * i) *
              (wT s.C (xs.getD i 0) q.val + toE theta * 0 + toE theta ^ 2 * 0)
      rw [key, zero_add]
      exact congrArg (_ + ·) (Finset.sum_congr rfl fun i _ => by ring)
    · have key : vec G.d (2 * s.Z.l + s.C.r + q.val)
          = toE theta * vec smp.d (2 * s.Z.l + s.C.r + q.val)
            + ∑ i ∈ Finset.range xs.length, toE theta ^ (3 + 3 * i) *
                wT s.Z (cp s.Z (xs.getD i 0)) q.val :=
        hG ▸ cs_at_maskTail s.st s'.st R smp xs theta col hfit q.val q.isLt
      show vec G.d (2 * s.Z.l + s.C.r + q.val)
          = 0 + toE theta * vec smp.d (2 * s.Z.l + s.C.r + q.val)
            + ∑ i ∈ Finset.range xs.length, toE theta ^ (2 + 3 * i) *
              (0 + toE theta * wT s.Z (cp s.Z (xs.getD i 0)) q.val + toE theta ^ 2 * 0)
      rw [key, zero_add]
      exact congrArg (_ + ·) (Finset.sum_congr rfl fun i _ => by ring)
    · have key : vec G.d (2 * s.Z.l + s.C.r + s.Z.r + q.val)
          = toE theta * vec smp.d (2 * s.Z.l + s.C.r + s.Z.r + q.val)
            + ∑ i ∈ Finset.range xs.length, toE theta ^ (4 + 3 * i) *
                wT s.Z (cp s.Z (xs.getD i 0)) q.val :=
        hG ▸ cs_at_freshTail s.st s'.st R smp xs theta col hfit q.val q.isLt
      show vec G.d (2 * s.Z.l + s.C.r + s.Z.r + q.val)
          = 0 + toE theta * vec smp.d (2 * s.Z.l + s.C.r + s.Z.r + q.val)
            + ∑ i ∈ Finset.range xs.length, toE theta ^ (2 + 3 * i) *
              (0 + toE theta * 0 + toE theta ^ 2 * wT s.Z (cp s.Z (xs.getD i 0)) q.val)
      rw [key, zero_add]
      exact congrArg (_ + ·) (Finset.sum_congr rfl fun i _ => by ring)
  · -- Free room: the sample's row alone.
    obtain ⟨i, hi, hlo, hhi⟩ := free_at hf p
    rw [csPlace_inr, hi]
    have key : vec G.d i = cut (2 ^ s'.h * s'.Z.l) (fun j => toE theta * vec smp.d j) i :=
      hG ▸ cs_at_free s.st s'.st R smp xs theta col i hlo
    show vec G.d i
        = 0 + toE theta * vec smp.d i + ∑ i ∈ Finset.range xs.length, toE theta ^ (2 + 3 * i) *
            (0 + toE theta * 0 + toE theta ^ 2 * 0)
    rw [key, cut_of_lt hhi]
    simp only [mul_zero, add_zero, zero_add, Finset.sum_const_zero]

end OnBytes.Slice

#print axioms OnBytes.Slice.cs_cols
#print axioms OnBytes.Slice.cs_at
