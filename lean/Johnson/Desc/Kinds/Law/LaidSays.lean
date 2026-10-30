-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/LaidSays.lean.
WHAT IT DOES NOT SHOW. No soundness. Not that any block asks Laid.ok: that the seated block does,
and that the seat's own numbers (Stored/HeadSeatAt.lean: laidAt, laidOk) are laidOf's, is Law/
SeatedSays.lean's. The two records of numbers are typed in after Law/K06Condition.lean's (hSmall,
bSmall, hFull, bFull), of which only the fields that laidOf and the sizes read are given: no tie.
WHAT IT IS. What Kinds/HeadLaid.lean's test says, clause by clause, in the letters of the program's
own records (OnBytes/Model/HeadLayout.lean: Shape; HeadPlan.lean: Border).
  sizesAt, laidOf   the sizes and the numbers beside them, of a shape and the stream's border.
  laid_says         where the test says yes: 0 < d; 0 < lt; lt <= la; ls <= lPd; the plan's lPd is
                    the text's; XL = 5; the tensor has 5 limbs; lt + lPd <= 63; la <= 63; off = 0;
                    cnt J = d; 5 d / S2 <= kxb (mxb / 2^la); JV = V; clipC < 2^40;
                    theta < 2^40; digSh = 8.
  laid_small, laid_full   it says yes at the two records.
  laid_no_*         seventeen controls at the small record with a number or two turned: WHICH TESTS
                    SAY NO, BY NAME: just the one meant, but for d := 0, at which four do, and for
                    la := 64, at which two do. Each of the seventeen tests says no in one of them.

-/
import Mathlib
import Johnson.Desc.Kinds.HeadLaid
import OnBytes.Model.HeadPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model.Head (Shape Border)
open Norm (lt ls d lPd T S2)

/-- The sizes, of the head's public numbers: Stored/HeadSeatAt.lean's sizesOf, typed again: that
file stands above this one's needs. -/
@[reducible] def sizesAt (h : Shape) : Sizes :=
  { lt := h.lt, ls := h.ls, d := h.d, MF := h.MF, KF := h.KF, epsF := h.epsF, V := h.V,
    sh := h.digSh, F := h.famF }

/-- The policy, of the head's public numbers (Stored/HeadSeatAt.lean: parOf's). -/
@[reducible] def policyAt (h : Shape) : Policy := { C := h.clipC, theta := h.theta, cap := h.cap }

/-- The numbers beside the sizes. -/
def laidOf (h : Shape) (b : Border) : Laid :=
  { la := h.la, padLog := h.lPd, limbs := h.XL, laidLimbs := b.nl, off := b.off,
    step := b.cnt * b.J, room := b.kxb * (b.mxb / 2 ^ h.la) }

/-- **What the test says.** -/
theorem laid_says (h : Shape) (b : Border)
    (hok : (letI := sizesAt h; letI := policyAt h; (laidOf h b).ok) = true) :
    0 < h.d ∧ 0 < h.lt ∧ h.lt ≤ h.la ∧ (letI := sizesAt h; ls ≤ lPd) ∧
      (letI := sizesAt h; h.lPd = lPd) ∧ h.XL = 5 ∧ b.nl = 5 ∧
      (letI := sizesAt h; lt + lPd ≤ 63) ∧ h.la ≤ 63 ∧ b.off = 0 ∧ b.cnt * b.J = h.d ∧
      5 * h.d / h.S2 ≤ b.kxb * (b.mxb / 2 ^ h.la) ∧ (letI := sizesAt h; JV = V) ∧
      h.clipC < 2 ^ 40 ∧ h.theta < 2 ^ 40 ∧ h.digSh = 8 := by
  letI := sizesAt h
  letI := policyAt h
  unfold Laid.ok Laid.tests laidOf at hok
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true, decide_eq_true_eq,
    beq_iff_eq] at hok
  obtain ⟨a1, a2, a3, _, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := hok
  exact ⟨a1, a2, a3, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩

/-! ## At the two records, and seventeen controls -/

/-- The head's public numbers at the stored small set: copied by program from another file's record
(Law/K06Condition.lean: hSmall). -/
def hSmall9 : Shape :=
  { lt := 6,
    la := 8,
    d := 512,
    lPd := 9,
    V := 512,
    MF := 43,
    KF := 30,
    epsF := 1,
    toksrc := 1,
    wbEmb := 21,
    wbHead := 13,
    clipC := 256,
    theta := 256,
    cap := 0,
    logS := 16,
    digSh := 8,
    tabS := 4,
    famF := 24,
    lmhf := 14,
    NHf := 1,
    lmhd := 12,
    lmhr := 12,
    lmbH := 13,
    iotaH := [0, 0, 0, 0, 0, 0],
    nmin := 20,
    NMINH := 0,
    LIDB := 24,
    XL := 5,
    polCallsH := [["R16a", "R16", "NF", "NFH", "HD0"],
                  ["R16b", "R16", "HD1"],
                  ["R8", "R8", "ROW", "HD2"],
                  ["FEa", "FE", "HE0"],
                  ["FEb", "FE", "HE1"],
                  ["FC", "FC", "CNF"]] }

/-- The same at a stored FULL-SIZE set of another build than the one that ships. -/
def hFull9 : Shape :=
  { lt := 10,
    la := 16,
    d := 5120,
    lPd := 13,
    V := 202048,
    MF := 44,
    KF := 30,
    epsF := 53687,
    toksrc := 1,
    wbEmb := 21,
    wbHead := 13,
    clipC := 256,
    theta := 256,
    cap := 0,
    logS := 15,
    digSh := 8,
    tabS := 4,
    famF := 24,
    lmhf := 16,
    NHf := 4,
    lmhd := 14,
    lmhr := 13,
    lmbH := 15,
    iotaH := [1, 1, 1, 0, 0, 0],
    nmin := 20,
    NMINH := 27,
    LIDB := 28,
    XL := 5,
    polCallsH := [["R16a", "R16", "NF", "NFH", "HD0"],
                  ["R16b", "R16", "HD1"],
                  ["R8", "R8", "ROW", "HD2"],
                  ["FEa", "FE", "HE0"],
                  ["FEb", "FE", "HE1"],
                  ["FC", "FC", "CNF"]] }

/-- What the head needs to know of the layers' layout, at the two sets. -/
def bSmall9 : Border := { mxb := 8192, kxb := 20, off := 0, nl := 5, cnt := 1, J := 512 }
def bFull9 : Border :=
  { mxb := 65536, kxb := 400, off := 0, nl := 5, cnt := 1, J := 5120 }

theorem laid_small : (letI := sizesAt hSmall9;
    letI := policyAt hSmall9;
    (laidOf hSmall9 bSmall9).ok) = true := by decide

theorem laid_full : (letI := sizesAt hFull9;
    letI := policyAt hFull9;
    (laidOf hFull9 bFull9).ok) = true := by decide

theorem laid_no_feature : (letI := sizesAt { hSmall9 with d := 0 };
    letI := policyAt { hSmall9 with d := 0 };
    (laidOf { hSmall9 with d := 0 } bSmall9).fails) = ["features", "block", "pad", "step"] := by
  decide

theorem laid_no_four_limbs : (letI := sizesAt { hSmall9 with XL := 4 };
    letI := policyAt { hSmall9 with XL := 4 };
    (laidOf { hSmall9 with XL := 4 } bSmall9).fails) = ["limbs"] := by decide

theorem laid_no_tensor_limbs : (letI := sizesAt hSmall9;
    letI := policyAt hSmall9;
    (laidOf hSmall9 { bSmall9 with nl := 4 }).fails) = ["the tensor's limbs"] := by decide

theorem laid_no_off : (letI := sizesAt hSmall9;
    letI := policyAt hSmall9;
    (laidOf hSmall9 { bSmall9 with off := 1 }).fails) = ["origin"] := by decide

theorem laid_no_step : (letI := sizesAt hSmall9;
    letI := policyAt hSmall9;
    (laidOf hSmall9 { bSmall9 with J := 513 }).fails) = ["step"] := by decide

theorem laid_no_room : (letI := sizesAt hSmall9;
    letI := policyAt hSmall9;
    (laidOf hSmall9 { bSmall9 with kxb := 19 }).fails) = ["stream"] := by decide

theorem laid_no_rows : (letI := sizesAt { hSmall9 with la := 5 };
    letI := policyAt { hSmall9 with la := 5 };
    (laidOf { hSmall9 with la := 5 } bSmall9).fails) = ["rows"] := by decide

theorem laid_no_pad : (letI := sizesAt { hSmall9 with lPd := 10 };
    letI := policyAt { hSmall9 with lPd := 10 };
    (laidOf { hSmall9 with lPd := 10 } bSmall9).fails) = ["pad"] := by decide

theorem laid_no_seven : (letI := sizesAt { hSmall9 with digSh := 7 };
    letI := policyAt { hSmall9 with digSh := 7 };
    (laidOf { hSmall9 with digSh := 7 } bSmall9).fails) = ["shift"] := by decide

theorem laid_no_whole : (letI := sizesAt { hSmall9 with V := 511 };
    letI := policyAt { hSmall9 with V := 511 };
    (laidOf { hSmall9 with V := 511 } bSmall9).fails) = ["whole"] := by decide

theorem laid_no_clip : (letI := sizesAt { hSmall9 with clipC := 2 ^ 40 };
    letI := policyAt { hSmall9 with clipC := 2 ^ 40 };
    (laidOf { hSmall9 with clipC := 2 ^ 40 } bSmall9).fails) = ["clip"] := by decide

theorem laid_no_mean : (letI := sizesAt { hSmall9 with theta := 2 ^ 40 };
    letI := policyAt { hSmall9 with theta := 2 ^ 40 };
    (laidOf { hSmall9 with theta := 2 ^ 40 } bSmall9).fails) = ["mean"] := by decide

theorem laid_no_point : (letI := sizesAt { hSmall9 with lt := 0, la := 2 };
    letI := policyAt { hSmall9 with lt := 0, la := 2 };
    (laidOf { hSmall9 with lt := 0, la := 2 } { bSmall9 with mxb := 128 }).fails) = ["point"] := by
  decide

/-- "block" alone: a block of 2^10 features over d = 512, whose padding has 2^9. -/
theorem laid_no_block : (letI := sizesAt { hSmall9 with la := 16, V := 1024 };
    letI := policyAt { hSmall9 with la := 16, V := 1024 };
    (laidOf { hSmall9 with la := 16, V := 1024 } { bSmall9 with mxb := 2 ^ 21 }).fails) =
      ["block"] := by
  decide

theorem laid_no_index : (letI := sizesAt { hSmall9 with lt := 60, la := 62 };
    letI := policyAt { hSmall9 with lt := 60, la := 62 };
    (laidOf { hSmall9 with lt := 60, la := 62 } { bSmall9 with mxb := 2 ^ 70 }).fails) =
      ["index"] := by
  decide

/-- "block's logarithm": at letters alone: no seat whose sizes take ls as la - lt can fail it. -/
theorem laid_no_logarithm : (letI := sizesAt hSmall9;
    letI := policyAt hSmall9;
    ({ laidOf hSmall9 bSmall9 with la := 9 } : Laid).fails) = ["block's logarithm"] := by decide

theorem laid_no_rows_index : (letI := sizesAt hSmall9;
    letI := policyAt hSmall9;
    ({ laidOf hSmall9 bSmall9 with la := 64 } : Laid).fails) =
      ["block's logarithm", "rows' index"] := by decide

end VerifiableInference.Desc.Kinds.Head.Law
