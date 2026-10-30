-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Packing.lean: the two packings of a fold's fresh mask table are one. The
coefficients of a fold's hiding polynomial are laid into the fresh mask table in two texts: the
library's packing, of which the laws on a fold's claim speak (`pkC`, Cb/Ld/LdSumPack.lean, at the
format's places; by numbers: `packedN`, Johnson/Prover/Link/BodyPack.lean), and the row of the
format library's own honest prover (`Fmt.M1.FoldOwn.freshRow`, Fmt/M1Fold.lean), a list of words.
This file proves that the two are equal entry by entry (`packing_one`), at every stage that has
room for the packing, all coefficients, every row's number and every place. Definitions, statements
and proofs. It depends on no frame for an honest side: nothing under
Johnson/Desc/ProofFile/Honest/ is imported.

In the list: a fold is the sumcheck protocol of Cb/Ld/LdSum.lean. A stage s (`Sg`,
OnBytes/Slice/Stage.lean) has the numbers h and g. The polynomial has k = h + g variables, numbered
from 1, each with the exponents 1 and 2, and a constant. W gives its coefficients under the
library's names (`hIx` for a variable and an exponent, `hCst` for the constant;
Cb/Ld/LdSumPack.lean). w and w0 give them by numbers: w l t is the coefficient of variable number l
at the exponent t, and w0 is the constant. A word is an element of the format (`Fmt.Ext3`,
Fmt/FieldE.lean: three machine words); `toE` reads a word in the field `GE`, and
`ofE` writes an element of `GE` as a word (OnBytes/Slice/Field.lean). The corner of a row's number b
is the point of the cube whose coordinate t, for t below h, is bit t of b. A column is an element of
`PCol h g 1` (Cb/Ld/LdSumPack.lean); its place is `hidePlace h g` (OnBytes/Slice/SimFold.lean).

  `packing_one`: for a stage s, under the two hypotheses below, at every row's number r and every
    place j: `packedN s W r j` is the word at place j of the row
    `freshRow .two (s.h + s.g) s.h (hideOfW w w0) r`, read in the field; past the list's end the
    word `zeroE` is read. From the place h + 2 g + 1 on both sides are 0: the proof shows this, and
    no theorem of its own states it
  `row_at`: under `Named (h + g) W w w0`, at every row's number b and every column c: the word of
    `freshRow .two (h + g) h (hideOfW w w0) b` at the place of c, read in the field, is
    `pkC h g 1 W` at the corner of b and at c
  `Named k W w w0`: a definition, a proposition with two fields. `coeff`: W at the name `hIx` of l
    and p, both counted from 0, is w (l + 1) (p + 1). `const`: W at `hCst` is w0. It determines W,
    since every name is one of these (`ld_pack_names`, Cb/Ld/LdSumPackProofs.lean); that
    consequence is not stated here. It reads w only at 1 ≤ l ≤ k and t = 1, 2, as `freshRow` does
    where h ≤ k
  `hideOfW w w0`: a definition: w and w0, each value written as a word by `ofE`, in the structure
    `Hide` (Fmt/M1Fold.lean) that `freshRow` takes
  `freshRow_layL`: at both fields of the format and all h, n, U, b: `freshRow f (h + n) h U b` is
    the list `layL` (OnBytes/Slice/SimFold.lean: the order of the format's vector of weights) at
    arguments that are written out in the statement
  `pMon_reaches`: the library's monomial `pMon i` (Cb/Ld/LdSumPack.lean: the variables number i + 1
    to h) at the corner of b is 1 where `reaches h b (i + 1)` (Fmt/M1Fold.lean) is true, else 0
  `lead_sum`: under `Named`: the first h variables' coefficients at the exponent 1, each times its
    `pMon` at the corner of b, add up to the sum of w (i + 1) 1, written as a word and read back,
    over the i below h at which `reaches h b (i + 1)` is true
  `toE_gather`: a `List.foldl` that starts at the word a and adds, by the format's `addE` at the
    field `.two`, the word x i for each i below n at which P i is true: read in the field, it is
    the reading of a plus the field's sum of the readings of these x i

By what. `freshRow_layL` unfolds `freshRow`, `layL` and `midL` (OnBytes/Slice/SimFold.lean).
`pMon_reaches` unfolds `pMon` and `reaches`. `toE_gather` is an induction on n with `toE_addE`
(OnBytes/Slice/Field.lean). `lead_sum` calls `Named.coeff`, `pMon_reaches` and `toE_ofE` (same
file). `row_at` rewrites by `freshRow_layL` and goes through the three kinds of column: it reads
the list by `layL_zero`, `layL_hd`, `layL_lin`, `layL_sq` and `layL_one`
(OnBytes/Slice/SimFold.lean) and the words by `toE_ofE` and `toE_zeroE` (OnBytes/Slice/Field.lean),
and at the leading column (`pLead`, Cb/Ld/LdSumPack.lean) it calls `lead_sum` and `toE_gather`.
`packing_one`: where j is a column's place, `row_at`, `placeV_at` (Cb/Ld/LdSumPackProofs.lean),
`placeF_inj` (Johnson/Prover/Link/FoldHolds.lean) and `hidePlace_lt` (OnBytes/Slice/SimFold.lean);
else h + 2 g + 1 ≤ j by `hidePlace_surj`, and the row has no word there by `layL_far` (same file).

Hypotheses of `packing_one`. hl: s.h + 2 * s.g + 1 ≤ s.Z.l: the stage has room for the packing
(`s.Z`: the code of a mask row; `l`: the number of entries of its messages, Fmt/M1Codes.lean).
N: `Named (s.h + s.g) W w w0`.

Limits. Without room for the packing (h + 2 g + 1 places in a mask row's message) `packedN` is 0,
whatever the row holds: the statement asks the room. The row's number is read at its lowest h bits
only, on both sides. `row_at` and `packing_one` are at the format's field `.two` and at `pkC` with
m = 1 (the exponents 1 and 2) only. `Named` can be met at all w, w0 (`named_byName`,
Johnson/Desc/ProofFile/Honest/K12/PackingAt.lean). An equation between two texts: nothing on who
lays either, on a tail, on how the coefficients are chosen, on a verifier's decision. Nothing on
completeness, on soundness or on what is hidden.
-/
import Johnson.Prover.Link.BodyPack
import OnBytes.Slice.SimFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open Johnson.Prover.Link
open Fmt.M1.FoldOwn (Hide freshRow reaches)

/-- The coefficients w and w0, each written as a word by `ofE`, in the structure `Hide` that
`freshRow` takes. -/
def hideOfW (w : ℕ → ℕ → GE) (w0 : GE) : Hide := ⟨fun l t => ofE (w l t), ofE w0⟩

/-- The coefficients W, under the library's names (`hIx`, `hCst`), are w (by the variable's number
from 1 and the exponent, 1 or 2) and the constant w0. -/
structure Named (k : ℕ) (W : HIdx (sVars GE 2 k) → GE) (w : ℕ → ℕ → GE) (w0 : GE) : Prop where
  coeff : ∀ (l : Fin k) (p : Fin 2), W (hIx GE 2 k l p) = w (l.val + 1) (p.val + 1)
  const : W (hCst GE 2 k) = w0

/-- `freshRow`, written as the list `layL`: the order of the format's vector of weights. -/
theorem freshRow_layL (f : Fmt.Fld) (h n : ℕ) (U : Hide) (b : ℕ) :
    freshRow f (h + n) h U b =
      layL ((List.range h).foldl
          (fun s i => if reaches h b (i + 1) then f.addE s (U.w (i + 1) 1) else s)
          (if 0 < n then U.w (h + 1) 1 else U.w0))
        (fun i => if reaches h b (i + 1) then U.w (i + 1) 2 else Fmt.Fld.zeroE)
        (fun t => U.w (h + 1 + t) 1) (fun t => U.w (h + 1 + t) 2) U.w0 h n := by
  cases n with
  | zero =>
    unfold freshRow layL midL
    simp
  | succ m =>
    have h1 : h < h + (m + 1) := by omega
    have h2 : h + (m + 1) - h - 1 = m := by omega
    unfold freshRow layL midL
    rw [if_pos h1, if_pos h1, h2, if_pos (Nat.succ_pos m), if_pos (Nat.succ_pos m),
      List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp [Nat.add_comm, Nat.add_left_comm]

/-- The library's monomial `pMon i` at the corner of the row's number b is 1 where
`reaches h b (i + 1)` is true, else 0. -/
theorem pMon_reaches (h : ℕ) (i : Fin h) (b : ℕ) :
    (pMon i (fun t : Fin h => b.testBit t.val) : GE) =
      if reaches h b (i.val + 1) then 1 else 0 := by
  unfold pMon reaches
  by_cases hr : ((List.range (h + 1 - (i.val + 1))).all
      fun j => b.testBit (i.val + 1 - 1 + j)) = true
  · rw [if_pos hr]
    refine Finset.prod_eq_one fun j _ => ?_
    by_cases hij : i ≤ j
    · rw [if_pos hij]
      rw [List.all_eq_true] at hr
      have hj := j.isLt
      have hle := Fin.le_def.1 hij
      have e := hr (j.val - i.val) (List.mem_range.2 (by omega))
      rw [show i.val + 1 - 1 + (j.val - i.val) = j.val by omega] at e
      rw [if_pos e]
    · rw [if_neg hij]
  · rw [if_neg hr]
    rw [List.all_eq_true] at hr
    obtain ⟨x, hx, hb⟩ : ∃ x, x ∈ List.range (h + 1 - (i.val + 1)) ∧
        ¬ b.testBit (i.val + 1 - 1 + x) = true := by
      by_contra hc
      exact hr fun x hx => by_contra fun hb => hc ⟨x, hx, hb⟩
    have hx' := List.mem_range.1 hx
    have hi := i.isLt
    refine Finset.prod_eq_zero (Finset.mem_univ (⟨i.val + x, by omega⟩ : Fin h)) ?_
    rw [if_pos (Fin.le_def.2 (Nat.le_add_right _ _))]
    rw [show i.val + 1 - 1 + x = i.val + x by omega] at hb
    rw [if_neg hb]

/-- A sum that `List.foldl` gathers word by word with the format's `addE`, read in the field, is the
reading of the first word plus the field's sum of the readings. -/
theorem toE_gather (P : ℕ → Bool) (x : ℕ → Fmt.Ext3) (a : Fmt.Ext3) : ∀ n : ℕ,
    toE ((List.range n).foldl (fun s i => if P i then Fmt.Fld.two.addE s (x i) else s) a) =
      toE a + ∑ i ∈ Finset.range n, if P i then toE (x i) else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← add_assoc,
      ← toE_gather P x a n]
    simp only [List.foldl_cons, List.foldl_nil]
    split
    · rw [toE_addE]
    · rw [add_zero]

section At
variable (h g : ℕ) (W : HIdx (sVars GE 2 (h + g)) → GE) (w : ℕ → ℕ → GE) (w0 : GE)

/-- The terms of the first h variables at the exponent 1, which `pkC` adds to its leading column, as
a sum over the i below h at which `reaches h b (i + 1)` is true. -/
theorem lead_sum (N : Named (h + g) W w w0) (b : ℕ) :
    (∑ i : Fin h, W (hIx GE 2 (h + g) (Fin.castAdd g i) 0) *
      pMon i (fun t : Fin h => b.testBit t.val)) =
      ∑ i ∈ Finset.range h, if reaches h b (i + 1) then toE (ofE (w (i + 1) 1)) else 0 := by
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [N.coeff, pMon_reaches, toE_ofE]
  show w (i.val + 1) 1 * _ = _
  split
  · rw [mul_one]
  · rw [mul_zero]

/-- At the place of each column of the library's packing `freshRow` holds that column's entry.
b: the row's number. c: the column. -/
theorem row_at (N : Named (h + g) W w w0) (b : ℕ) (c : PCol h g 1) :
    toE ((freshRow .two (h + g) h (hideOfW w w0) b).getD (hidePlace h g c) Fmt.Fld.zeroE) =
      pkC h g 1 W (fun t : Fin h => b.testBit t.val, c) := by
  rw [freshRow_layL]
  rcases c with ⟨i, q⟩ | ⟨t, p⟩ | u
  · have hq : q = 0 := Subsingleton.elim _ _
    subst hq
    show toE ((layL _ _ _ _ _ h g).getD (1 + i.val) Fmt.Fld.zeroE) =
      W (hIx GE 2 (h + g) (Fin.castAdd g i) (Fin.succ 0)) *
        pMon i (fun t : Fin h => b.testBit t.val)
    rw [layL_hd _ _ _ _ _ _ _ _ _ i.isLt, N.coeff, pMon_reaches]
    show toE (if reaches h b (i.val + 1) then ofE (w (i.val + 1) 2) else Fmt.Fld.zeroE) =
      w (i.val + 1) 2 * _
    split
    · rw [toE_ofE, mul_one]
    · rw [toE_zeroE, mul_zero]
  · have hg : 0 < g := Nat.lt_of_le_of_lt (Nat.zero_le _) t.isLt
    show toE ((layL _ _ _ _ _ h g).getD
        (if t.val = 0 ∧ p.val = 0 then 0 else h + 2 * t.val + p.val) Fmt.Fld.zeroE) =
      W (hIx GE 2 (h + g) (Fin.natAdd h t) p) +
        if decide (t.val = 0 ∧ p.val = 0) = true then
          ∑ i : Fin h, W (hIx GE 2 (h + g) (Fin.castAdd g i) 0) *
            pMon i (fun t : Fin h => b.testBit t.val)
        else 0
    rw [N.coeff]
    show _ = w (h + t.val + 1) (p.val + 1) + _
    by_cases h0 : t.val = 0 ∧ p.val = 0
    · rw [if_pos h0, if_pos (decide_eq_true h0), layL_zero, lead_sum h g W w w0 N b, if_pos hg]
      show toE ((List.range h).foldl (fun s i =>
        if reaches h b (i + 1) then Fmt.Fld.two.addE s (ofE (w (i + 1) 1)) else s)
          (ofE (w (h + 1) 1))) = _
      rw [toE_gather (fun i => reaches h b (i + 1)) (fun i => ofE (w (i + 1) 1)), toE_ofE, h0.1,
        h0.2]
    · rw [if_neg h0, if_neg (show ¬ decide (t.val = 0 ∧ p.val = 0) = true by simpa using h0),
        add_zero]
      by_cases hp : p.val = 0
      · rw [hp, Nat.add_zero (h + 2 * t.val), layL_lin _ _ _ _ _ _ _ _ _ (by omega) t.isLt]
        show toE (ofE (w (h + 1 + t.val) 1)) = _
        rw [toE_ofE, show h + 1 + t.val = h + t.val + 1 by omega]
      · have hp1 : p.val = 1 := by have := p.isLt; omega
        rw [hp1, layL_sq _ _ _ _ _ _ _ _ _ t.isLt]
        show toE (ofE (w (h + 1 + t.val) 2)) = _
        rw [toE_ofE, show h + 1 + t.val = h + t.val + 1 by omega]
  · show toE ((layL _ _ _ _ _ h g).getD (if g = 0 then 0 else h + 2 * g) Fmt.Fld.zeroE) =
      W (hCst GE 2 (h + g)) +
        if decide (g = 0) = true then
          ∑ i : Fin h, W (hIx GE 2 (h + g) (Fin.castAdd g i) 0) *
            pMon i (fun t : Fin h => b.testBit t.val)
        else 0
    rw [N.const]
    by_cases hg : g = 0
    · rw [if_pos hg, if_pos (decide_eq_true hg), layL_zero, lead_sum h g W w w0 N b,
        if_neg (by omega)]
      show toE ((List.range h).foldl (fun s i =>
        if reaches h b (i + 1) then Fmt.Fld.two.addE s (ofE (w (i + 1) 1)) else s) (ofE w0)) = _
      rw [toE_gather (fun i => reaches h b (i + 1)) (fun i => ofE (w (i + 1) 1)), toE_ofE]
    · rw [if_neg hg, if_neg (show ¬ decide (g = 0) = true by simpa using hg), add_zero,
        layL_one _ _ _ _ _ _ _ _ (Nat.pos_of_ne_zero hg)]
      exact toE_ofE w0

end At

/-- **The two packings are one.** Where the stage has room for the packing, `packedN s W r j` is the
word at place j of `freshRow`, read in the field. r: the row's number. j: the place in the row's
message. -/
theorem packing_one (s : Sg) (hl : s.h + 2 * s.g + 1 ≤ s.Z.l)
    (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (w : ℕ → ℕ → GE) (w0 : GE)
    (N : Named (s.h + s.g) W w w0) (r j : ℕ) :
    packedN s W r j =
      toE ((freshRow .two (s.h + s.g) s.h (hideOfW w w0) r).getD j Fmt.Fld.zeroE) := by
  by_cases hex : ∃ c, hidePlace s.h s.g c = j
  · obtain ⟨c, rfl⟩ := hex
    have hj : hidePlace s.h s.g c < s.Z.l := lt_of_lt_of_le (hidePlace_lt s.h s.g c) hl
    rw [row_at s.h s.g W w w0 N r c]
    unfold packedN
    rw [dif_pos ⟨hl, hj⟩]
    exact placeV_at (placeF_inj s hl) (fun c => pkC s.h s.g 1 W (fun t => r.testBit t.val, c)) c
  · have hfar : s.h + 2 * s.g + 1 ≤ j := by
      by_contra hlt
      exact hex (hidePlace_surj s.h s.g j (by omega))
    rw [freshRow_layL, layL_far _ _ _ _ _ _ _ _ _ hfar, toE_zeroE]
    unfold packedN
    split
    · rename_i hh
      exact Finset.sum_eq_zero fun c _ => if_neg fun e => hex ⟨c, congrArg Fin.val e⟩
    · rfl

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.freshRow_layL
#print axioms ProofFile.Honest.K12.pMon_reaches
#print axioms ProofFile.Honest.K12.toE_gather
#print axioms ProofFile.Honest.K12.lead_sum
#print axioms ProofFile.Honest.K12.row_at
#print axioms ProofFile.Honest.K12.packing_one
#print axioms ProofFile.Honest.K12.hideOfW
#print axioms ProofFile.Honest.K12.Named
