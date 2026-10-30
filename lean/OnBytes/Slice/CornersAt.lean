-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/CornersAt.lean: at the sizes of an entry file, different entries have different
corners.

OnBytes/Slice/LinkAt.lean names an entry of the layout that is compared, and an entry of a folded
row's oracle message, by a vertex of a cube: the binary digits of the entry's index. The library's
theorems ask that this naming is injective. This file proves it from the facts on natural numbers
of OnBytes/Slice/Corners.lean.

Main theorems.
 `cut_le_two_pow`     the layout that is compared fits its cube, at every record of sizes.
 `rows_le_two_pow`    the rows of a folded row's oracle message fit their digits, likewise.
 `lw_pl_inj`          the corners of the layout that is compared are different.
 `memb_plc_inj`       the corners of a folded row's oracle message are different.


Not claimed. That the places of a row fit their digits at every record of sizes: the number of
digits is rounded down there, so this holds only if the number of places is 0 or a power of 2.
-/
import OnBytes.Slice.LinkAt
import OnBytes.Slice.Corners
import Fmt.M3Items
import Fmt.M3Dec
import Fmt.ParamsRead
import Fmt.Rules5Fast

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## What holds at every record of sizes -/

/-- The layout that is compared fits its cube. -/
theorem cut_le_two_pow (P : Fmt.M3.Par) : P.cut ≤ 2 ^ P.aPhi :=
  le_trans (Nat.sub_le P.T.l (3 * P.s)) (le_two_pow_clog P.T.l)

/-- The rows of a folded row's oracle message fit their digits. -/
theorem rows_le_two_pow (P : Fmt.M3.Par) : P.R ≤ 2 ^ P.aR :=
  le_two_pow_clog P.R

/-! ## The layout that is compared -/

/-- The corners of the layout that is compared are different. -/
theorem lw_pl_inj (S : Sz) (h : S.P.cut ≤ 2 ^ S.P.aPhi) : Function.Injective S.lw.pl := by
  intro (a : Fin S.P.cut) (b : Fin S.P.cut) hab
  have hbit : ∀ t : Fin S.P.aPhi, a.val.testBit t.val = b.val.testBit t.val :=
    fun t => congrFun hab t
  exact Fin.ext
    (testBit_inj S.P.aPhi (lt_of_lt_of_le a.isLt h) (lt_of_lt_of_le b.isLt h) hbit)

/-! ## A folded row's oracle message -/

/-- The index of an entry is below the number of vertices of the cube. -/
theorem idxJ_lt (S : Sz) (hR : S.P.R ≤ 2 ^ S.P.aR) (hl : S.P.C.l ≤ 2 ^ S.P.aP) (j : S.MJ) :
    S.idxJ j < 2 ^ (S.P.aR + S.P.aP) := by
  rcases j with x | x
  · have h1 : x.1.val < 2 ^ S.P.aR := lt_of_lt_of_le x.1.isLt hR
    have h2 : x.2.val + 1 ≤ 2 ^ S.P.aP := le_trans x.2.isLt hl
    calc x.1.val + 2 ^ S.P.aR * x.2.val
        < 2 ^ S.P.aR + 2 ^ S.P.aR * x.2.val := Nat.add_lt_add_right h1 _
      _ = 2 ^ S.P.aR * (x.2.val + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ 2 ^ S.P.aR * 2 ^ S.P.aP := Nat.mul_le_mul_left _ h2
      _ = 2 ^ (S.P.aR + S.P.aP) := (Nat.pow_add 2 _ _).symm
  · exact x.1.elim

/-- Different entries have different indices. -/
theorem idxJ_inj (S : Sz) (hR : S.P.R ≤ 2 ^ S.P.aR) : Function.Injective S.idxJ := by
  intro j j' h
  rcases j with x | x
  · rcases j' with y | y
    · have hxy : x.1.val = y.1.val ∧ x.2.val = y.2.val :=
        idx_inj S.P.aR (lt_of_lt_of_le x.1.isLt hR) (lt_of_lt_of_le y.1.isLt hR) h
      exact congrArg Sum.inl (Prod.ext (Fin.ext hxy.1) (Fin.ext hxy.2))
    · exact y.1.elim
  · exact x.1.elim

/-- The corners of a folded row's oracle message, the pad left out, are different. -/
theorem memb_plc_inj (S : Sz) (hR : S.P.R ≤ 2 ^ S.P.aR) (hl : S.P.C.l ≤ 2 ^ S.P.aP) :
    Function.Injective S.memb.plc := by
  intro (j : {j : S.MJ // j ≠ S.padJ}) (j' : {j : S.MJ // j ≠ S.padJ}) h
  have hbit : ∀ t : Fin (S.P.aR + S.P.aP),
      (S.idxJ j.1).testBit t.val = (S.idxJ j'.1).testBit t.val := fun t => congrFun h t
  have hidx : S.idxJ j.1 = S.idxJ j'.1 :=
    testBit_inj _ (idxJ_lt S hR hl j.1) (idxJ_lt S hR hl j'.1) hbit
  exact Subtype.ext (idxJ_inj S hR hidx)

/-! ## The small test configuration -/

end OnBytes.Slice

#print axioms OnBytes.Slice.cut_le_two_pow
#print axioms OnBytes.Slice.rows_le_two_pow
#print axioms OnBytes.Slice.lw_pl_inj
#print axioms OnBytes.Slice.memb_plc_inj
