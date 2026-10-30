-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/HeadRowNums.lean: the errors of the row of the output head's own rounds, as one written
list.

rowNums q s sW: the list, over a field of q elements: the errors of the chain of the norm
(normNums, Cb/Pv/Head/Norm.lean); 6 for the batch of the seven row products; then the three lists of
the token sumchecks (TokKind.errs, Cb/Pv/Head/Tok.lean). All are counts of drawn elements; the first
member counts points of lt coordinates.

norm2_nums: the errors of the chain up to the first token sumcheck. row_nums: the errors with which
row_knowAt (Cb/Pv/Head/HeadRow.lean) is stated are rowNums.

What is not claimed. That the list is the plan's: Cb/Pv/Head/TestRow.lean
compares it with the written list of Cb/Pv/Head/Sizes.lean.


-/
import Cb.Pv.Head.HeadRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head
open Iop Prob TWhole Finset Inst.Model Tok

/-- The errors of the row, as counts of draws. -/
def rowNums (q : ℕ) (s : SqSize) (sW : ℕ) : List ℕ :=
  normNums q s ++ (6 :: (kindTV s.lt (sPvOf sW s)).errs) ++ (kN s.lt (sPvOf sW s)).errs ++
    (kH s.lt s.lPd (sPvOf sW s)).errs

section
variable {E : Type} [Field E] [Fintype E] {J P M Wp Kc : Type} [Fintype J] [DecidableEq J]
variable (np : NormPar) (limb : (J → E) → ℕ → ℕ → E) (dig : (J → E) → ℕ → ℕ → E)
variable (msk : ℕ → J) (sW : ℕ) (Ex : ExtSpec) (msg : M → J → E)
variable (Q0 : IOR.Rels Kc P Ex (M × Wp)) (s : SqSize)
variable (ztN ztH : P → Fin s.lt → E) (tabN tabH : P → (J → E) → Fin 2 → ℕ → E)
variable (join : P → E → E → (J → E) → Prop)

/-- The errors of the chain up to the first token sumcheck. -/
theorem norm2_nums :
    errList (norm2Err (P := P) (Kc := Kc) limb dig msk sW Ex s) =
      normNums (Fintype.card E) s ++ (6 :: (kindTV s.lt (sPvOf sW s)).errs) := by
  have h1 : errList (norm2Err (P := P) (Kc := Kc) limb dig msk sW Ex s) =
      errList (normErr (P := P) (Kc := Kc) limb (sqSlot msk sW) Ex s) ++
        errList (Err.app (Bat.batErr E ((Fin s.lt → E) × SqOut limb msk sW P s) 7 Ex)
          (tokErr (kindTV s.lt (sPvOf sW s)) (tvW limb dig msk sW P s).behind Ex)) :=
    errList_app _ _
  have h2 : errList (Err.app (Bat.batErr E ((Fin s.lt → E) × SqOut limb msk sW P s) 7 Ex)
      (tokErr (kindTV s.lt (sPvOf sW s)) (tvW limb dig msk sW P s).behind Ex)) =
      ((kindTV s.lt (sPvOf sW s)).np - 1) :: (kindTV s.lt (sPvOf sW s)).errs :=
    bt_nums (k := kindTV s.lt (sPvOf sW s)) (W := tvW limb dig msk sW P s) Ex
  rw [h1, h2, norm_nums]
  rfl

/-- **The errors of the row are the written list.** -/
theorem row_nums :
    errList
      (Err.app
        (Err.app (norm2Err (P := P) (Kc := Kc) limb dig msk sW Ex s)
          (tokErr (kN s.lt (sPvOf sW s))
            (rowSeat np limb dig msk sW Ex msg Q0 s ztN ztH tabN tabH join).seatN.world Ex))
        (tokErr (kH s.lt s.lPd (sPvOf sW s))
          (rowSeat np limb dig msk sW Ex msg Q0 s ztN ztH tabN tabH join).seatH.world Ex)) =
      rowNums (Fintype.card E) s sW := by
  rw [two_nums (rowSeat np limb dig msk sW Ex msg Q0 s ztN ztH tabN tabH join), norm2_nums]
  rfl

end

end Cb.Pv.Head

#print axioms Cb.Pv.Head.norm2_nums
#print axioms Cb.Pv.Head.row_nums
