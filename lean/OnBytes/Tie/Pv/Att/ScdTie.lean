-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/ScdTie.lean: the numbers of the block of Cb/Pv/Att/Scd.lean are those of the
port's own functions.

Main names:
  `scd_degs_plan`: the entries of (Params.attentionScd lt lgk pairs Lam).degree, each less 1, are
    the degrees of the block's rounds. `scd_degY_plan`: its degreeY is the degree in the further
    variable. `scd_values_plan`: the block shows as many end values as that record says.
    `scd_withY_plan`: the record has the further variable.
  `scd_nums_plan`: so the block's errors, as a list of counts, are: 1; each entry of that degree
    less 1; degreeY; 0. These are the numbers that Params.planPsc hands to fieldError and
    fieldErrorNonzero, round by round; the last round (PSC values) has no error there.
  `ofShape`: the sizes of a shape. `scd_degrees_shape`: the degrees of the block's rounds are
    Attention.Shape.scdDegrees. `scd_pairs_shape`: the pairs are Attention.Shape.NP.

Limits: numbers alone. Nothing on the order of the variables, on which coefficient is left out, or
on what the port computes.
-/
import Cb.Pv.Att.ScdProofs
import OnBytes.Params.SubRounds
import OnBytes.Model.AttentionShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open Iop Prob Cb TWhole Cb.Pv.Att

theorem scd_degs_plan (s : ScdSize) :
    (OnBytes.Params.attentionScd s.lt s.lgk s.pairs s.Lam).degree.map (· - 1) =
      List.ofFn s.deg := by
  rw [s.ofFn_deg]
  simp [OnBytes.Params.attentionScd]

theorem scd_degY_plan (s : ScdSize) :
    (OnBytes.Params.attentionScd s.lt s.lgk s.pairs s.Lam).degreeY = s.lt + 1 := rfl

theorem scd_withY_plan (s : ScdSize) :
    (OnBytes.Params.attentionScd s.lt s.lgk s.pairs s.Lam).withY = true := rfl

theorem scd_values_plan (s : ScdSize) :
    (OnBytes.Params.attentionScd s.lt s.lgk s.pairs s.Lam).values = Fintype.card s.A := by
  simp [OnBytes.Params.attentionScd, ScdSize.A]

variable {E : Type} [Field E] [Fintype E] {s : ScdSize} (T : Scd E s)

theorem scd_nums_plan (n : ℕ) {X : Type} (cl : X → (Fin n → E) → E × T.St) (Ex : ExtSpec) :
    errList (scdE T n cl Ex) =
    1 :: ((OnBytes.Params.attentionScd s.lt s.lgk s.pairs s.Lam).degree.map (· - 1) ++
      [(OnBytes.Params.attentionScd s.lt s.lgk s.pairs s.Lam).degreeY] ++ [0]) := by
  rw [scd_nums, scd_degs_plan, s.ofFn_deg, scd_degY_plan]

/-- the sizes of a shape -/
def ofShape (S : OnBytes.Attention.Shape) : ScdSize := ⟨S.cf.lt, S.cf.lgk, S.Lam, S.HA⟩

theorem scd_degrees_shape (S : OnBytes.Attention.Shape) :
    List.ofFn (ofShape S).deg = S.scdDegrees := (ofShape S).ofFn_deg

theorem scd_pairs_shape (S : OnBytes.Attention.Shape) : (ofShape S).pairs = S.NP := rfl

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.scd_degs_plan
#print axioms OnBytes.Tie.Pv.Att.scd_values_plan
#print axioms OnBytes.Tie.Pv.Att.scd_nums_plan
#print axioms OnBytes.Tie.Pv.Att.scd_degrees_shape
