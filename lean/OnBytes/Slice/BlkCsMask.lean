-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkCsMask.lean: the rows of the program's code switch reach over the whole mask table.

The law on the batching of rows on a group's mask table (OnBytes/Iop/MaskLaws.lean) asks of each row
that every tensor that it has on a mask table has at least as many variables as the table's row bits
and the group's place bits together (`MaskFits`). This file shows it of the rows of a code switch
into a stage (OnBytes/Slice/BlkCsRows.lean). The carried claim and the main code's rows have no
tensor among their terms, which is where `MaskFits` looks. A mask code's row has one if its message
has a box, and that tensor has a variable for each index bit of the table that takes the rest.

Main theorems: `maskFits_carriedRow`, `maskFits_genMain`, `maskFits_genMask`.
Not claimed. Nothing on the sample row, which has its own law.
-/
import OnBytes.Iop.MaskLaws
import OnBytes.Slice.BlkCsPlain

set_option autoImplicit false

namespace OnBytes.Slice

/-- A row without terms meets `MaskFits`. -/
theorem maskFits_of_empty (S : Statement) (L : GroupLayout) (r : Row) (h : r.terms = #[]) :
    MaskFits S L r := by
  intro t ht
  rw [h] at ht
  exact absurd ht List.not_mem_nil

/-- The carried claim has no tensor among its terms, so it meets `MaskFits`. -/
theorem maskFits_carriedRow (S : Statement) (L : GroupLayout) (W : SwitchFrame)
    (old : SingleRows) : MaskFits S L (carriedRow W old) :=
  maskFits_of_empty S L _ ((terms_restE _ _ _ _ _).trans (terms_restE _ _ _ _ _))

/-- The row of the old main code's generator has no tensor among its terms, so it meets
`MaskFits`. -/
theorem maskFits_genMain (S : Statement) (L : GroupLayout) (W : SwitchFrame) (x : ℕ) (t : E) :
    MaskFits S L (genMain W x t) :=
  maskFits_of_empty S L _ (terms_restF _ _ _ _ _)

/-- A tensor on a box has a variable for each index bit of the table, at least. -/
theorem le_vars_switchOnBox (b : SwitchBox) (v : Tensor) (vars tableBits : ℕ)
    (hv : v.vars = vars) : tableBits ≤ (switchOnBox b v vars tableBits).vars := by
  have h1 : (v.insertChoice 0 b.shift (b.start % 2 ^ b.shift)).vars = vars + b.shift := by
    rw [Tensor.vars_insertChoice v 0 _ _ (Nat.zero_le _), hv]
  show tableBits ≤ ((v.insertChoice 0 b.shift (b.start % 2 ^ b.shift)).insertChoice
    (b.shift + vars) (tableBits - b.shift - vars) (b.start / 2 ^ (b.shift + vars))).vars
  rw [Tensor.vars_insertChoice _ _ _ _ (by rw [h1]; omega), h1]
  omega

/-- The row of the old mask code's generator meets `MaskFits`: its tensor, if it has one, reaches
over the table that takes the rest. hS: that table's index bits are at least the new oracle
message's mask row bits and the group's place bits together. -/
theorem maskFits_genMask (S : Statement) (L : GroupLayout) {W : SwitchFrame} (hW : FrameOK W)
    (hS : S.rowBits W.g .mask + L.logEllZk ≤ W.restBits) (x j : ℕ) (t : E) :
    MaskFits S L (genMask W x j t) := by
  unfold genMask
  cases hb : W.box.getD j none with
  | none =>
    exact maskFits_of_empty S L _ ((terms_restF _ _ _ _ _).trans (terms_restF _ _ _ _ _))
  | some b =>
    intro u hu _
    have e : (switchAddRestF (({} : Row).add W.g W.restPart (switchOnBox b
        (messageTensor W.zk (shortPosition W.zk.logN x)) W.zk.logEll W.restBits)) W.g W.restPart
        (W.maskTail.getD j []) (generatorTail W.zk (shortPosition W.zk.logN x))).terms
        = #[⟨W.g, W.restPart, switchOnBox b (messageTensor W.zk (shortPosition W.zk.logN x))
          W.zk.logEll W.restBits⟩] := terms_restF _ _ _ _ _
    have hu' : u ∈ (#[⟨W.g, W.restPart, switchOnBox b
        (messageTensor W.zk (shortPosition W.zk.logN x)) W.zk.logEll W.restBits⟩]
        : Array Term).toList := e ▸ hu
    rw [List.mem_singleton.1 hu']
    exact Nat.le_trans hS (le_vars_switchOnBox b _ _ _
      (vars_messageTensor W.zk _ (hW.box j b hb).2))

end OnBytes.Slice

#print axioms OnBytes.Slice.maskFits_of_empty
#print axioms OnBytes.Slice.maskFits_carriedRow
#print axioms OnBytes.Slice.maskFits_genMain
#print axioms OnBytes.Slice.le_vars_switchOnBox
#print axioms OnBytes.Slice.maskFits_genMask
