-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkTieFold.lean: the tie on columns goes through a fold.

OnBytes/Slice/BlkTies.lean writes down what ties the columns that a later block of the program reads
to the oracle messages that were sent, before a fold (`GroupTie`) and after it (`SingleTie`). This
file shows that a run of the program's fold leads from the first to the second
(OnBytes/Slice/BlkJointFold.lean: `FoldTies`). The fold sends no oracle message and reads no column.
It marks the fresh mask as spent, which changes no shape. What the tie after the fold says of the
three folded rows is read off the fold's output (OnBytes/Slice/BlkFoldOut.lean).

Main theorems.
 `spend_shapesKeep`   marking an oracle message as spent keeps all shapes
                      (OnBytes/Slice/BaseOpen.lean: `shape_after_spend`, for all at once).
 `foldTies_at`        `FoldTies` from `GroupTie` to `SingleTie`.

Not claimed. Nothing on the claim after the fold: see OnBytes/Slice/BlkJointFold.lean.
-/
import OnBytes.Slice.BaseOpen
import OnBytes.Slice.BlkFoldOut
import OnBytes.Slice.BlkJointFold
import OnBytes.Slice.BlkTies

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run
open Params (IoppStage)

/-- Marking an oracle message as spent keeps all shapes. -/
theorem spend_shapesKeep (o : Nat) (c c1 : Ctx) (h : (Blk.spendAsMask o).Yields c () c1) :
    ShapesKeep c.st c1.st :=
  fun i x hx => shape_after_spend o i c c1 x h hx

/-- The tie on columns goes through a fold at the stage s, before a switch to the stage s'. The
four hypotheses on codes are public. -/
theorem foldTies_at (K : Codes) (s s' : Sg) (cur : IoppStage) (hK : StageCodes s cur K)
    (nc nz n : Nat) (shapes : List OracleShape) (mainFirst maskFirst : Array (Option Nat))
    (pt : Fin (s.h + s.g) → GE) (rest : List Fmt.RoundView)
    (hzk : (K.mask[cur.maskCode]?).map codeOf = some s.Z)
    (hc' : (K.base[nc]?).map codeOf = some s'.C) (hz' : (K.mask[nz]?).map codeOf = some s'.Z)
    (hsmall : s.C.a ≤ 32) :
    FoldTies K s cur pt rest (GroupTie s n shapes mainFirst maskFirst)
      (SingleTie s s' K nc nz n shapes mainFirst maskFirst pt) := by
  intro c c1 c' row L o eps claim gamma ht hcK hpl hsp hran hpt hlen hshape hrow
  obtain ⟨ms, hlay, hseat⟩ := ht.seat
  have e1 := Blk.spendAsMask_inv o c c1 hsp
  have hc1 : c1.st.codes = K := by rw [e1]; exact hcK
  obtain ⟨hhk, hcol⟩ := of_foldShapeOk c.st (ioppFoldShape cur L) hshape
  have hkept : ∀ i, i < (ioppFoldShape cur L).layout.members.size →
      (ioppFoldShape cur L).layout.kept.getD i false = false := by
    intro i hi
    refine hlay.kept i ?_
    have hm : (ioppFoldShape cur L).layout.members = ms.toArray := hlay.members
    rw [hm] at hi
    exact hi
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ :=
    foldOutput_ok c1.st (ioppFoldShape cur L) row o eps gamma claim (hlen.trans hK.k.symm) hrow hhk
      (by rw [hc1, ← hcK]; exact hcol) hpl ht.noKept hkept
  obtain ⟨cd, hcd, hC⟩ := hK.base
  have ez : (c1.st.codes.mask.getD cur.maskCode default).ell = s.Z.l := by
    rw [hc1]
    exact congrArg (·.l) hK.mask
  have ec : (c1.st.codes.base.getD cur.code default).ell = s.C.l := by
    rw [hc1, Array.getD_eq_getD_getElem?, hcd]
    exact congrArg (·.l) hC
  have hcode : (K.base[cur.code]?).map codeOf = some s.C := by
    rw [hcd]
    exact congrArg some hC
  refine ⟨⟨⟨hcode, hzk, hc', hz', o2, rfl, o3, hsmall⟩, o1, o4.trans ez, o5.trans ez,
    fun v hv => (o6 v hv).trans (congrArg ceilLog2 ec), o7⟩, hK.k, hK.h, hpt, ms,
    ⟨hlay.members, hlay.kept, hlay.mainFirst, hlay.maskFirst⟩, ?_⟩
  refine hseat.keeps (BookKeeps.of_eq ?_) ?_
  · rw [hran.book, e1]
  · rw [hran.st]
    exact spend_shapesKeep o c c1 hsp

end OnBytes.Slice

#print axioms OnBytes.Slice.spend_shapesKeep
#print axioms OnBytes.Slice.foldTies_at
