-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlToyPackNames.lean: bounds on list decoding and on mutual correlated agreement for codes
of length 8 at the radius 1, in the form in which test instances of a folding step cite them (not
all hypotheses are named here: see their statements).

For toys: what the toys of closings over the field with 101 elements cite of their five-point code,
over p = 2^64 - 2^32 + 1, under the same names.
Definitions and restatements.
Cb/Ld/LdRelToy7d4.lean: `C74`; Cb/Ld/LdSumPackToy.lean: `plc5`, `plc5_inj`, `list5`. Here (namespace
`Cb.Gl`) these names speak of the one code of Cb/GlVal/GlToyBase4.lean (eight points, dimension 4,
distance 5), as in Cb/GlVal/GlToyStdNames.lean.
The numbers differ, because the codes of those files are read at a radius not below half the
distance and this code is read within a third: distance 4 ↦ 5; radius 2 ↦ 1; lists of at most 2:
kept as a bound (there is at most one member); exceptional values on a line: 16 ↦ 2; hidden
positions of the fold's fresh mask: 1, kept as a bound (the code hides 3).

Main names:
  `toy_par_hyp`: `Y.Hyp 5 1 1 (2) (2) (2) (2)`, for parameters Y of a fold (`SumPar`) under the
    eleven hypotheses `hC` to `hzk` of its statement.
  `list74` (Cb/Ld/LdRelToy7d4.lean): `D.ListAt 1 3`, under `hL` (`D.Laws`) and `hD` (`D.Dist 4`).
    `toy_par_hyp74`: `Y.Hyp 4 1 3 (3) (29) (29) (29)`, under the eleven hypotheses `hC` to `hzk` of
    its statement: the radius is 1, where the seven-point code of Cb/Ld/LdRelToy7d4.lean is read at
    2; the other numbers hold as bounds.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyStdNames
import Cb.Ld.LdSumPackProofs
import Cb.Ld.LdGroupFoldProofs

set_option autoImplicit false

namespace Cb.Gl
open Iop Prob Hiop Blocks IOR Cb.Ood

/-- The code itself, under the name of that of Cb/Ld/LdRelToy7d4.lean. -/
abbrev C74 : Code.Enc F := C84

/-- Each column of the packing in its own coordinate of the mask code's message. -/
def plc5 (h g : ℕ) : PCol h g 1 → (toyLd (PCol h g 1)).J := fun c => toyPlace84 (PCol h g 1) c
theorem plc5_inj (h g : ℕ) : Function.Injective (plc5 h g) := (toyPlace84 (PCol h g 1)).injective

theorem list5 (D : LdCode E P5) (hL : D.Laws) (hD : D.Dist 5) : D.ListAt 1 2 := fun f =>
  le_trans (list84 D hL hD f) (by norm_num)

/-- The fold's hypotheses, for any parameters at the toy's eight positions. (not all hypotheses are
named here: see the statement below) -/
theorem toy_par_hyp (Y : SumPar E P5) (hC : Y.C.Laws) (hCD : Y.C.Dist 5) (hZ : Y.Z.Laws)
    (hZD : Y.Z.Dist 5) (hW : Y.Zw.Laws) (hWD : Y.Zw.Dist 5) (hn : 2 ≤ Y.n)
    (hv : Function.Injective Y.val) (hP : Y.PackOK) (hQ : Y.QwDeg) (hzk : Y.Zw.Zk 1) :
    Y.Hyp 5 1 1 (fun _ => 2) (fun _ => 2) (fun _ => 2) (fun _ => 2) :=
  { codes := ⟨⟨hC, hZ, hW⟩, ⟨hCD, hZD, hWD⟩, by norm_num⟩
    errs :=
      { list := fun j _ =>
          list5 _ (ld_laws_pair E P5 _ _ (ld_laws_il E P5 _ _ hC)
              (ld_laws_pair E P5 _ _ (ld_laws_il E P5 _ _ hZ) (ld_laws_il E P5 _ _ hW)))
          (ld_dist_pair E P5 _ _ 5 (ld_dist_il E P5 _ _ 5 hCD)
            (ld_dist_pair E P5 _ _ 5 (ld_dist_il E P5 _ _ 5 hZD) (ld_dist_il E P5 _ _ 5 hWD)))
        mcaC := fun j _ _ => mca84 _ (ld_laws_il E P5 _ _ hC) (ld_dist_il E P5 _ _ 5 hCD)
        mcaS := fun j _ _ => mca84 _ (ld_laws_il E P5 _ _ hZ) (ld_dist_il E P5 _ _ 5 hZD)
        mcaW := fun j _ _ => mca84 _ (ld_laws_il E P5 _ _ hW) (ld_dist_il E P5 _ _ 5 hWD) }
    inj := hv
    deg := hn
    pack := hP
    qw := hQ
    zk := ld_zk_il E P5 _ _ 1 hzk }

theorem list74 (D : LdCode E P74) (hL : D.Laws) (hD : D.Dist 4) : D.ListAt 1 3 := fun f =>
  le_trans (ld_list_unique E P84 D 4 1 hL hD (by norm_num) f) (by norm_num)

/-- The same under the names and bounds of the seven-point toys: distance at least 4, lists of at
most 3, at most 29 exceptional values, 3 hidden positions: all kept as bounds; the radius is 1
(there 2). (not all hypotheses are named here: see the statement below) -/
theorem toy_par_hyp74 (Y : SumPar E P74) (hC : Y.C.Laws) (hCD : Y.C.Dist 4) (hZ : Y.Z.Laws)
    (hZD : Y.Z.Dist 4) (hW : Y.Zw.Laws) (hWD : Y.Zw.Dist 4) (hn : 2 ≤ Y.n)
    (hv : Function.Injective Y.val) (hP : Y.PackOK) (hQ : Y.QwDeg) (hzk : Y.Zw.Zk 3) :
    Y.Hyp 4 1 3 (fun _ => 3) (fun _ => 29) (fun _ => 29) (fun _ => 29) :=
  { codes := ⟨⟨hC, hZ, hW⟩, ⟨hCD, hZD, hWD⟩, by norm_num⟩
    errs :=
      { list := fun j _ =>
          list74 _ (ld_laws_pair E P74 _ _ (ld_laws_il E P74 _ _ hC)
              (ld_laws_pair E P74 _ _ (ld_laws_il E P74 _ _ hZ) (ld_laws_il E P74 _ _ hW)))
          (ld_dist_pair E P74 _ _ 4 (ld_dist_il E P74 _ _ 4 hCD)
            (ld_dist_pair E P74 _ _ 4 (ld_dist_il E P74 _ _ 4 hZD) (ld_dist_il E P74 _ _ 4 hWD)))
        mcaC := fun j _ _ =>
          ld_mca_mono E P84 _ 1 2 29 (by norm_num)
            (ld_mca_third E P84 _ 4 1 (ld_laws_il E P74 _ _ hC)
              (ld_dist_il E P74 _ _ 4 hCD) (by norm_num))
        mcaS := fun j _ _ =>
          ld_mca_mono E P84 _ 1 2 29 (by norm_num)
            (ld_mca_third E P84 _ 4 1 (ld_laws_il E P74 _ _ hZ)
              (ld_dist_il E P74 _ _ 4 hZD) (by norm_num))
        mcaW := fun j _ _ =>
          ld_mca_mono E P84 _ 1 2 29 (by norm_num)
            (ld_mca_third E P84 _ 4 1 (ld_laws_il E P74 _ _ hW)
              (ld_dist_il E P74 _ _ 4 hWD) (by norm_num)) }
    inj := hv
    deg := hn
    pack := hP
    qw := hQ
    zk := ld_zk_il E P74 _ _ 3 hzk }

end Cb.Gl
