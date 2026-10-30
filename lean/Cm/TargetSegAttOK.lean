-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegAttOK.lean: the attention segments of the model over p = 2^64 - 2^32 + 1 have what
`segsOK_of` requires of them (`AttOK`, Cm/TargetSegModelOf.lean), for every table of scales.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean).

`keyVec_agree_spec` and `idnVal_agree_spec` are Cm/SegAttOK.lean's.
The fields are `Cb.Gl.F`, `Cb.Gl.E` (Cb/Gl/GlField.lean);
the format is `Cm.Seg.TS.fmtRef`
(Cm/TargetSegAll.lean); `castW` is `Cm.TP.castW Cb.Gl.p`
(an integer index matrix, read modulo p: Cm/TargetPRel.lean).

`AttOK s att`: for g < `nGr` the segment att g has the shape of the layout (Cm/SegLayout.lean), is
well formed, reads places that the layout says it reads, and its conditions hold (at `fmtRef`, for
every request x, at the image of every integer index matrix W) at the matrices of a trace T if and
only if the clauses `AttAt` (Cm/TargetSegAll.lean) hold at T, and at integer matrices M if and only
if they hold at the trace of M. Used for the segments of the model (`segM`, Cm/TargetSegModel.lean;
`segs_ok`, Cm/TargetSegModelProofs.lean).

Main names:
  `attM s g`: the attention segment of group g (`attSpec`, Cm/TargetSegAtt.lean) at the words
    (`LayerScale`) of the table s: the shift of the exponential's key and the number of its live
    rows are those of the group's first layer.
  `attOK`: `AttOK s (attM s)`.

Limits: what is not said of the segments' clauses:
Cm/TargetSegAll.lean, the head, Limits.



Terms: lean/GLOSSARY.md.
-/
import Cm.SegAttOK
import Cm.TargetSegAll
import Cm.TargetSegAtt
import Cm.TargetSegModelOf
import Cm.TargetSegLayoutPlain
import Cm.TargetSegIdxModel
import Cm.TargetSegLayoutPlainProofs
import Cm.TargetSegIdxModelProofs
import Cm.TargetSegFFAllProofs
import Cm.TargetSegFFAll
import Cm.TargetSegFFMat
import Cm.TargetSegFF
import Cm.TargetSegFFAffPass
import Cm.TargetSegFFCellKeys
import Cm.TargetSegFFCellIdnOK
import Cm.TargetSegFFMatProofsE
import Cm.TargetSegFFMatProofsA
import Cm.TargetSegFFMatProofs
import Cm.TargetSegFFMatProofsC
import Cm.TargetSegFFMatProofsB
import Cm.TargetSegFFMatProofsD
import Cm.TargetSegHeadAsm
import Cm.TargetSegHeadProofs
import Cm.TargetSegHead
noncomputable section -- Lean tags what it cannot compile


set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Code Inst.Model Inst.Model.All

/-- The attention segment of group g at the table s of scales. -/
def attM (s : Scales) (g : ℕ) : SegSpec XI Cb.Gl.F Cb.Gl.E :=
  attSpec (scl := SFK s.kap s.nf g) g (s.kap (4 * g)).expRows.toNat tbRef

theorem attOK (s : Scales) : AttOK s (attM s) where
  rows := fun g _ => by
    show 18 = rowsLog (2 * g + 1)
    unfold rowsLog
    rw [if_pos (by omega)]
  cols := fun g hg => by
    have hg' : g < 12 := hg
    show colsAtt = cols (2 * g + 1)
    unfold cols
    rw [if_neg (by omega), if_pos (by omega)]
  wf := fun g _ => attSpec_wf (scl := SFK s.kap s.nf g) fmtRef
  places := fun g hg => attSpec_reads (scl := SFK s.kap s.nf g) fmtRef Hd.plain hg
  toM := fun g hg x T W =>
    attSpec_iff_toMat fmtRef keyVec_agree_spec idnVal_agree_spec s.kap s.nf Hd.plain
      lay_figures.2.2.2.2.2 hg x T (TP.castW Cb.Gl.p W)
  ofM := fun g hg x M W =>
    attSpec_iff_ofMat fmtRef keyVec_agree_spec idnVal_agree_spec s.kap s.nf Hd.plain hg
      x M (TP.castW Cb.Gl.p W)

end Cm.Seg.TS
