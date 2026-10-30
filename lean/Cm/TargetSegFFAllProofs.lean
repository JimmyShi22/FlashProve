-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegFFAllProofs.lean: the proofs of the statements of Cm/TargetSegFFAll.lean (the
feed-forward segment of a group with all its families), over p = 2^64 - 2^32 + 1: `kfAll_ok`,
`ffSeg_toMat`, `ffSeg_ofMat`, `ffSeg_wf`, `ffSeg_reads`.

They follow from the three groups of key families, the identities, and the theorems on `ffSpec` of
Cm/TargetSegFF.lean.





The statements and their limits: Cm/TargetSegFFAll.lean, the head, Limits.
-/
import Cm.SegFFMat
import Cm.SegFFCellKeys
import Cm.SegFFCellIdnOK
import Cm.SegFFMatProofsE
import Cm.TargetSegAll
import Cm.TargetSegFFAll
import Cm.TargetSegFFMat
import Cm.TargetSegIdxModelProofs
import Cm.TargetSegIdxModel
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

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Code Inst.Model Inst.Model.All

theorem kfAll_ok : Spec.kfAll_ok := by
  intro _ X g tb s hg
  unfold kfAll
  by_cases h1 : isAff s = true
  · rw [if_pos h1]
    exact affKey_ok fmtRef g tb h1
  · rw [if_neg h1]
    by_cases h2 : isQuad s = true
    · rw [if_pos h2]
      exact quadKey_ok fmtRef g tb h2
    · rw [if_neg h2]
      refine matKey_ok X g tb s hg ?_
      cases s <;> first
        | rfl
        | exact absurd rfl h1
        | exact absurd rfl h2

theorem ffSeg_toMat : Spec.ffSeg_toMat := fun X κ nf h g tok hh hg x₀ T Wi =>
  ffSpec_iff_toMat κ nf h hh hg (fun s => @kfAll_ok (SFK κ nf g) X g tbRef s hg)
    (idn_ok (scl := SFK κ nf g) g tok) x₀ T Wi

theorem ffSeg_ofMat : Spec.ffSeg_ofMat := fun X κ nf h g tok hg x₀ M Wi =>
  ffSpec_iff_ofMat κ nf h hg (fun s => @kfAll_ok (SFK κ nf g) X g tbRef s hg)
    (idn_ok (scl := SFK κ nf g) g tok) x₀ M Wi

theorem ffSeg_wf : Spec.ffSeg_wf := fun X κ nf g tok hg =>
  ffSpec_wf (scl := SFK κ nf g)
    (fun s => @kfAll_ok (SFK κ nf g) X g tbRef s hg) (idn_ok (scl := SFK κ nf g) g tok)

theorem ffSeg_reads : Spec.ffSeg_reads := fun X κ nf h g tok hg =>
  ffSpec_reads κ nf h hg (fun s => @kfAll_ok (SFK κ nf g) X g tbRef s hg)
    (idn_ok (scl := SFK κ nf g) g tok)

end Cm.Seg.TS
