-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegFFCellKeys.lean: the key families of the feed-forward segment with products of cells
and no weight (N1, N2, XR, DD, MR) have `KeyOK` over p = 2^64 - 2^32 + 1.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean).

`quadKey_ok`: for one of the five (`isQuad s`), the family `quadKeyFam g tb s`
(Cm/SegFFCellKeys.lean, for any field E over `Cb.Gl.F`) has `KeyOK` (Cm/TargetSegFF.lean): for all
matrices A, index matrices W and every set S that holds the padding value of the table, all its
values on its cube are in S if and only if all keys of s (Inst/Model/FF/Trace.lean, over E, at the
trace `tA g A` and the weights `wOf g W`) are; it is well formed; it reads only places of valid
cells that the segment reads, own or borrowed (`IsFF`).

What each family is: the head of Cm/SegFFCellKeys.lean.
Limits: what is not said of the segment's families: Cm/TargetSegFFAll.lean, the head, Limits.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegFFCellKeys
import Cm.TargetSegAll
import Cm.TargetSegFF
import Cm.TargetSegFFAffPass


set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Inst.Model Inst.Model.All Finset

variable [scl : Scl]

/-- The five families have what the theorems on `ffSpec` require (`KeyOK`, Cm/TargetSegFF.lean). -/
theorem quadKey_ok {X E : Type} [Field E] [Algebra Cb.Gl.F E] (Φ : IdxFmt Cb.Gl.F) (g : ℕ)
    (tb : Tables) {s : FFSeg.Fam} (hs : isQuad s = true) :
    KeyOK Φ g tb s (quadKeyFam (X := X) (E := E) g tb s) where
  iff := fun x₀ W A S hS => quadKey_iff g tb Φ x₀ W A (4 * g) (wOf g W) hs S hS
  wf := quadKey_wf g tb Φ s
  places := quadKey_places g tb s

end Cm.Seg.TS
