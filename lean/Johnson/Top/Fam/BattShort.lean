-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fam/BattShort.lean: one kind of block as a family of a written proof file.

A definition, a statement and its proof, which is a call of the kind's own file. It imports that
file and Johnson/E/KObj/PFile.lean alone.

Main names:
  `KObj.KBattShortF`, `KObj.KBattShortF_good`: the batching of tensor rows with short messages
    (Johnson/Top/H/BattShort.lean), at every caller that meets `BattOK`.
Limits: those of that file. Nothing is said of any caller.
-/
import Johnson.E.KObj.PFile
import Johnson.Top.H.BattShort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob Hiop IOR Cb VerifiableInference.OnPublicFiles

/-- the batching of tensor rows with short messages, whoever calls it -/
noncomputable def KBattShortF : KFam.{1} where
  ι := BattCaller Cb.Gl.E
  mem := fun c => BattOK [c]
  src := fun c => (kBattShort [c]).toKind.src c
  dst := fun c => (kBattShort [c]).toKind.dst c
  blk := fun c => (kBattShort [c]).toKind.block c

theorem KBattShortF_good : KBattShortF.Good := fun c hc =>
  kBattShort_good [c] hc c (List.mem_singleton.2 rfl)

#print axioms KObj.KBattShortF_good

end KObj
