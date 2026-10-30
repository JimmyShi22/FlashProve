-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/OpenedAtTruth.lean: Law/OpenedAll.lean's opened_all AS OpenedAt (Law/RowAtDecide.lean), at letters g : Given: the tie that
OpenedAll.lean's head speaks of, checked by Lean. What it is not: at OpenedAll.lean's head: no tape and no honest cells
are shown to exist.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.OpenedAll
import Johnson.Desc.Kinds.Law.RowAtDecide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE)
open OnBytes.Model (Fork)
open Norm (lt ls d lPd T S2)

/-- **OpenedAt, at the truth.** -/
theorem openedAt_truth (g : Given) (H : HeardAll) (G : Fork) (c : NCells) (mask : Nat → E)
    (hreq : Request.ok = true) (hy : y < V) (hw : WeightsOk) (hzt : (FinalNorm.zt).size = lt)
    (hls : ls ≤ lPd) (hdS : S2 ∣ d)
    (hblock : ∀ x, x < d →
      FinalNorm.ew .remLow x = FinalNorm.ewh .remLow (x / S2) * eq FinalNorm.zl (x % S2)) :
    let _ : Norm.Heard := H.1
    let _ : FinalNorm.Heard := H.2.1
    let _ : Heard := H.2.2
    let _ : FinalNorm.Reads := normReadsAtCells c
    let _ : Reads := readsAt c.toCells
    (Norm.pV).size = lt → Norm.squares.r.size = lPd + lt → Norm.products.r.size = lt →
    FinalNorm.normed.r.size = lt →
    (dataOf c).Holds → HonestHead c.toCells →
    NormTruthW (worldE G mask noEnt) c → okE (Norm.P.getD 6 {}).var.const = true →
    HeadTruth c.toCells G mask noEnt →
    OpenedAt g H G c mask :=
  opened_all H G c mask hreq hy hw hzt hls hdS hblock

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.openedAt_truth
