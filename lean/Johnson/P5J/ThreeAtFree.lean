-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ThreeAtFree.lean: `h.Three h.free` FROM WHAT IS LEFT OF IT. One theorem.

`AtMgA.three_of_left` (Johnson/P5J/ThreeLeftAtAll.lean) gives `h.Three 𝔏`, for every 𝔏, from what is
left of it and five premises on 𝔏: hk, q₁, q₂, q₃ and hsp.
At the value `h.free` (Johnson/P5J/FreeAll.lean: the tower's letters laid at the tables' constants)
all five have payers:

  hk: `freeOf_hk` (Johnson/P5J/FreeShared.lean), under the test `H2K.Sizes.AtFull` on the made
    sizes, which `H2K.Sizes.atFull_of_pubPlain` (Johnson/Loose/H2K12/AtFullPlain.lean) has from the
    head.
  q₁ · q₂ · q₃: `AtMgA.free_q₁` | `free_q₂` | `free_q₃`. hsp: `AtMgA.free_split`.

  **`three_at_free`**: h.ThreeLeft h.free → h.Three h.free. No other premise.

Read against Johnson/P5J/FreeAll.lean, Johnson/P5J/FreeAt.lean and Johnson/P5J/FreeShared.lean,
which may still turn.
Limits. A joining: it pays no field by itself. No member of `h.ThreeLeft h.free` is known.
At the second hash function `OnBytes.secondHashFunction` alone. No soundness follows from it. Nothing on hiding.

-/
import Johnson.P5J.ThreeLeftAtAll
import Johnson.P5J.FreeAll
import Johnson.Loose.H2K12.AtFullPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **`h.Three h.free` from what is left of it**: the five premises on 𝔏 are paid at the value. -/
theorem three_at_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (V : h.ThreeLeft h.free) :
    h.Three h.free :=
  h.three_of_left h.free
    (freeOf_hk h.toAtMg h.𝔇 _ _ _ _ _ _ _ (H2K.Sizes.atFull_of_pubPlain h.scope h.laid.pub))
    h.free_q₁ h.free_q₂ h.free_q₃ h.free_split V

end P5J

#print axioms P5J.three_at_free
