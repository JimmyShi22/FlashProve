-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/SlotsWhole.lean: every entry of a member's whole mask table lies inside the
member's ranges, said of the member's shape alone. One theorem with its proof.

`inMsg_whole_table`: for a member x with 2 ^ k mask rows whose mask rows' messages have a length
that is a power of two: for every j below 2 ^ (k + logEll) the position `posMask k j` lies inside
x's ranges (`InMsg`, Johnson/Desc/Sound/World.lean). It is `index_in_msg` (IndexRow.lean) without
a verifier's state: there the two numbers are read off a statement, here they are written out.
By `slots_quick` and `inMsg_of_slots` (SlotsIn.lean).

Limits. That 2 ^ (k + logEll) is the size of the mask table of a message of x's shape is
`mask_size_of_shape` (IndexRow.lean), not repeated here. Nothing on soundness.
-/
import Johnson.Top.H0.MergeLaw.SlotsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes (Codes)
open VerifiableInference.Desc.Sound (Mem InMsg)

/-- **Every entry of the whole mask table lies inside the member's ranges.** -/
theorem inMsg_whole_table (cs : Codes) (x : Mem) (k : ℕ)
    (hp : (x.1.l.get x.2).1.maskRows = 2 ^ k)
    (hl : (Johnson.Pack.pMask cs (x.1.l.get x.2).1).ell =
      2 ^ (Johnson.Pack.pMask cs (x.1.l.get x.2).1).logEll) :
    ∀ j, j < 2 ^ (k + (Johnson.Pack.pMask cs (x.1.l.get x.2).1).logEll) →
      InMsg cs (x.1.l.get x.2).1 (posMask k j).1 (posMask k j).2.1 (posMask k j).2.2 :=
  inMsg_of_slots cs x _ k (slots_quick (le_of_eq hp.symm) (by
    show _ ≤ 2 ^ k * (Johnson.Pack.pMask cs (x.1.l.get x.2).1).ell
    rw [hl, ← pow_add]))

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.inMsg_whole_table
