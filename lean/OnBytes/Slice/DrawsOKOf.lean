-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/DrawsOKOf.lean: what the theorems on the written link ask of the draws of its five
rounds (`DrawsOK`, OnBytes/Slice/CorePeel.lean) follows from what the block on the batching asks of
the first six rounds (`BatDraws`, OnBytes/Slice/BlockBat.lean).

`DrawsOK` says, round by round, that the map from the round's typed values to the library's verifier
message is injective, and that positions have at most 64 bits. `BatDraws` says what each round sends
and draws; OnBytes/Slice/BatAt.lean gets it from the rounds' forms (`batDraws_of`). The files on one
setting proved `DrawsOK` by evaluation; this lemma is general.

Main theorem: `drawsOK_of`.
Not claimed. Nothing on any rounds. Nothing on soundness.

-/
import OnBytes.Slice.BatAt

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Run

/-- What `DrawsOK` asks of the link's five rounds follows from what they send and draw. -/
theorem drawsOK_of {S : Sz} {d1 d2 d3 d4 d5 dA : PQ.RD} (h : BatDraws S d1 d2 d3 d4 d5 dA) :
    DrawsOK S d1 d2 d3 d4 d5 where
  g1 := h.r1.gVec_inj
  g2 := gSeed_inj _ _ h.r2.plain h.r2.els h.r2.poss h.nz
  g3 := gUnit_inj _ h.r3.plain h.r3.els h.r3.poss
  g4 := h.r4.gLoc_inj
  g5 := h.r5.gVec_inj
  l1 := h.r1.logN
  l2 := h.r2.logN
  l3 := h.r3.logN
  l4 := h.r4.logN
  l5 := h.r5.logN

end OnBytes.Slice
