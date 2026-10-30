-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoHeadLookTied.lean.
The stretches of OnBytes/Tie/Pv/Lookup/Ends/FoHeadLook.lean are those into which the walk of the
head's check is cut.

States:
  headMid1_eq, headMid2_eq: at the names under which Head.walk records the equation's constant,
    Fo.headMid1 and Fo.headMid2 are the routines Fo.hMid1 and Fo.hMid2 of
      OnBytes/Tie/Pv/Lookup/Ends/FoTiedH.lean.
So the chain of run equations into which a run of Head.walk is cut (Fo.h_walk_exact,
OnBytes/Tie/Pv/Lookup/Ends/FoTiedH.lean)
holds the five runs in a row of which Fo.head_look_total speaks; that the two statements meet to the
letter is tried by an example in OnBytes/Tie/Pv/Lookup/Test/FoHeadLookTest.lean, which draws two of
the conclusions.
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a run returns.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoHeadLook
import OnBytes.Tie.Pv.Lookup.Ends.FoTiedH

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Model.Head Cb.Fo

theorem headMid1_eq (R : Head.Run) :
    headMid1 R "the look-up's claims on mask entries" "the sum of squares" "the row ledger"
      "the stream times the reciprocal" = hMid1 R := rfl

theorem headMid2_eq (R : Head.Run) :
    headMid2 R "the look-up's join" "the acceptance policy" = hMid2 R := rfl

end Fo
