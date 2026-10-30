-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/K5Work.lean: k5Work (Johnson/AtFull/Rounds/K5.lean), WRITTEN OUT: the policy's
work at a round of the request's scope that draws field elements, off a public part's frame. One
equation, by definition: for whoever shows that work's value in its own words and wants it at
k5_row_spots' premise hw.

  k5Work_is   k5Work W = (OnBytes.Params.settingOf W.P.frame).workOf .field .request.
  k5Work_of   so a value of the right side is a value of k5Work.

Limits. Nothing is shown at any public files. Nothing on soundness.

-/
import Johnson.AtFull.Rounds.K5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Rounds
open OnBytes.Model

theorem k5Work_is (W : Verify.Public) :
    k5Work W = (OnBytes.Params.settingOf W.P.frame).workOf .field .request := rfl

theorem k5Work_of {W : Verify.Public} {w : Nat}
    (h : (OnBytes.Params.settingOf W.P.frame).workOf .field .request = w) : k5Work W = w := h

end Johnson.AtFull.Rounds

#print axioms Johnson.AtFull.Rounds.k5Work_is
#print axioms Johnson.AtFull.Rounds.k5Work_of
