-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/K4Nums.lean: the fifteen numbers that K4's table of rounds
(`OnBytes.Desc.First.K4.rounds`, OnBytes/Desc/First/K4/Rounds.lean) reads of the public values, and
their written values at the full size. Definitions alone, in a file of their own, so that a closed
fact on the makers and K4's row (Johnson/AtFull/Rounds/K4.lean) can both name them.

  `numsOf P hp`: the fifteen, of the layers' public values P and a group's plan hp.
  `numsW g`: their written values at the group g: read by a program off the two lists that the
    written table `listAt` (Johnson/AtFull/Rounds/ListAt.lean) bears at K4's places; it only
    proposes them.

Limits. Definitions alone: that any public values have these numbers is not said here.
Nothing on soundness.

-/
import OnBytes.Model.Layer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Rounds
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (nEndT)

/-- The fifteen numbers that K4's table of rounds reads of the layers' public values and of a
group's plan: lt, ls, lPd, xl, NI, lNI, muV, the number of end values of the second sumcheck over
the tokens, lamS, LamM, NCL, muH, ll, muH2, lk. -/
def numsOf (P : Layer.Pub) (hp : Layer.HPlan2) : List Nat :=
  [P.y.h.lt, P.y.ls, P.y.lPd, P.y.h.xl, P.y.NI, P.rd.lNI, P.rd.muV, nEndT P.y, hp.lamS, P.y.LamM,
    hp.NCL, P.rd.muH, P.y.h.ll, P.rd.muH2, P.wsLay.lk]

/-- The fifteen numbers at the full size, written; NCL is 33 in the first group, else 32. -/
def numsW (g : Nat) : List Nat :=
  [10, 6, 13, 5, 8, 3, 26, 266, 23, 2, if g == 0 then 33 else 32, 26, 2, 24, 18]

end Johnson.AtFull.Rounds
