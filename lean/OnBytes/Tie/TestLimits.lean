-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/TestLimits.lean: tests of the list of limits that a description breaks.

Each test is evaluated when the file compiles. The descriptions are the library's own, from the
directory Fmt/: those of the two small test protocols, and small made-up chains. The tests show that each limit is noticed. The descriptions
that the program itself makes are tested in OnBytes/Tie/TestKeyOneTime.lean and TestNotCovered.lean.

The tests show what is so at these descriptions, and nothing beyond them.
-/
import OnBytes.Tie.Limits
import Fmt.M1TheirsSpec
import Fmt.M2Theirs
import Fmt.M3Items
import Fmt.M3Dec
import Fmt.ParamsRead
import Fmt.Rules5Fast
import Fmt.Rules8Known2
import Fmt.Rules8More

set_option autoImplicit false

namespace OnBytes.Tie

-- The two small test protocols are covered, at tiny and at full parameters.
#guard limitsOf Fmt.M1.Theirs.specTiny == [] && limitsOf Fmt.M1.Theirs.specFull == []
#guard limitsOf Fmt.M2.Theirs.specTiny == [] && limitsOf Fmt.M2.Theirs.specFull == []
-- These four are meant to open every tree that they send. The limits
-- would not notice an opening that was left out of a description by mistake; this test does.
#guard eachOnce Fmt.M1.Theirs.specTiny && eachOnce Fmt.M1.Theirs.specFull
#guard eachOnce Fmt.M2.Theirs.specTiny && eachOnce Fmt.M2.Theirs.specFull
-- The same chains with their random bytes given by the description are covered too.
#guard limitsOf { Fmt.M1.Theirs.specFull with rand := .given Fmt.zero32 } == []
#guard limitsOf { Fmt.M2.Theirs.specFull with rand := .given Fmt.zero32 } == []
-- A chain without random bytes breaks `noRandomBytes`.
#guard (limitsOf { Fmt.M1.Theirs.specFull with rand := .none }).contains .noRandomBytes
-- Two roots in one round break `severalRoots`.
#guard limitsOf Fmt.Toy8K2.specM == [.severalRoots]
-- A tree that is opened twice breaks `notOnce`.
#guard limitsOf Fmt.Toy8K2.specT == [.notOnce]
#guard !eachOnce Fmt.Toy8K2.specT
-- A tree that is taken over from outside the chain breaks `takenOver`.
#guard (limitsOf (Fmt.Toy8M.spec Fmt.Toy8M.good .inFile)).contains .takenOver
-- This description is not in order: its parameter bytes do not begin with its plan.
#guard limitsOf { Fmt.M1.Theirs.specTiny with params := ByteArray.empty } == [.notInOrder]

end OnBytes.Tie
