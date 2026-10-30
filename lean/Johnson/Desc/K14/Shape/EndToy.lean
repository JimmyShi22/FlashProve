-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Shape/EndToy.lean: evaluations of the shape behind "SPLIT"
(Johnson/Desc/K14/Shape/End.lean: endAt) at three written plans, and against a run of the verifier's
own text. #guard lines; no theorem.

What is evaluated:
  atKey, atReal, Toy.P   the plans: the written sizes of a key of full size; the written sizes over
                      a proof file's own codes (Johnson/Desc/K14/Honest/YesAt.lean names both); the
                      small written example (Johnson/Desc/K14/Honest/Toy.lean)
  fronts              AT EACH OF THE THREE: all nineteen clauses of the library's own frontL pass,
                      at o_u's group with the first mask and at o_omega's group with no mask; and
                      the test factsB at 9 passes
  Toy.run             AGAINST A RUN: the small example's run of the eight sub-protocols' own decide
                      functions returns, and the shape of the state behind it IS the closed form, at
                      two lists of challenges; the closed form one border earlier is another shape
  endOf atKey         what stands there at the key's written sizes, written out: the groups'
                      members, marks kept and numbers of constraints; each message's marks; the
                      trees' parts; the count of roots
  NEGATIVE TESTS      the clauses can fail: o_omega's group in front of the joinings; a member as
                      the mask; a group that is not there; a sampled message as the mask. Fourteen
                      of the nineteen clauses have no negative test here

HOW MUCH THIS SAYS. The lines that begin with `#guard` are tests, checked by evaluation: Lean's
evaluator runs each of them when the file is compiled, and the build fails if one is false. The
kernel does not check them, and they prove nothing. So «all nineteen pass» joins no law of Lean's.
frontAt is evaluated AT THE STATE THAT lift MAKES OF THE SHAPE, not at a run's own state; that
frontL says the same at every state of that shape is End.lean's front_of_shape, UNDER A PREMISE
(FrontReads) that is shown in no file that this file stands over. AT o_omega's GROUP IT IS THE SHAPE
AT THE BORDER 9: the proximity test on o_u's group stands between that border and the front of the
test on o_omega's group. The nineteen clauses are a part of what a proximity test asks of the
structure in front of it; the whole is not evaluated here, and no file that this file stands over
writes it as a term. WHAT GOES OUT WITH o_u is written (withU P.S).getD #[] in these lines: the
empty array where withU returns nothing; no line asks that withU returns at the three plans.

What is not claimed. Nothing on soundness, on completeness or on hiding.
-/
import Johnson.Desc.K14.Shape.End
import Johnson.Desc.K14.Honest.YesAt
import Johnson.Desc.K14.Honest.Toy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Shape.EndToy
open OnBytes OnBytes.Params OnBytes.Params.Prices OnBytes.Plan Johnson.G
open VerifiableInference.Desc.K1 (realSized)
open Lk6.AtPlan (keyFull)
open Desc.K14.Honest (keyW)

/-- The shape behind "SPLIT" at a plan, at what the plan lets go out with o_u (the empty array where
withU returns nothing) and at a key of the plan's sizes. -/
def endOf (P : P14) : Sh2 := endAt P ((withU P.S).getD #[]) (keyW P.par.S.fold.index)

/-- All nineteen clauses of the front of the test on o_u's group, with the first mask; and of the
front of a test on o_omega's group, with no mask: both AT THE SHAPE BEHIND "SPLIT". -/
def fronts (P : P14) : Bool :=
  frontAt (endOf P) (endOf P).lin.gU (endOf P).lin.firstMask &&
    frontAt (endOf P) (endOf P).lin.gOmega none

/-- The written sizes of a key of full size. -/
def atKey : P14 := ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, 0, [(0, 0)]⟩

/-- The written sizes over a proof file's own codes; nothing where the library's realSized is
nothing (a line below asks that it is something). -/
def atReal : Option P14 :=
  realSized.map fun x => ⟨recordSet, .shared, x.2, x.1.shape, 0, [(0, 0)]⟩

#guard fronts atKey
#guard factsB atKey 9 (endOf atKey)
#guard atReal.isSome
#guard (atReal.map fronts) == some true
#guard (atReal.map fun P => factsB P 9 (endOf P)) == some true
#guard fronts Desc.K14.Honest.Toy.P
#guard factsB Desc.K14.Honest.Toy.P 9 (endOf Desc.K14.Honest.Toy.P)

-- AGAINST A RUN OF THE VERIFIER's OWN TEXT: the small example's run of the eight sub-protocols'
-- decide functions returns, and the shape of the state behind it IS the closed form
#guard ((Desc.K14.Honest.Toy.run {} (Desc.K14.Honest.Toy.chal 0)).toOption.map sh2) ==
  some (endOf Desc.K14.Honest.Toy.P)
-- with other challenges too: at these two lists the shape behind is the same
#guard ((Desc.K14.Honest.Toy.run {} (Desc.K14.Honest.Toy.chal 5)).toOption.map sh2) ==
  some (endOf Desc.K14.Honest.Toy.P)
-- and the closed form one border earlier is another shape
#guard ((Desc.K14.Honest.Toy.run {} (Desc.K14.Honest.Toy.chal 0)).toOption.map sh2) !=
  some (upTo Desc.K14.Honest.Toy.P ((withU Desc.K14.Honest.Toy.P.S).getD #[]) 8
    (sh2 (first Desc.K14.Honest.Toy.P.codes (keyW Desc.K14.Honest.Toy.P.par.S.fold.index))))

-- what stands there, at the key's written sizes
#guard ((endOf atKey).lin.gU, (endOf atKey).lin.gOmega, (endOf atKey).lin.firstMask) ==
  (0, 1, some 1)
#guard ((endOf atKey).core.st.groups.map fun G => (G.members, G.kept, G.kinds.length, G.inRun)) ==
  [([0, 3], [false, false], 64, false), ([2, 3], [false, false], 1, false)]
#guard ((endOf atKey).core.st.oracles.map fun x =>
    (x.sampled, x.rows, x.shape.answers, x.groups)) ==
  [(true, 1, 1, [0]), (false, 0, 0, []), (true, 1, 1, [1]), (true, 1, 1, [1, 0])]
#guard ((endOf atKey).core.book.trees.map fun t => (t.parts, t.oneList, t.lists)) ==
  [([0, 1], true, 0), ([2], false, 0), ([3], false, 0)]
#guard (endOf atKey).core.roots == 3

-- NEGATIVE TESTS: the clauses can fail
-- in front of the joinings o_omega's group has no member
#guard !frontAt (upTo atKey ((withU atKey.S).getD #[]) 6 (sh2 (first atKey.codes
  (keyW atKey.par.S.fold.index)))) 1 none
-- a member as the mask
#guard !frontAt (endOf atKey) 0 (some 0)
-- a group that is not there
#guard !frontAt (endOf atKey) 2 none
-- a message that is sampled as the mask
#guard !frontAt (endOf atKey) 0 (some 2)

end Desc.K14.Shape.EndToy
