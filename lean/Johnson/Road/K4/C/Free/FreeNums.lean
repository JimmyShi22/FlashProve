-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/Free/FreeNums.lean: a fact at copies of the layout's functions, with four
variables, from an evaluation at closed values.

What is here. At each of the twelve groups the test planNumsB, ten tests on the plan's numbers
(Johnson/Desc/First/K4/Returns/Needs.lean) holds. The statement (freeNums) speaks of the library's
copies of the makers of the public part, without the lines at which Lean's kernel stops
(Johnson/Road/K4/RowHead/Twins.lean), at the full size's frame, with four variables: the parameter
file's eight free numbers, the counts of padding keys, the scales, the rotary table. No maker is
evaluated with a variable in the term: the test (testNums) holds at closed values, by kernel_rfl
(Johnson/Unfolds/KernelRfl.lean): one comparison by a kernel (closedNums); it has one value with
the variables laid in and without them, by unfolding (blindNums); so it holds at all of them
(allNums); and the library's withPlans follows by plans_closed
(Johnson/Road/K4/RowHead/ClosedJoin.lean). Not by one kernel_rfl with the four variables in the
term: RowHead/ClosedAt.lean says why. Beneath freeNums stand eight uses of kernel_rfl: closedNums;
closedSizes and weightsAt (RowHead/ClosedAt.lean), without a variable; and five equations on the
parameter file's scan (RowHead/ClosedTies.lean), in which the eight free numbers are a variable,
and in one of them the layout too. One definition.

  `testNums`   the test; it also asks that each of the twelve groups has a plan: where one
      lacks it is false. A definition.
  `blindNums`   it has one value with the variables laid in and without them.
  `closedNums`   it holds at closed values: one kernel_rfl, no variable.
  `allNums`   so it holds at all of them.
  `freeNums`   **the fact at the four variables.**

Not shown here. Anything on public files. Only for the parameter files whose scan is Pv v at some
eight free numbers v (the full-size model). The eight uses of kernel_rfl are comparisons by Lean's
own kernel; no independent checker has replayed this file. No negative test stands beside
closedNums: no input is shown at which the test says no. The import closure, by a program's walk
along the imports that stops unopened at Johnson/Goal/, Johnson/D/, Johnson/Bridge/ and ThirdParty/
and at every name that begins Cb.Bridge (so these are floors): one module under Johnson/Goal/
(Meaning/ScopeScan.lean, through the library's Twins.lean); none at the other four; none whose name
holds RecCompile. Nothing of it is restated here and no goal is stated. A LAW, NOT A PART: no file
that defines a part of the proof file's description may import this one.

Kin. The library has a fact of this form, by the same road, for another test (frontB, at the groups
0 and 1): `front_free_at` (Johnson/Road/K4/RowHead/FrontFreeK.lean). `light_head`
(Johnson/Road/K4/C/PublicLight.lean) carries this fact and four sisters of this folder, each for a
test of its own (FreeDepth, FreePoints, FreeSlots, FreeTables), to the head's own public parameters.
FreeOwners.lean, of this folder too, has the like fact for a test of its own; `light_head` does not
carry it.
No property is claimed.
-/
import Johnson.Unfolds.KernelRfl
import Johnson.Road.K4.RowHead.ClosedJoin
import Johnson.Desc.First.K4.Returns.Needs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C.Free
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Pub HPlan2 Scales)
open OnBytes.Road.K4 (withPlans)
open OnBytes.Road.K4.C (setP)
open OnBytes.Road.K4.Closed (afterN scC wC after_letters plans_closed)
open OnBytes.Desc.First.K4.Rt (planNumsB)

/-- The test. At each of the twelve groups the test planNumsB, ten tests on the plan's numbers
(Johnson/Desc/First/K4/Returns/Needs.lean) holds. -/
def testNums : Pub → Array HPlan2 → Bool :=
  fun L G => (List.range 12).all fun g => (G[g]?).any fun hp =>
      planNumsB L hp g

/-- It has one value with the variables laid in and without them. -/
theorem blindNums (e1 e2 eF : Nat) (pub : Array Nat) (sc : Scales) (rope : Array Nat) (W : WsLay)
    (L : Pub) (G : Array HPlan2) :
    testNums (setP L e1 e2 eF pub sc rope W) G = testNums L G := rfl

/-- It holds at closed values. No variable. -/
theorem closedNums : afterN 0 0 0 #[] scC #[] wC testNums = true := by
  kernel_rfl

/-- So it holds at all of them. -/
theorem allNums (e1 e2 eF : Nat) (pub : Array Nat) (sc : Scales) (rope : Array Nat) (W : WsLay) :
    afterN e1 e2 eF pub sc rope W testNums = true :=
  after_letters e1 e2 eF pub #[] sc scC rope #[] W wC (blindNums e1 e2 eF pub sc rope W)
    closedNums

/-- **The fact at the four variables**: from closedNums, by laws. -/
theorem freeNums (v : VerifierAndGoals.FreeLines) (pub : Array Nat) (sc : Layer.Scales) (rope : Array Nat) :
    withPlans v pub sc rope (fun L G => (List.range 12).all fun g => (G[g]?).any fun hp =>
      planNumsB L hp g) = true :=
  plans_closed (f := testNums) (fun e1 e2 eF W => allNums e1 e2 eF pub sc rope W)

end OnBytes.Road.K4.C.Free

#print axioms OnBytes.Road.K4.C.Free.testNums
#print axioms OnBytes.Road.K4.C.Free.blindNums
#print axioms OnBytes.Road.K4.C.Free.closedNums
#print axioms OnBytes.Road.K4.C.Free.allNums
#print axioms OnBytes.Road.K4.C.Free.freeNums
