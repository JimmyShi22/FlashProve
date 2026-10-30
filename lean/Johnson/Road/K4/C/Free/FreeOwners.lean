-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/Free/FreeOwners.lean: NO HYPOTHESIS. A fact at copies of the layout's functions,
with four variables, from an evaluation at closed values.

What is here. At each of the twelve groups: the group stands in the public parameters' list of tails
(the sub-proofs' lists of matrices), and each matrix of its list to which an earlier sub-proof has
committed (kind 1) names an earlier group and a matrix of that group's list: the seventh and the
eighth clause of the public test `k4TableFits` (Johnson/Desc/ProofFile/Honest/K4/Part.lean), typed
here at the layers' public parameters and a group's number, without that file's frame. The statement
(freeOwners) speaks of the library's copies of the makers of the public part, without the lines at
which Lean's kernel stops (Johnson/Road/K4/RowHead/Twins.lean), at the full size's frame, with four
variables: the parameter file's eight free numbers, the counts of padding keys, the scales, the
rotary table. Built step by step as FreeSlots.lean and FreeTables.lean are. No maker is evaluated
with a variable in the term: the test (testOwners) holds at closed values, by kernel_rfl
(Johnson/Unfolds/KernelRfl.lean): one comparison by a kernel (closedOwners); it has one value with
the variables laid in and without them, by unfolding (blindOwners); so it holds at all of them
(allOwners); and the library's withPlans follows by plans_closed
(Johnson/Road/K4/RowHead/ClosedJoin.lean). Beneath freeOwners stand eight uses of kernel_rfl:
closedOwners; closedSizes and weightsAt (RowHead/ClosedAt.lean), without a variable; and five
equations on the parameter file's scan (RowHead/ClosedTies.lean), in which the eight free numbers
are a variable, and in one of them the layout too. Two definitions.

  `ownersAt`   the two clauses at one group. A definition.
  `testOwners`   the test. A definition.
  `blindOwners`   it has one value with the variables laid in and without them.
  `closedOwners`   it holds at closed values: one kernel_rfl, no variable.
  `allOwners`   so it holds at all of them.
  `freeOwners`   **the fact at the four variables.**

Not shown here. Anything on public files. Only for the parameter files whose scan is Pv v at some
eight free numbers v (the full-size model). The eight uses of kernel_rfl are comparisons by Lean's
own kernel; no independent checker has replayed this file. No input is shown at which the clause on
a borrowed matrix's owner says no. The import closure, by a program's walk along the imports that
stops unopened at Johnson/Goal/, Johnson/D/, Johnson/Bridge/ and ThirdParty/ and at every name that
begins Cb.Bridge (so these are floors): one module under Johnson/Goal/ (Meaning/ScopeScan.lean,
through the library's Twins.lean); none at the other four; none whose name holds RecCompile. Nothing
of it is restated here and no goal is stated. A LAW, NOT A PART: no file that defines a part of the
proof file's description may import this one.

Kin. The library has a fact of this form, by the same road, for another test (frontB, at the groups
0 and 1): `front_free_at` (Johnson/Road/K4/RowHead/FrontFreeK.lean). Five sisters stand in this
folder, each for a test of its own (FreeDepth, FreeNums, FreePoints, FreeSlots, FreeTables).
`tableFits_head` (Johnson/Desc/ProofFile/Honest/K4/Law/TableFitsMember.lean) carries this fact to
the head's own public parameters. Sought: by statement, to the letter and up to the bound letters,
and by short name, among the theorems of the library: no hit. Not sought: twins of the two
definitions in other letters.
No property is claimed.
-/
import Johnson.Unfolds.KernelRfl
import Johnson.Road.K4.RowHead.ClosedJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C.Free
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Pub HPlan2 Scales)
open OnBytes.Road.K4 (withPlans)
open OnBytes.Road.K4.C (setP)
open OnBytes.Road.K4.Closed (afterN scC wC after_letters plans_closed)

/-- The two clauses at one group. The plan is not read. -/
def ownersAt (L : Pub) (_ : HPlan2) (g : Nat) : Bool :=
  decide (g < L.tails.size) &&
    ((L.tails.getD g {}).mats.all fun M =>
      M.kind != 1 || (decide (256 ≤ M.aId) && decide (M.aId / 256 - 1 < g) &&
        decide (M.aId % 256 < (L.tails.getD (M.aId / 256 - 1) {}).mats.size)))

/-- The test. -/
def testOwners : Pub → Array HPlan2 → Bool :=
  fun L G => (List.range 12).all fun g => (G[g]?).any fun hp => ownersAt L hp g

/-- It has one value with the variables laid in and without them. -/
theorem blindOwners (e1 e2 eF : Nat) (pub : Array Nat) (sc : Scales) (rope : Array Nat) (W : WsLay)
    (L : Pub) (G : Array HPlan2) :
    testOwners (setP L e1 e2 eF pub sc rope W) G = testOwners L G := rfl

/-- It holds at closed values. No variable. -/
theorem closedOwners : afterN 0 0 0 #[] scC #[] wC testOwners = true := by
  kernel_rfl

/-- So it holds at all of them. -/
theorem allOwners (e1 e2 eF : Nat) (pub : Array Nat) (sc : Scales) (rope : Array Nat) (W : WsLay) :
    afterN e1 e2 eF pub sc rope W testOwners = true :=
  after_letters e1 e2 eF pub #[] sc scC rope #[] W wC (blindOwners e1 e2 eF pub sc rope W)
    closedOwners

/-- **The fact at the four variables**: from closedOwners, by laws. -/
theorem freeOwners (v : VerifierAndGoals.FreeLines) (pub : Array Nat) (sc : Layer.Scales) (rope : Array Nat) :
    withPlans v pub sc rope (fun L G => (List.range 12).all fun g => (G[g]?).any fun hp =>
      ownersAt L hp g) = true :=
  plans_closed (f := testOwners) (fun e1 e2 eF W => allOwners e1 e2 eF pub sc rope W)

end OnBytes.Road.K4.C.Free

#print axioms OnBytes.Road.K4.C.Free.ownersAt
#print axioms OnBytes.Road.K4.C.Free.testOwners
#print axioms OnBytes.Road.K4.C.Free.blindOwners
#print axioms OnBytes.Road.K4.C.Free.closedOwners
#print axioms OnBytes.Road.K4.C.Free.allOwners
#print axioms OnBytes.Road.K4.C.Free.freeOwners
