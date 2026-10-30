-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/Free/FreePlan.lean: a fact at copies of the layout's functions, with four
variables, from an evaluation at closed values.

What is here. At each of the twelve groups the plan's number of rounds of the batched sumcheck is
the function lamSOf of the layout and at most 63, and its number of weight claims is the function
nclOf of the layout and the group (OnBytes/Model/LayerPlan.lean). The statement (freePlan) speaks
of the library's copies of the makers of the public part, without the lines at which Lean's kernel
stops (Johnson/Road/K4/RowHead/Twins.lean), at the full size's frame, with four variables: the
parameter file's eight free numbers, the counts of padding keys, the scales, the rotary table. No
maker is evaluated with a variable in the term: the test (testPlan) holds at closed values, by
kernel_rfl (Johnson/Unfolds/KernelRfl.lean): one comparison by a kernel (closedPlan); it has one
value with the variables laid in and without them, by unfolding (blindPlan); so it holds at all of
them (allPlan); and the library's withPlans follows by plans_closed
(Johnson/Road/K4/RowHead/ClosedJoin.lean). Not by one kernel_rfl with the four variables in the
term: RowHead/ClosedAt.lean says why. Beneath freePlan stand eight uses of kernel_rfl: closedPlan;
closedSizes and weightsAt (RowHead/ClosedAt.lean), without a variable; and five equations on the
parameter file's scan (RowHead/ClosedTies.lean), in which the eight free numbers are a variable,
and in one of them the layout too. One definition.

Not shown here. Anything on public files. Only for the one parameter file whose scan the library's
copies read (the full-size model). The eight uses of kernel_rfl are comparisons by Lean's own
kernel; no independent checker has replayed this file. The import closure, by a program's walk
along the imports that stops unopened at Johnson/Goal/, Johnson/D/ and ThirdParty/ (so these are
floors): one module under Johnson/Goal/ (Meaning/ScopeScan.lean, through the library's Twins.lean);
none under the other two; none whose name holds RecCompile. Nothing of it is restated here and no
goal is stated. No property is claimed.
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

/-- The test. At each of the twelve groups the plan's number of rounds of the batched sumcheck is
the function lamSOf of the layout and at most 63, and its number of weight claims is the function
nclOf of the layout and the group (OnBytes/Model/LayerPlan.lean). -/
def testPlan : Pub → Array HPlan2 → Bool :=
  fun L G => (List.range 12).all fun g => (G[g]?).any fun hp =>
      hp.lamS == Layer.lamSOf L.y && hp.NCL == Layer.nclOf L.y g && decide (hp.lamS ≤ 63)

/-- It has one value with the variables laid in and without them. -/
theorem blindPlan (e1 e2 eF : Nat) (pub : Array Nat) (sc : Scales) (rope : Array Nat) (W : WsLay)
    (L : Pub) (G : Array HPlan2) :
    testPlan (setP L e1 e2 eF pub sc rope W) G = testPlan L G := rfl

/-- It holds at closed values. No variable. -/
theorem closedPlan : afterN 0 0 0 #[] scC #[] wC testPlan = true := by
  kernel_rfl

/-- So it holds at all of them. -/
theorem allPlan (e1 e2 eF : Nat) (pub : Array Nat) (sc : Scales) (rope : Array Nat) (W : WsLay) :
    afterN e1 e2 eF pub sc rope W testPlan = true :=
  after_letters e1 e2 eF pub #[] sc scC rope #[] W wC (blindPlan e1 e2 eF pub sc rope W)
    closedPlan

/-- **The fact at the four variables**: from closedPlan, by laws. -/
theorem freePlan (v : VerifierAndGoals.FreeLines) (pub : Array Nat) (sc : Layer.Scales) (rope : Array Nat) :
    withPlans v pub sc rope (fun L G => (List.range 12).all fun g => (G[g]?).any fun hp =>
      hp.lamS == Layer.lamSOf L.y && hp.NCL == Layer.nclOf L.y g && decide (hp.lamS ≤ 63)) =
      true :=
  plans_closed (f := testPlan) (fun e1 e2 eF W => allPlan e1 e2 eF pub sc rope W)

end OnBytes.Road.K4.C.Free

#print axioms OnBytes.Road.K4.C.Free.blindPlan
#print axioms OnBytes.Road.K4.C.Free.closedPlan
#print axioms OnBytes.Road.K4.C.Free.allPlan
#print axioms OnBytes.Road.K4.C.Free.freePlan
