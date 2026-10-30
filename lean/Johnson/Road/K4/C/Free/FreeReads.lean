-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/Free/FreeReads.lean: a fact at copies of the layout's functions, with four
variables, from an evaluation at closed values.

What is here. At each of the twelve groups the array of the reads has a column, and the row of the
first free entry behind the reads fits 32 bits: what the verifier's reader U3at
(OnBytes/Model/LayerForms.lean) tests beside the entry's number. The statement (freeReads) speaks
of the library's copies of the makers of the public part, without the lines at which Lean's kernel
stops (Johnson/Road/K4/RowHead/Twins.lean), at the full size's frame, with four variables: the
parameter file's eight free numbers, the counts of padding keys, the scales, the rotary table. No
maker is evaluated with a variable in the term: the test (testReads) holds at closed values, by
kernel_rfl (Johnson/Unfolds/KernelRfl.lean): one comparison by a kernel (closedReads); it has one
value with the variables laid in and without them, by unfolding (blindReads); so it holds at all of
them (allReads); and the library's withPlans follows by plans_closed
(Johnson/Road/K4/RowHead/ClosedJoin.lean). Not by one kernel_rfl with the four variables in the
term: RowHead/ClosedAt.lean says why. Beneath freeReads stand eight uses of kernel_rfl:
closedReads; closedSizes and weightsAt (RowHead/ClosedAt.lean), without a variable; and five
equations on the parameter file's scan (RowHead/ClosedTies.lean), in which the eight free numbers
are a variable, and in one of them the layout too. One definition.

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
import Johnson.Desc.First.K4.Returns.Pub.Tables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C.Free
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Pub HPlan2 Scales)
open OnBytes.Road.K4 (withPlans)
open OnBytes.Road.K4.C (setP)
open OnBytes.Road.K4.Closed (afterN scC wC after_letters plans_closed)

/-- The test. At each of the twelve groups the array of the reads has a column, and the row of the
first free entry behind the reads fits 32 bits: what the verifier's reader U3at
(OnBytes/Model/LayerForms.lean) tests beside the entry's number. -/
def testReads : Pub → Array HPlan2 → Bool :=
  fun L G => (List.range 12).all fun g => (G[g]?).any fun hp =>
      (hp.tl.ix.U.getD 2 none).any fun iU3 =>
        (OnBytes.Desc.First.K4.RtPub.tablesAt L g).any fun r =>
          ((hp.Fp.trees[iU3]?).map (·.K)).getD 0 != 0 &&
            decide (r.2.2 / ((hp.Fp.trees[iU3]?).map (·.K)).getD 0 < 2 ^ 32)

/-- It has one value with the variables laid in and without them. -/
theorem blindReads (e1 e2 eF : Nat) (pub : Array Nat) (sc : Scales) (rope : Array Nat) (W : WsLay)
    (L : Pub) (G : Array HPlan2) :
    testReads (setP L e1 e2 eF pub sc rope W) G = testReads L G := rfl

/-- It holds at closed values. No variable. -/
theorem closedReads : afterN 0 0 0 #[] scC #[] wC testReads = true := by
  kernel_rfl

/-- So it holds at all of them. -/
theorem allReads (e1 e2 eF : Nat) (pub : Array Nat) (sc : Scales) (rope : Array Nat) (W : WsLay) :
    afterN e1 e2 eF pub sc rope W testReads = true :=
  after_letters e1 e2 eF pub #[] sc scC rope #[] W wC (blindReads e1 e2 eF pub sc rope W)
    closedReads

/-- **The fact at the four variables**: from closedReads, by laws. -/
theorem freeReads (v : VerifierAndGoals.FreeLines) (pub : Array Nat) (sc : Layer.Scales) (rope : Array Nat) :
    withPlans v pub sc rope (fun L G => (List.range 12).all fun g => (G[g]?).any fun hp =>
      (hp.tl.ix.U.getD 2 none).any fun iU3 =>
        (OnBytes.Desc.First.K4.RtPub.tablesAt L g).any fun r =>
          ((hp.Fp.trees[iU3]?).map (·.K)).getD 0 != 0 &&
            decide (r.2.2 / ((hp.Fp.trees[iU3]?).map (·.K)).getD 0 < 2 ^ 32)) = true :=
  plans_closed (f := testReads) (fun e1 e2 eF W => allReads e1 e2 eF pub sc rope W)

end OnBytes.Road.K4.C.Free

#print axioms OnBytes.Road.K4.C.Free.blindReads
#print axioms OnBytes.Road.K4.C.Free.closedReads
#print axioms OnBytes.Road.K4.C.Free.allReads
#print axioms OnBytes.Road.K4.C.Free.freeReads
