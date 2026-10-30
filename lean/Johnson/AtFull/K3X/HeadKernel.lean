-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/HeadKernel.lean: the three tests on the output head's layout and plan
(Johnson/AtFull/K3X/HeadTests.lean) say yes at the full size's written numbers. Three closed facts,
each proved by evaluation in Lean's kernel, with a negative test beside each.

  names_head_W   on strings alone. names_head_no: with the word of another sort of link the name is
                 not the written one.
  headCalls_W    at the head's layout as its makers make it (withLaid,
                 Johnson/AtFull/Head/PubAtFull.lean): the six calls, their tables taken out, are the
                 written calls. By its text the test reads no table and no array of columns.
  headCalls_no   with the last call dropped the test says no, while the makers return.
  headTail_W     at the head's plan as planH2 makes it from the written numbers (runW,
                 Johnson/AtFull/Head/PlanAtFull.lean).
  headTail_no, headTail_no2   with one slot more (it fails at the first clause), and with the depth
                 limit of the smallness test's lookup raised by one, the test says no, while the
                 plan's maker returns.
  headTail_no3   the clause on the first slot alone, with 2^19 columns of the weights' matrix in the
                 place of 2^18: it says no, while the plan's maker returns.
  headTail_HW    so the test says yes at HW, the plan's value.

Limits. The full size, at the stored free numbers alone. Nothing of a key file or a proof file is
read. Nothing on soundness.
-/
import Johnson.AtFull.K3X.HeadTests
import Johnson.AtFull.Head.PubAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.K3X
open OnBytes OnBytes.Model
open _root_.AtFull.Head (withLaid runW runW_ok HW)

theorem names_head_W : namesHeadT = true := by decide +kernel

/-- A negative test. -/
theorem names_head_no : (nameOf 24 "layers" false == Lots.K3.nameW 24 false) = false := by
  decide +kernel

/-- **By the kernel**: the head's six calls. -/
theorem headCalls_W : withLaid headCallsT = true := by decide +kernel

/-- A negative test: the last call dropped. (withLaid is false also where a maker refuses: that the
makers return is headCalls_W's: it is the control.) -/
theorem headCalls_no : withLaid (fun HLy => headCallsT { HLy with cl := HLy.cl.pop }) = false := by
  decide +kernel

/-- **By the kernel**: what is read of the head's plan. -/
theorem headTail_W : (match runW with
    | .ok H => headTailT H.ns H.tl
    | .error _ => false) = true := by decide +kernel

/-- A negative test: one slot more. Where the maker refused this would be true. -/
theorem headTail_no : (match runW with
    | .ok H => headTailT (H.ns + 1) H.tl
    | .error _ => true) = false := by decide +kernel

/-- A negative test: the depth limit raised by one. -/
theorem headTail_no2 : (match runW with
    | .ok H => headTailT H.ns { H.tl with lidb := H.tl.lidb + 1 }
    | .error _ => true) = false := by decide +kernel

/-- A negative test of the clause on the first slot alone: 19 in the place of 18. -/
theorem headTail_no3 : (match runW with
    | .ok H => VerifiableInference.Desc.First.Look.digitsNext H.ns (wsForkSlots 19)
        (Forest.elems H.tl.f9) == some (Lots.K3.firstW 3 true)
    | .error _ => true) = false := by decide +kernel

theorem headTail_HW : headTailT HW.ns HW.tl = true := by
  have h := headTail_W
  rw [runW_ok] at h
  exact h

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.names_head_W
#print axioms Johnson.AtFull.K3X.names_head_no
#print axioms Johnson.AtFull.K3X.headCalls_W
#print axioms Johnson.AtFull.K3X.headCalls_no
#print axioms Johnson.AtFull.K3X.headTail_W
#print axioms Johnson.AtFull.K3X.headTail_no
#print axioms Johnson.AtFull.K3X.headTail_no2
#print axioms Johnson.AtFull.K3X.headTail_no3
#print axioms Johnson.AtFull.K3X.headTail_HW
