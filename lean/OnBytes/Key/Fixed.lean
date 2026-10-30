-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Key/Fixed.lean: the public values of a key file's first chain fit together.

A key's first chain binds, in addition to the table, five public values: the codes, the shape of the
test on the committed table, the notice of the index-mask message, the item "ranges", and the shape
of the binding tree. Each has conditions of its own. This file has the conditions that only several
of them together can show. No key can be made or read under values that fail them.

The test is written once, here. It is asked where the values are made from the public files, and
again where a key file is checked under the values of its first chain's parameter bytes.

Main definition: `Key.fixedOk`.
C++ counterpart: key_fault() in blocks/frame/key_fixed.h.

What is not claimed: no theorem is stated here.
-/
import OnBytes.Iop.Wf
import OnBytes.Iop.Lin

namespace OnBytes.Key

open OnBytes.Params (LinShape WfPublic LinBindingShape)

/-- The public values of a key's first chain fit together.
 - The shape of the test on the table is admitted under the codes.
 - The item "ranges" is admitted under the codes and the matrix's size, which is taken from the
   shape of the test on the table and from nowhere else.
 - The binding tree has one leaf.
 - The oracle message of the multiplicities is the second of the chain.
 - The index-mask message is a sampled message of mask rows only, under a mask code that exists.
 - It has room for the entries that the lookups and the joining take. -/
def fixedOk (codes : Codes) (lin : LinShape) (indexMasks : OracleNotice) (ranges : WfPublic)
    (binding : LinBindingShape) : Bool :=
  let m := indexMasks.shape
  let matrix := Wf.matrixOf lin
  linOk codes lin &&
  Wf.admitted codes ranges matrix &&
  binding.logLeaves == 0 &&
  ranges.messageId == 1 &&
  m.mainRows == 0 && m.maskRows != 0 && decide (1 ≤ m.answers) &&
  decide (m.maskCode < codes.mask.size) &&
  decide (Wf.indexMaskEntries ranges matrix ≤
    Send.freeMaskEntries m.maskRows (codes.mask.getD m.maskCode default).ell m.answers)

end OnBytes.Key
