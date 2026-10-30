-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Arrays/SameTensors.lean

Which indices have the same weights as arrays: those that hold the same weight tensors.
At valid settings (`valid`): `index_indexOfWeights`: the matrix of digits made from the arrays of an
index holds the tensors of that index. `weightsOfIndex_eq_iff`: two indices have the same arrays
exactly if they hold the same tensors (`Cm.Idx.index`, Cm/RelBase.lean). So what the arrays do not
keep of a matrix of digits is what its tensors do not keep. By a reading of the layout
(Cm/RelBase.lean), and no theorem, these are the entries at which no byte of a weight lies.
-/
import IntegerModel.Arrays.OfIndex
import IntegerModel.Arrays.RoundTrip

set_option autoImplicit false

/- No default table of scales here: `Scl.ref` (Inst/Model/Scl.lean) is off; each `Scl` is named. -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference

open Inst.Model IntegerModel.Readable IntegerModel.Runnable Back

variable {settings : IntegerTransformer.Settings} (valid : settingsAreValid settings = true)

/-- At valid settings, the matrix made from the arrays of an index holds the same tensors as that
index. -/
theorem index_indexOfWeights (index : Cm.Idx) :
    (indexOfWeights valid (weightsOfIndex valid index)).index = index.index := by
  unfold indexOfWeights
  rw [Cm.index_ofIndex]
  exact Subtype.ext (weightsTo_weightsArraysOf index.index.property)

/-- At valid settings, two indices have the same arrays exactly if they hold the same tensors. -/
theorem weightsOfIndex_eq_iff (index index' : Cm.Idx) :
    weightsOfIndex valid index = weightsOfIndex valid index' ↔ index.index = index'.index := by
  constructor
  · intro h
    rw [← index_indexOfWeights valid index, h, index_indexOfWeights valid index']
  · intro h
    exact Subtype.ext (congrArg (fun tensors : Index ppref => weightsArraysOf ppref tensors.val) h)

end VerifiableInference
