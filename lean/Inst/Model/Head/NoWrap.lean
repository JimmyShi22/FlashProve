-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/NoWrap.lean: the class `Lawful`: the quantization scales are valid for the head, by
their final normalisation (`Scl.nf`, Inst/Model/Scl.lean).

  `Lawful`            the scales are valid for the head: their final normalisation is in the range
                      of NORM (`NormPar.OK`, Inst/Model/Program.lean); the reference scales are
                      valid
(Words of this library: lean/GLOSSARY.md.)
-/
import Inst.Model.Head.NoWrapN

set_option autoImplicit false

namespace Inst.Model.Head

/-- the final normalisation of `ppref` is valid -/
theorem nf_ok : ppref.nf.OK := by unfold NormPar.OK; decide

/-- The quantization scales are valid for the head: their final normalisation is in the range of
NORM (`NormPar.OK`, Inst/Model/Program.lean). -/
class Lawful [scl : Scl] : Prop where
  nf : scl.nf.OK

/-- the reference scales are valid -/
instance Lawful.ref : @Lawful Scl.ref := ⟨nf_ok⟩

end Inst.Model.Head
