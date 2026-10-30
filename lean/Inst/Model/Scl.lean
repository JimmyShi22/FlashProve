-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Scl.lean: the quantization scales of a segment, as an instance argument.

The sub-proof of a segment of the model is a long chain of definitions and theorems. The public
quantization scales (the shifts and the constants of the normalisations) enter it in a handful of
places: the integer relation of the trace, the verifier's key forms, the honest prover's trace. No
shape, count or size depends on them, but the number of rows in use of Exp, `LayerScale.expRows`, is
the field u0 of `AttSeg.Dim` (`DAK`, Inst/Model/All/TraceK.lean), and `nd sh`, the number of unused
rows of `tau2`, depends on the shift sh (Inst/Model/Tables.lean). So that the definitions between
these places and the top need not name the scales, they are the fields of a class:
    `Scl`              `κ l`: the scales of layer l of one segment (l = 0, .., 3 is read); `nf`: the
                       constants of the final normalisation (read by the head only)
A definition or theorem that reads a field of `Scl`, however far down, has the argument
`[scl : Scl]`, which Lean fills in from the context, up to the definition that fixes the table: for
instance `Scl.ref` (below) or `(scl := SFK κ nf g)` (Inst/Model/All/TraceK.lean). It holds for all
scales unless it says otherwise; what needs valid scales says so by a further argument (for a
feed-forward segment: `[FFSeg.Lawful]`, Inst/Model/FF/Lawful.lean).
    `Scl.ref`          the reference scales: the scales of `ppref` in every layer. It is an instance
                       of low priority: it is taken only where no other scales are in scope, that is
                       in the files that are only about the reference parameters.
                       They are not "THE" scales: no claim is made that they suit the weights of any
                       real model (where their numbers come from: lean/CREDITS.md, section 8).
This file does not say which scales are valid.
-/
import Inst.Model.Program

set_option autoImplicit false

namespace Inst.Model

/-- The scales of one segment, and the final normalisation. -/
class Scl where
  /-- the scales of layer l of the segment -/
  κ : ℕ → LayerScale
  /-- the constants of the final normalisation -/
  nf : NormPar

/-- The reference scales. Of low priority: scales that are in scope are preferred. -/
instance (priority := low) Scl.ref : Scl := ⟨fun _ => ppref.scale, ppref.nf⟩

end Inst.Model
