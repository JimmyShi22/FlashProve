-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/All/TraceK.lean: scales, parameters and sizes of the segments of a group of layers, at
  given scales. Definitions, and a small lemma (`kapG_lt`).

  For group g (Inst/Model/All/Trace.lean): `kapG κ g`: the scales of its four layers; `PG κ g l`:
  the parameters of its layer l; `SFK κ nf g`: the scales of one segment (`Scl`), as an explicit
  term; `DAK κ g`: the sizes of its attention segment.
  The files of a feed-forward segment and of an attention segment take the scales as an instance
  argument `[scl : Scl]` (Inst/Model/Scl.lean). No statement of this file leaves that argument to
  Lean: it is written out, (scl := SFK κ nf g), wherever a name reads a scale.
  The trace (`Trace`) and the way in which a segment reads it (`vFF`, `vAtt`, `vHead`;
  Inst/Model/All/Trace.lean) take no scales: they read sizes only, and no size that they read
  depends on a scale (the live rows, `AttSeg.Dim.u0`, do: `DAK`).

  Notation:
    live rows: `AttSeg.Dim.u0`, "the number of live rows of the table Exp"; shift: `AttSeg.Dim.sh`,
      "the input shift of the exponential: 2^sh units of a score are one step of the table Exp"
      (Inst/Model/Att/Index.lean).
  Limits: this file says nothing on the chain, which is at the reference scales.
  Terms: lean/GLOSSARY.md.
-/
import Inst.Model.All.Trace
import Inst.Model.Head.TraceN
import Inst.Model.Scales
import Inst.Model.ProgramRPol

set_option autoImplicit false

/- no default scales are in sight in this file: what reads scales says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.All

open Layout (kRef hRef)

/-- The scales of the four layers of group g. A segment reads the layers ℓ < 4 only; the function is
continued with period 4, so that all its values are scales of the group. -/
abbrev kapG (κ : ℕ → LayerScale) (g : ℕ) : ℕ → LayerScale := fun l => κ (4 * g + l % 4)

theorem kapG_lt (κ : ℕ → LayerScale) (g : ℕ) {l : ℕ} (hl : l < 4) : kapG κ g l = κ (4 * g + l) := by
  show κ (4 * g + l % 4) = _
  rw [Nat.mod_eq_of_lt hl]

/-- The parameters of layer ℓ of group g. -/
abbrev PG (κ : ℕ → LayerScale) (g l : ℕ) : Params := ppref.at (kapG κ g l)
/-- The scales of one segment (`Scl`, Inst/Model/Scl.lean) for group g: an explicit term, passed to
every name of a feed-forward or attention segment that reads a scale. -/
abbrev SFK (κ : ℕ → LayerScale) (nf : NormPar) (g : ℕ) : Scl := ⟨kapG κ g, nf⟩
/-- The sizes of the attention segment of group g: the reference sizes with the live rows of the
group's first layer. (Its shift is read from the scales `SFK κ nf g`: that of the group's first
layer.) -/
abbrev DAK (κ : ℕ → LayerScale) (g : ℕ) : AttSeg.Dim := AttSeg.Dim.refK (κ (4 * g)).expRows.toNat

end Inst.Model.All
