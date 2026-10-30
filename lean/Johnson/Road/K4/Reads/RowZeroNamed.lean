-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Reads/RowZeroNamed.lean: RowZero.lean's TWO STATEMENTS WITH THEIR PREMISES ON WHAT
THE LOOKUP RETURNED PAID OUT OF ONE RECORD OF THE LOOKUP's OWN: `Fo.Tp.PadNames g F'`
(Johnson/Top/H/Keep/PadNamed.lean: every row that a hearing of the lookup keeps, the form in which
its key side ends and its leaves' start form name no entry). Statements and proofs: calls.

  `inTab_bare`: a form that names no entry (the library's `Bare`) is `InTab v`, at every v, for
    nothing.
  **`front_row0_named`**, **`back_row0_named`**: behind K4's hearing, IF hK : hp.nU[2] ≤ o.v.K3 AND
    `PadNames o.H.fo F'` at some ledger F': every entry that a form of `formsFrontWith rows` (either
    form of the run) | `formsBack` names is (o.v.iU3, 0, i) with i below hp.nU[2].

Limits. hK is a premise on the plan's make (RowZero.lean). `PadNames` AT K4's OWN o.H.fo IS A
PREMISE: the lookup's law has it of the record that ITS hearing returns (`pad_named`): that this
record is the one that K4 was handed is not said here. F' is spent nowhere: of `PadNames` the halves
on entries alone are. Nothing on soundness.
-/
import Johnson.Road.K4.Reads.RowZero
import Johnson.Top.H.Keep.PadNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Reads

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Pub Own HPlan2)
open _root_.Fo.Tp (PadNames bare_ents)

/-- A form that names no entry is covered, for nothing. -/
theorem inTab_bare (v : Env) {f : Aff} (h : OnBytes.Road.Rows.Bare f) : InTab v f :=
  entsIn_noEnts (bare_ents h)

variable {P : Pub} {hpl : HPlan2} {g : Nat} {fo : Forest.Heard} {F0 G0 F' : Fork}
  {t u : OnBytes.K.Kc.Tape} {o : Own}

/-- **The run "front", at either form, behind the hearing, under the lookup's own record.** -/
theorem front_row0_named {rows : Bool} {F G : Fork} {fs : Array Aff}
    (hh : hearFl P hpl g fo F0 t = some (o, G0, u)) (hK : hpl.nU.getD 2 0 ≤ o.v.K3)
    (N : PadNames o.H.fo F') (h : formsFrontWith rows P g o F = some (fs, G)) :
    ∀ f ∈ fs.toList, ∀ y ∈ f.ents.toList,
      y.tree = o.v.iU3 ∧ y.row = 0 ∧ y.idx < hpl.nU.getD 2 0 :=
  front_row0 hh hK h (fun _ f hf => inTab_bare o.v (N.rows f hf).1) (inTab_bare o.v N.start.1)

/-- **The run "back", behind the hearing, under the lookup's own record.** -/
theorem back_row0_named {F G : Fork} {fs : Array Aff}
    (hh : hearFl P hpl g fo F0 t = some (o, G0, u)) (hK : hpl.nU.getD 2 0 ≤ o.v.K3)
    (N : PadNames o.H.fo F') (h : formsBack o F = some (fs, G)) :
    ∀ f ∈ fs.toList, ∀ y ∈ f.ents.toList,
      y.tree = o.v.iU3 ∧ y.row = 0 ∧ y.idx < hpl.nU.getD 2 0 :=
  back_row0 hh hK h (bare_ents N.cEnd.1)

end OnBytes.Desc.First.K4.Reads

#print axioms OnBytes.Desc.First.K4.Reads.front_row0_named
#print axioms OnBytes.Desc.First.K4.Reads.back_row0_named
