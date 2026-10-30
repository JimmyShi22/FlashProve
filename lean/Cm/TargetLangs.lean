-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetLangs.lean: the index's side of the integer model of Cm/ in a configuration: the entries of
an index, their places, and what a table of entries holds.

Definitions; lemmas on them are in Cm/TargetLangsProofs.lean; the configuration, with the relation
pair modulo the field's own characteristic, is Cm/TargetPLangs.lean; a code's side with room for the
index, over p = 2^64 - 2^32 + 1: Cm/TargetLangsGl.lean.
(In the form of a partition the integer model, with its conditions modulo the field's prime,
is Cm/TargetPart.lean's `targetPart R s`.)

Main names:
  `TargetEnt`: the numbers (row, column) of the entries of an index of the model: 3,076,096 rows,
    2^18 columns.
  `targetAt Cf₀ pl q`: the place of q (see its docstring); pl sends q to a row and a place of the
    layout.
  `targetBody Cf₀ pl i`: the entries of the index i: at the place of q the image in F of the
    integer i q (of one such q, by choice, if several entries share a place); 0 at all other
    places.
  `targetHeld Cf₀ pl a`: the index that a table a of entries holds: the index whose entries' images
    stand at the places, if there is one; it reads nothing else. By choice: no program.

Limits: in the write-up membership in the index set is a clause of both relations; here it is in the
type of indices.
This file says nothing on weights-formedness (that "holds an index" is "all keys lie in their
tables"), and nothing on which layout the write-up has: pl is any map under which different entries
stand at different places (so is the layout in the write-up's definition; its test for linear
constraints asks one form of it: each row of the encoded index takes one block of consecutive
columns of the index).
A lawful table need not be sensible (Cm/Rel2Idle.lean). No weights are in sight.
Terms: lean/GLOSSARY.md.
The notions follow the worked example named in lean/CREDITS.md; the text is this library's.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Obj.LdObjectConfMore
import Cm.Rel2Proofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm

open Inst.Model Inst.Model.All Iop Prob Hiop Cb
open Inst.Model.Layout (kRef hRef)

/-- the numbers (row, column) of the entries of an index of the model -/
abbrev TargetEnt : Type := Fin hRef × Fin (2 ^ kRef)

section
variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (Cf₀ : LdCf F E) (pl : TargetEnt → Cf₀.Row × Cf₀.Lay)

/-- the place at which an entry of the index stands: a row of the format, and an entry of the row
that lies in the layout -/
def targetAt (q : TargetEnt) : Cf₀.Row × Cf₀.J₀ := ((pl q).1, Cf₀.lay (pl q).2)

open Classical in
/-- the entries of an index: the images of its integers at their places, 0 elsewhere (where entries
share a place: see the head) -/
def targetBody (i : Idx) : Cf₀.Row × Cf₀.J₀ → F :=
  fun n => if h : ∃ q, targetAt Cf₀ pl q = n then ((i.val h.choose.1 h.choose.2 : ℤ) : F) else 0

open Classical in
/-- the index that a table of entries holds: the index whose entries' images stand at the places,
if there is one -/
def targetHeld (a : Cf₀.Row × Cf₀.J₀ → F) : Option Idx :=
  if h : ∃ i : Idx,
    ∀ q, a (targetAt Cf₀ pl q) = ((i.val q.1 q.2 : ℤ) : F) then some h.choose else none

end

end Cm
