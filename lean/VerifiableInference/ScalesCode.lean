-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/ScalesCode.lean

A number for each table of scales.

A table of scales (`Cm.Scales`, Cm/Rel2.lean) is a finite list of natural numbers and integers.
`scalesNumber` packs them into one natural number, by Mathlib's pairing of numbers
(`Encodable`). Different tables have different numbers. No value is picked by choice: the number
comes from the functions written below and Mathlib's `Encodable`, and no definition of this file is
marked noncomputable (the numbering of keys is: `numberOf`, VerifiableInference/KeyCode.lean).
Lean's list of axioms under `scalesNumber` still has `Classical.choice`. No definition of this file
names it: it comes in with what Mathlib's `Encodable` rests on.

The number can serve as the tag under which keys are coded (the coding:
VerifiableInference/KeyCode.lean), so that the digest
of a key covers the table of scales.
-/
import Cm.Rel2
import Mathlib.Logic.Encodable.Pi
import Mathlib.Logic.Denumerable

set_option autoImplicit false

/- No default table of scales here: `Scl.ref` (Inst/Model/Scl.lean) is off; each `Scl` is named. -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference

/-- The three numbers of a normalisation, packed into one. -/
instance encodableNormPar : Encodable Inst.Model.NormPar :=
  Encodable.ofLeftInjection (fun a => (a.M, a.K, a.eps)) (fun t => some ⟨t.1, t.2.1, t.2.2⟩)
    fun _ => rfl

/-- The numbers of one layer of a table of scales, packed into one. -/
instance encodableWords : Encodable Inst.Model.Words :=
  Encodable.ofLeftInjection
    (fun a => (a.kq, a.kk, a.kv, a.ko, a.kg, a.ku, a.kd, a.kr, a.kg', a.ku', a.n1, a.n2, a.sh))
    (fun t => some ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2.1,
      t.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2.2.1,
      t.2.2.2.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2.2.2.2⟩)
    fun _ => rfl

/-- The numbers of a table of scales, packed into one. -/
instance encodableScales : Encodable Cm.Scales :=
  Encodable.ofLeftInjection (fun s => (s.w, s.nf)) (fun t => some ⟨t.1, t.2⟩) fun _ => rfl

/-- The number of a table of scales. -/
def scalesNumber (s : Cm.Scales) : ℕ :=
  Encodable.encode s

/-- Different tables of scales have different numbers. -/
theorem scalesNumber_injective : Function.Injective scalesNumber :=
  Encodable.encode_injective

end VerifiableInference

#print axioms VerifiableInference.scalesNumber_injective
#print axioms VerifiableInference.scalesNumber
