-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Front/PolicyCode.lean

A number for each pair of a table of scales (`Cm.Scales`, Cm/Rel2.lean) and an acceptance policy
(`Inst.Model.AcceptancePolicy`, Inst/Model/ProgramR.lean), made by Mathlib's `Encodable` and `Nat.pair` over the
packing of a table in VerifiableInference/ScalesCode.lean. It can serve as a tag under which keys
are coded (the coding: VerifiableInference/KeyCode.lean).

Limits:
* The file is on numbers alone.



* The number covers the table and the policy's three numbers. It
  is one to one on tables; that different valid settings have different tables is
  `scalesOf_injective` (IntegerModel/Arrays/OfIndex.lean).
* A table with the policy of exact match does not have the table's number.

* Of the numbers `Nat.pair k m` only those with k = 0 are shown to be no table's number.

* It is no byte format, and no theorem ties it to what any program hashes.
-/
import VerifiableInference.ScalesCode
import Inst.Model.ProgramR

set_option autoImplicit false

/- No default table of scales is in sight in this file: the low-priority instance `Scl.ref`
(Inst/Model/Scl.lean) is switched off, so whatever takes an `Scl` has to say which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy

open VerifiableInference

/-! ## 1. The number -/

/-- The three numbers of a policy, packed into one. -/
instance encodablePol : Encodable Inst.Model.AcceptancePolicy :=
  Encodable.ofLeftInjection (fun a => (a.C, a.theta, a.cap)) (fun t => some ⟨t.1, t.2.1, t.2.2⟩)
    fun _ => rfl

/-- The number of a table of scales with a policy: the pair of 0 and the packed numbers of both. The
0 keeps it apart from the number of every table (`policyNumber_ne_scalesNumber`). No value is picked
by choice, and the definition is not marked noncomputable; Lean's list of axioms under it has
`Classical.choice`, which comes in with what Mathlib's `Encodable` rests on. -/
def policyNumber (s : Cm.Scales) (policy : Inst.Model.AcceptancePolicy) : ℕ :=
  Nat.pair 0 (Encodable.encode (s, policy))

/-- Two tables with policies that have the same number are the same table with the same policy. -/
theorem policyNumber_injective {s s' : Cm.Scales} {policy policy' : Inst.Model.AcceptancePolicy}
    (h : policyNumber s policy = policyNumber s' policy') : s = s' ∧ policy = policy' :=
  Prod.mk.inj (Encodable.encode_injective (Nat.pair_eq_pair.1 h).2)

/-! ## 2. It is the number of no table -/

/-- The number of a table with a policy is the number of no table. A table's number is the pair of
the code of its 48 layers' words and the code of its final normalisation. The first of these is the
code of a list of 48 entries, and the code of a list that is not empty is a successor (Lean sees
that by unfolding Mathlib's coding), so it is not the 0 that stands first in `policyNumber`. -/
theorem policyNumber_ne_scalesNumber (s s' : Cm.Scales) (policy : Inst.Model.AcceptancePolicy) :
    policyNumber s policy ≠ scalesNumber s' := fun equal =>
  have pairs : Nat.pair 0 (Encodable.encode (s, policy)) =
      Nat.pair (Encodable.encode s'.w) (Encodable.encode s'.nf) := equal
  Nat.succ_ne_zero _ (Nat.pair_eq_pair.1 pairs).1.symm

end Policy

#print axioms Policy.policyNumber
#print axioms Policy.policyNumber_injective
#print axioms Policy.policyNumber_ne_scalesNumber
