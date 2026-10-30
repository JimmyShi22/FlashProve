-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Tie/HashOfEvery.lean: every hash function of the goals is `hashOf O` for a function O
from bytes to 32 bytes.
`hashOf_eq`: `hashOf O` is `Run.oBitsAt O ()`. `hashOf_oOf`: at `Run.oOf` of a hash
function it is that hash function (Run/OracleBitsAtLaws.lean: `toBytes` is one-to-one, and `oOf`
undoes it by choice). `forall_hashOf32`: so a property holds of `hashOf O` at every O with 32-byte
answers exactly if it holds of every hash function.
Why. The laws of Johnson/Goal/Tie and Johnson/Goal/Description speak of a value at `hashOf O`; the
goals draw a hash function on bit strings.
Limits. `Run.oOf` has no code. Nothing on any distribution: that `oOf h` is uniform where h is, is
not said. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.FastFamProbe
import Run.OracleBitsAtLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles

theorem hashOf_eq (O : ByteArray → ByteArray) : hashOf O = _root_.Run.oBitsAt O () := rfl

/-- **Every hash function is `hashOf` of a function on bytes.** -/
theorem hashOf_oOf (h : Hash) : hashOf (_root_.Run.oOf fun _ => h) = h := by
  rw [hashOf_eq, _root_.Run.oBitsAt_oOf]

/-- "At every O with 32-byte answers" and "at every hash function" are one. -/
theorem forall_hashOf32 (p : Hash → Prop) :
    (∀ O : ByteArray → ByteArray, (∀ b, (O b).size = 32) → p (hashOf O)) ↔ ∀ h, p h :=
  ⟨fun H h => hashOf_oOf h ▸ H _ (_root_.Run.size_oOf _), fun H _ _ => H _⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hashOf_oOf
#print axioms VerifiableInference.OnPublicFiles.forall_hashOf32
