-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/WalkK8.lean: kind K8's hearing (the draw of the smallness test's matrix) at the
first chain's record carries the ledger and what kind K5 heard (CarK5, Claims/WalkK5.lean): it lays the
smallness test's record alone.

Main name: k8_steps. By the library's general rule k8_whole (Johnson/Goal/Meaning/RecK5K8.lean: a relation that
the seat's laying keeps is kept by K8's hearing), fork_putTl (Johnson/Desc/First/StateLedger.lean) and
heard5_putTl (Claims/WalkK5.lean).
IS IT EMPTY HERE? Where the hearing refuses nothing is said.
Limits. Nothing on K8's runs of claims, which are another text's.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Goal.Meaning.RecK5K8
import Johnson.Desc.First.Att.Claims.WalkK5

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S)
open VerifiableInference.Desc.First (K8.atS K8.approximateRangeProofDrawKind K8.Par)

theorem k8_lay_carries (s : First.S) (m : _) (first : _) (s' : First.S)
    (h : K8.atS.lay s m first = .ok s') : CarK5 s s' := by
  simp only [K8.atS] at h
  split at h
  · injection h with h
    subst h
    exact carK5_same _ _ (First.S.fork_putTl _ _) (heard5_putTl _ _)
  · cases h

/-- **Kind K8's hearing carries.** -/
theorem k8_steps {Cl : Type} (p : K8.Par) : (K8.approximateRangeProofDrawKind (Cl := Cl) K8.atS p).Steps CarK5 :=
  (Meaning.K2.k8_whole CarK5 K8.atS k8_lay_carries p).1

end K5Law

#print axioms K5Law.k8_steps
