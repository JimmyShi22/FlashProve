-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/FirstW.lean: the key file's first chain at the full size's written values,
with the two lookups' rounds off the planner's plain list; and that it is Key.firstChain at these
values.

Main names.
  lookE x: the entries of lookup x's rounds off the plain list (lookupList, as in the law
  KB8.entriesG_eq).
  looks_return: at both lookups of the full size K3.entriesG returns lookE x: from KB8.entriesG_eq,
  KB8.fit_full and KB8.looks_ok_full.
  firstW: the chain. firstFull_eq: firstFull = firstW.
Limits. At written values alone. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.Chains
import Johnson.HB.LLHARD.KB4.FirstL
import Johnson.HB.LLHARD.KB8.AtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open Lk6.AtPlan (keyFull)
open Johnson.KB8 (declKeyFull rangesNumsFull laterPlacesFull)

/-- The entries of a lookup's rounds off the plain list. -/
def lookE (x : Lookup) : List Fmt.Entry :=
  (lookupList keyFull.set (K3.faceOfLkp x).size).map fun y => (y.round keyFull.set .once).entry

theorem looks_return :
    ∀ x ∈ lookupsOf oneFull, K3.entriesG keyFull.set .once (K3.faceOfLkp x) = some (lookE x) := by
  intro x hx
  have h := Bool.and_eq_true_iff.1 (List.all_eq_true.1 Johnson.KB8.looks_ok_full x hx)
  exact Johnson.KB8.entriesG_eq Johnson.KB8.fit_full h.1 h.2

/-- The first chain, the lookups' rounds off the plain list. -/
def firstW : Chain FirstState Claim :=
  firstChainL (lookLinks lookE oneFull keyFull.set) oneFull declKeyFull.1 toldKeyFull.1
    rangesNumsFull

theorem firstFull_eq : firstFull = firstW :=
  firstChain_look looks_return declKeyFull.1 toldKeyFull.1 rangesNumsFull

end Johnson.KB4

#print axioms Johnson.KB4.looks_return
#print axioms Johnson.KB4.firstFull_eq
