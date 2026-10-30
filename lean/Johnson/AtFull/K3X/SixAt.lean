-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/SixAt.lean: what the two lookups of ONE link of the proof's first chain ask of
the public data, as one Lean structure of six statements; and that these six give the comparison
with code at that link. Definitions and short laws; one small closed fact by Lean's kernel, on
written values alone.

Why. The six hypotheses on the public data (ReadsX, Johnson/AtFull/Desc/Lots/K3RowX.lean) each speak
of all 25 links. They are paid link by link, on three roads: the layers' links, the attention's
links and the output head's link. This structure is the common form in which each road hands in its
links. It stands over the light file of the comparison (Johnson/AtFull/Desc/Lots/K3Light.lean), so
that a file which pays one link does not load the heavy closed facts of the lookups' rows.

  `SixAt X i`: at link i: the view of the lookup on the calls (its tables taken out) and of the
    lookup on the digits are the written ones; at both lookups the host's count of padding places is
    the written list, the test on the padding key passes, and a step without a round stands behind
    just where the written table says; the caller's readers are there just where it says.
  `same_written`: [Lean's kernel] the comparison with code of two views accepts each written view
    against itself: no written call has a table.
  `SixAt.test`: SixAt X i, i < 25 ⊢ Light.readsAt X i = true.
  `test_of_six`: from all 25: Light.readsB X = true.

Limits. Light.readsAt and Light.readsB are this library's comparison with written values: the
verifier does not ask them. That the six hold at any public data is not said here. Nothing on
soundness.

-/
import Johnson.AtFull.Desc.Lots.K3Light

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.K3X

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.K3 (quietAt)
open VerifiableInference.Desc.First.Look (lookAt laidAt padKeyAt)
open Johnson.AtFull.Lots.K3 (pubW sortOf quietW callerW)
open Johnson.AtFull.Lots.K3.Light (viewOf viewW sameView readsAt readsB)

/-- **The six, at one link.** -/
structure SixAt (X : Verify.Public) (i : Nat) : Prop where
  calls : ∃ x, lookAt X i false = some x ∧ viewOf true x = viewW i false
  digits : ∃ x, lookAt X i true = some x ∧ viewOf false x = viewW i true
  laid : ∀ d, laidAt X i d = some (pubW (sortOf i) d)
  key : ∀ d, padKeyAt X i d = some true
  quiet : ∀ d, (quietAt X i d).isSome = quietW i d
  caller : (K3Lot.readersAt X i).isSome = callerW i

set_option maxRecDepth 100000 in
/-- The comparison with code accepts each written view against itself. -/
theorem same_written : ((List.range 25).all fun i => [false, true].all fun d =>
    sameView (viewW i d) (viewW i d)) = true := by decide +kernel

theorem same_at {i : Nat} (hi : i < 25) (d : Bool) : sameView (viewW i d) (viewW i d) = true :=
  List.all_eq_true.1 (List.all_eq_true.1 same_written i (List.mem_range.2 hi)) d
    (by cases d <;> simp)

/-- **The six give the comparison with code at the link.** -/
theorem SixAt.test {X : Verify.Public} {i : Nat} (h : SixAt X i) (hi : i < 25) :
    readsAt X i = true := by
  obtain ⟨x, hx, vx⟩ := h.calls
  obtain ⟨z, hz, vz⟩ := h.digits
  unfold readsAt
  rw [hx, hz, h.caller]
  simp only [Option.any_some, vx, vz, same_at hi, h.laid, h.key, h.quiet, List.all_cons,
    List.all_nil, beq_self_eq_true, Bool.and_self]

/-- From all 25 links: the whole comparison. -/
theorem test_of_six {X : Verify.Public} (h : ∀ i, i < 25 → SixAt X i) : readsB X = true :=
  List.all_eq_true.2 fun i hi => (h i (List.mem_range.1 hi)).test (List.mem_range.1 hi)

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.same_written
#print axioms Johnson.AtFull.K3X.same_at
#print axioms Johnson.AtFull.K3X.SixAt.test
#print axioms Johnson.AtFull.K3X.test_of_six
