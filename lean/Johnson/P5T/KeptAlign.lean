-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5T/KeptAlign.lean: THE WITNESS's NUMBERING GIVES THE TWO COPIES OF A KEPT ORACLE MESSAGE
ONE NUMBER: what lies by the make, and a named test with code for the rest. One definition, two
theorems. It names no Mathlib.

Why. A code switching into group l + 1 sends each kept oracle message anew. A law on that
sub-protocol wants: by place a, the number of the old copy's (tree, tenant) ((N.keptOf l)[a]) is the
number of the new copy's (the member 1 + a of link l + 1's first sending: (N.sent (l + 1) 0)[1 + a];
the carried message stands in front).
  `arrOf_same_key`: BY THE MAKE: two (tree, tenant)s whose first entries have one key have one
    number (`arrOf`, `keyOf`: Johnson/P5T/PlanSeats.lean).
  `keptAlignB arr N n`: THE NAMED TEST: at every l below n and every place a of N.keptOf l: there is
    a member 1 + a of N.sent (l + 1) 0, and arr gives the two one number.
  `keptAlign_at`: the test's acceptance, by l and a.
WHY A TEST: `numbersOf` (Johnson/P5T/NumbersOf.lean) lists the old copies in the entries' order in
their group; the new copies stand in the order of the group's list of what it keeps. That the two
orders are one is given by no make.

Limits. The test reads arr and N alone: at the composed meaning's terms: the public part's sendings
and declared rounds. Nothing on soundness.

-/
import Johnson.P5T.NumOfPlan
import Johnson.P5T.NumbersOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open VerifiableInference.Desc.First (Numbers)

/-- **Two (tree, tenant)s whose first entries have one key have one number.** -/
theorem arrOf_same_key (ps : List PSeat) (j t j' t' : Nat) (p p' : PSeat)
    (h : (ps.find? fun p => p.j == j && p.t == t) = some p)
    (h' : (ps.find? fun p => p.j == j' && p.t == t') = some p') (hk : keyOf p = keyOf p') :
    arrOf ps j t = arrOf ps j' t' := by
  rw [arrOf_of_find ps j t p h, arrOf_of_find ps j' t' p' h', hk]

/-- **By place, the old and the new copy of a kept oracle message have one number.** -/
def keptAlignB (arr : Nat → Nat → Nat) (N : Numbers) (n : Nat) : Bool :=
  (List.range n).all fun l => (List.range (N.keptOf l).length).all fun a =>
    match (N.keptOf l)[a]?, (N.sent (l + 1) 0)[1 + a]? with
    | some o, some w => arr o.1 o.2 == arr w.1 w.2
    | _, _ => false

theorem keptAlign_at (arr : Nat → Nat → Nat) (N : Numbers) (n : Nat)
    (h : keptAlignB arr N n = true) (l : Nat) (hl : l < n) (a : Nat) (o : Nat × Nat)
    (ho : (N.keptOf l)[a]? = some o) :
    ∃ w, (N.sent (l + 1) 0)[1 + a]? = some w ∧ arr o.1 o.2 = arr w.1 w.2 := by
  have ha : a < (N.keptOf l).length := (List.getElem?_eq_some_iff.1 ho).1
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h l (List.mem_range.2 hl)) a
    (List.mem_range.2 ha)
  rw [ho] at h1
  cases hw : (N.sent (l + 1) 0)[1 + a]? with
  | none =>
    rw [hw] at h1
    cases h1
  | some w =>
    rw [hw] at h1
    exact ⟨w, rfl, by simpa using h1⟩

end P5T

#print axioms P5T.arrOf_same_key
#print axioms P5T.keptAlign_at
