-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/LookKindAgrees.lean: A PLACE OF THE KIND "LOOKUP" MAKES ITS SHAPE, AND TESTS
ITS PLAN, AS IT DID WHILE IT CALLED THE VERIFIER PROGRAM'S FUNCTIONS. Theorems alone. Without
Mathlib.

Why. `P.shape` and `P.planOk` (Johnson/Desc/First/Look/LookKind.lean) are typed over the
description's own `shapeOwn`, `pubOk` and `planesOk`. The same two can be written with
`Forest.shape`, `Forest.pubAsk` and `Forest.planeCols` (OnBytes/Model/Forest.lean). A proof that
unfolds to those rewrites by the first or the third equation here and goes on.

Main theorems:
  **`P.shape_older`**: `p.shape` is the value through `Forest.shape`, at every place.
  `P.shape_made`: where a place has a shape, the program's two public tests have passed, and the
    shape is theirs with the place's numbers of padding keys.
  `P.planOk_older`: `p.planOk laid guests` is the value through `Forest.planeCols`.

Limits: equations of functions: nothing is said of what the numbers mean. No file of the description
imports this one.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.LookKind
import Johnson.Desc.First.Look.ShapeOwnAgrees2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- **The shape of a place is what `Forest.shape` and `Forest.pubAsk` give.** -/
theorem P.shape_older (p : P) : p.shape =
    match Forest.shape p.calls p.lid with
    | .ok h0 => if (Forest.pubAsk h0 p.pub).toBool then some { h0 with pub := p.pub } else none
    | .error _ => none := by
  unfold P.shape
  rw [shapeOwn_eq]
  cases Forest.shape p.calls p.lid with
  | error e => rfl
  | ok h0 =>
    show (if pubOk h0 p.pub = true then some { h0 with pub := p.pub } else none) = _
    rw [pubOk_eq]

/-- Where a place has a shape, the program's two public tests have passed. -/
theorem P.shape_made {p : P} {h : Forest.Shape} (e : p.shape = some h) :
    ∃ h0, Forest.shape p.calls p.lid = .ok h0 ∧ Forest.pubAsk h0 p.pub = .ok () ∧
      h = { h0 with pub := p.pub } := by
  unfold P.shape at e
  cases h0e : shapeOwn p.calls p.lid with
  | none => rw [h0e] at e; cases e
  | some h0 =>
    rw [h0e] at e
    have e' : (if pubOk h0 p.pub = true then some { h0 with pub := p.pub } else none) = some h := e
    split at e'
    · rename_i hb
      cases e'
      exact ⟨h0, shapeOwn_gives h0e, pubOk_gives hb, rfl⟩
    · cases e'

/-- The test on the plan is what `Forest.planeCols` gives. -/
theorem P.planOk_older {S Cl : Type} (p : P) (laid : Array Nat) (guests : List (Guest S Cl)) :
    p.planOk laid guests =
      match p.shape with
      | none => false
      | some h =>
        p.entries.isSome && (Forest.planeCols h p.lm).toBool && decide (1 < h.NC) &&
          decide (p.first + Forest.elems h ≤ p.ns) && laid == p.pub &&
          guests.all (Guest.fits h.dT) := by
  unfold P.planOk
  cases p.shape with
  | none => rfl
  | some h =>
    show (p.entries.isSome && planesOk h p.lm && _ && _ && _ && _) = _
    rw [planesOk_eq]

end VerifiableInference.Desc.First.Look
