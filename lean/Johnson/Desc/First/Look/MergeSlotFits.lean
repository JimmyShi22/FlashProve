-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/MergeSlotFits.lean: A TEST WITH CODE ON THE VERIFIER's STATE: THE SLOT OF
THE MERGE's END VALUE (K9.mergeOf, Johnson/Desc/First/Batch/AtS.lean) LIES BELOW THE OPEN LEDGER's
NEXT SLOT. With a bent input for a negative test. Two definitions and three small theorems; no
Mathlib.

OBJECT: no text that runs in the verifier: a Bool and a function on First.S.
Used by MergeSlotFitsLaw.lean (Johnson/Top/H/Keep/) · K3DigitsFormsJoin.lean, K3DigitsJoinIt.lean
  (Johnson/Desc/Sound/MgAt/) and 8 more.
LETTERS: s.

Main names:
  sFvFitsB s: where the merge has a slot j: a ledger F is open and j < F.next; true where the merge
    has no slot.
  sFvBent s: s with the merge's slot turned to the ledger's next slot; s itself where the merge has
    no slot.
  sFvFits_bent_lay, sFvFits_bent_head: at the bent state the test says false. sFvFits_none: where
    the merge has no slot it says true.

WHAT THE ONE CLAUSE SERVES. A lookup's hearing fills slots from the ledger's next slot on; the
forms that it keeps are to name none below. So j < F.next in front keeps j apart from every slot
that these forms name. NOT ASKED: THAT THE SLOT j IS FREE IN THE LEDGER: IT IS FILLED: the merge
reads what was shown under it (OnBytes/Model/Merge.lean: SubM.shown sFv), which refuses at a free
slot.

Limits. Nothing is shown on any reached state. Whether the test says true at an honest run's states
is for an evaluation.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Batch.AtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (mergeOf)

/-- **The merge's slot lies below the open ledger's next slot.** Where the merge has a slot j: a
ledger F is open and j < F.next. True where the merge has no slot. -/
def sFvFitsB (s : S) : Bool :=
  match mergeOf s with
  | some j => s.fork?.any fun F => decide (j < F.next)
  | none => true

/-- A bent input: the merge's slot turned to the ledger's next slot. -/
def sFvBent (s : S) : S :=
  match s.here with
  | .lay a =>
    match a.own with
    | some o =>
      { s with here := .lay { a with own := some { o with wo := { o.wo with sFv := a.F.next } } } }
    | none => s
  | .head a =>
    match a.wo with
    | some w => { s with here := .head { a with wo := some { w with sFv := a.F.next } } }
    | none => s
  | _ => s

theorem sFvFits_none {s : S} (h : mergeOf s = none) : sFvFitsB s = true := by
  unfold sFvFitsB
  rw [h]

/-- At the bent state of a layers' link the test says false. -/
theorem sFvFits_bent_lay {s : S} {a : First.LayOwn} {o : Layer.Own} (hs : s.here = .lay a)
    (ho : a.own = some o) : sFvFitsB (sFvBent s) = false := by
  simp [sFvFitsB, sFvBent, mergeOf, S.fork?, hs, ho]

/-- At the bent state of the head's link, once it is opened, the test says false. -/
theorem sFvFits_bent_head {s : S} {a : First.HeadOwn} {w : WsForkOut} (hs : s.here = .head a)
    (hw : a.wo = some w) (hop : a.opened = true) : sFvFitsB (sFvBent s) = false := by
  simp [sFvFitsB, sFvBent, mergeOf, S.fork?, hs, hw, hop]

end VerifiableInference.Desc.K3

#print axioms VerifiableInference.Desc.K3.sFvFits_none
#print axioms VerifiableInference.Desc.K3.sFvFits_bent_lay
#print axioms VerifiableInference.Desc.K3.sFvFits_bent_head
