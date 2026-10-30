-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/KeptTypedFull.lean: the code switch: A CLOSED FACT ON THE 25 WRITTEN ENTRIES
OF THE FULL SIZE, BY LEAN's KERNEL: at the written front of each typed structure the kept old
messages have the shapes that the structure's list of old members has at its kept numbers. It is the
one closed premise (hty) of `frontSide_of` (FrontSide.lean), which carries it to a real front
through the test `frontB2`'s own clause «the kept old messages' shapes are the written front's».

Main names:
  `keptTypedAtB`, `keptTypedB`: the test, at any front and at the structure's own written front.
  `keptTyped_full`: it accepts at all 25 entries of `tableFullLit`. `keptTyped_at`: the sentence at
    an entry.
  `keptTyped_short`, `keptTyped_other`: two negative tests: the first entry's written front against
    that entry with one kept number less, and against the second entry: the test rejects.
Limits. The written front is made of the typed structure: so the fact says that this make is as
meant; it says nothing of a real front. Bending an entry on both sides cannot fail (tried: the test
accepts). Nothing at the small size. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Hands.FrontsB
import Johnson.Top.H0.K2Caller.LitRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes
open VerifiableInference.Desc.First.K2Hands (keptShapes)
open Johnson.G (fxAt)

/-- **The test, at any front**: the front's kept old messages have, in the order of sending, the
    shapes
that the typed structure's list of old members has at its kept numbers. -/
def keptTypedAtB (x : _root_.Tw.K2.Front) (r : SwRow) : Bool :=
  decide (keptShapes x = r.kept.map fun i => (r.lo[i]?).map (·.1))

/-- The test at the typed structure's own written front. -/
def keptTypedB (r : SwRow) : Bool := keptTypedAtB (fxAt r) r

theorem keptTyped_of {r : SwRow} (h : keptTypedB r = true) :
    keptShapes (fxAt r) = r.kept.map fun i => (r.lo[i]?).map (·.1) := of_decide_eq_true h

/-- **It accepts at all 25 written entries of the full size**: by Lean's kernel. -/
theorem keptTyped_full : tableFullLit.all keptTypedB = true := by decide +kernel

/-- The sentence at an entry of the written table. -/
theorem keptTyped_at {i : ℕ} {r : SwRow} (h : tableFullLit[i]? = some r) :
    keptShapes (fxAt r) = r.kept.map fun i => (r.lo[i]?).map (·.1) :=
  keptTyped_of (List.all_eq_true.1 keptTyped_full r (List.mem_of_getElem? h))

/-- **A negative test**: the first entry's written front against that entry with one kept number
    less:
the test rejects. (Bending the entry on BOTH sides cannot fail: the written front is made of it.) -/
theorem keptTyped_short : (tableFullLit[0]?).map
    (fun r => keptTypedAtB (fxAt r) { r with kept := r.kept.tail }) = some false := by
  decide +kernel

/-- **A second**: the first entry's written front against the second entry: it rejects. -/
theorem keptTyped_other : (tableFullLit[0]?).bind
    (fun r => (tableFullLit[1]?).map fun r' => keptTypedAtB (fxAt r) r') = some false := by
  decide +kernel

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.keptTyped_full
#print axioms VerifiableInference.Desc.First.K2Caller.keptTyped_at
#print axioms VerifiableInference.Desc.First.K2Caller.keptTyped_other
#print axioms VerifiableInference.Desc.First.K2Caller.keptTyped_short
