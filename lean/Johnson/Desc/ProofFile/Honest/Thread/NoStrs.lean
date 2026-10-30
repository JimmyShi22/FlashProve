-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/NoStrs.lean: THE PROMISE AT A BORDER, AT THE HONEST LETTERS,
READS NO ORACLE STRING: `onAt` (Johnson/Desc/First/Borders.lean) at `honest Mg ans test`
(Honest/Thread/First.lean) is the same sentence at every two values of its last argument. General
in the meaning Mg, the numbers, the links, the place and the open sets. A lemma on the library's
definition and ours.

Why. `onAt` reads the strings at three letters of the meaning alone: `decodes`, `shown`, `noColl`;
the honest letters lay True for all three. So an author's law on the promise that stands at one
value of the strings (at none; at those of a frame) serves at every other.

Limits. It is none of the library's goals. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Place Strs)
open VerifiableInference.Desc.First (S ModelPart Item Numbers Meaning onAt)

/-- **At the honest letters the promise reads no oracle string.** -/
theorem onAt_honest_strs {P Wt : Type} (N : Numbers) (Mg : Meaning P Wt)
    (ans : Nat → Nat → P × S → Strs → Wt → Prop) (test : Nat → S → Option String)
    (links : List ModelPart) (p : Option Place) (O : List Item)
    (Q : List VerifiableInference.Desc.First.Pub) (a : P × S) (y y' : Strs) :
    onAt N (honest Mg ans test) links p O Q a y ↔ onAt N (honest Mg ans test) links p O Q a y' :=
  Iff.rfl

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.onAt_honest_strs
