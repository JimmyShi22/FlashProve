-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Foot/FormsSame.lean: what four public tests on the verifier's state read of it:
formsIn, formsInT, formsInA and totalIn (Johnson/Desc/First/Batch/FormsIn.lean and Ahead.lean). Two
states that agree in what a test reads get one answer from it. Statements and proofs.

What for. The kind-free rule for what passes a place (Johnson/Desc/First/PubFoot.lean) books a
public item where a sub-protocol leaves what the item's test reads. For these four tests that is:
  formsIn_same | formsInT_same | formsInA_same
                  the open segment's part (segAt?), the named run's reader's answer (Rd.forms piece
                  run) and the slot whose scalar is masked elsewhere (mergeOf)
  totalIn_same    kind K9's lens (atS.get?)
formsInA stands in Ahead.lean, so that file is imported; it reads of the state the same three as
formsIn and nothing more.

Can the premises be met? At s' := s by rfl; and at every sub-protocol that leaves these readers.
Limits. Nothing on which sub-protocol leaves them. Nothing on soundness.

-/
import Johnson.Desc.First.Batch.Ahead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open VerifiableInference.Desc.First (S)

section
variable (Rd : Readers) (sent : Nat → List (Nat × Nat)) (own : List (Nat × Nat)) (piece : Nat)
  (run : String) {s s' : S}

theorem formsIn_same (e1 : segAt? s' = segAt? s) (e2 : Rd.forms piece run s' = Rd.forms piece run s)
    (e3 : mergeOf s' = mergeOf s) : formsIn Rd own piece run s' = formsIn Rd own piece run s := by
  unfold formsIn
  rw [e1, e2, e3]

theorem formsInT_same (e1 : segAt? s' = segAt? s)
    (e2 : Rd.forms piece run s' = Rd.forms piece run s) (e3 : mergeOf s' = mergeOf s) :
    formsInT Rd own piece run s' = formsInT Rd own piece run s := by
  unfold formsInT
  rw [e1, e2, e3]

theorem formsInA_same (e1 : segAt? s' = segAt? s)
    (e2 : Rd.forms piece run s' = Rd.forms piece run s) (e3 : mergeOf s' = mergeOf s) :
    formsInA Rd sent own piece run s' = formsInA Rd sent own piece run s := by
  unfold formsInA
  rw [e1, e2, e3]

theorem totalIn_same (e : atS.get? s' = atS.get? s) : totalIn own s' = totalIn own s := by
  unfold totalIn
  rw [e]

end

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.formsIn_same
#print axioms VerifiableInference.Desc.K9.formsInT_same
#print axioms VerifiableInference.Desc.K9.formsInA_same
#print axioms VerifiableInference.Desc.K9.totalIn_same
