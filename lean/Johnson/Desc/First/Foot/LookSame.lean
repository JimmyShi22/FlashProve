-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Foot/LookSame.lean: what the lookups' four public tests on the verifier's state
read of it: k3OnIn and k3OnOut (Johnson/Desc/First/Look/K3Borders.lean), lookInC and lookOutC
(Johnson/Desc/First/Look/K3FillCode.lean). Two states that agree in what a test reads get one answer
from it. Statements and proofs. No Mathlib.

What for. The kind-free rule for what passes a place (Johnson/Desc/First/PubFoot.lean) books a
public item where a sub-protocol leaves what the item's test reads. For these four that is:
  heardAt_same    what was heard at the seat: the approximate range proof's parameters (tl?) and
                  what the lookup on the calls heard (lookHeard?)
  k3OnIn_same     these two, the rows that are owed (rowsOwed) and the ledger (fork?)
  k3OnOut_same    these two and the ledger
  lookInC_same    what k3OnIn reads, and the open segment's link context (link?)
  lookOutC_same   what k3OnOut reads

Can the premises be met? At s' := s by rfl; and at every sub-protocol that writes none of these five
readers.
Limits. Nothing on which sub-protocol leaves them. Nothing on soundness.

-/
import Johnson.Desc.First.Look.K3FillCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3

theorem heardAt_same (digits : Bool) {s s' : First.S} (e1 : s'.tl? = s.tl?)
    (e2 : s'.lookHeard? = s.lookHeard?) : heardAt digits s' = heardAt digits s := by
  unfold heardAt
  rw [e1, e2]

theorem k3OnIn_same (p : First.Look.P) {s s' : First.S} (e1 : s'.tl? = s.tl?)
    (e2 : s'.lookHeard? = s.lookHeard?) (e3 : s'.rowsOwed = s.rowsOwed)
    (e4 : s'.fork? = s.fork?) : k3OnIn p s' = k3OnIn p s := by
  unfold k3OnIn
  rw [heardAt_same p.digits e1 e2, e3, e4]

theorem k3OnOut_same (p : First.Look.P) {s s' : First.S} (e1 : s'.tl? = s.tl?)
    (e2 : s'.lookHeard? = s.lookHeard?) (e4 : s'.fork? = s.fork?) :
    k3OnOut p s' = k3OnOut p s := by
  unfold k3OnOut
  rw [heardAt_same p.digits e1 e2, e4]

end VerifiableInference.Desc.K3

namespace VerifiableInference.Desc.First.Look

theorem lookInC_same (d : K3Data) (m : Nat) (dg : Bool) {s s' : First.S} (e1 : s'.tl? = s.tl?)
    (e2 : s'.lookHeard? = s.lookHeard?) (e3 : s'.rowsOwed = s.rowsOwed)
    (e4 : s'.fork? = s.fork?) (e5 : s'.link? = s.link?) : lookInC d m dg s' = lookInC d m dg s := by
  unfold lookInC
  simp only [Desc.K3.k3OnIn_same _ e1 e2 e3 e4, e5]

theorem lookOutC_same (d : K3Data) (m : Nat) (dg : Bool) {s s' : First.S} (e1 : s'.tl? = s.tl?)
    (e2 : s'.lookHeard? = s.lookHeard?) (e4 : s'.fork? = s.fork?) :
    lookOutC d m dg s' = lookOutC d m dg s := by
  unfold lookOutC
  simp only [Desc.K3.k3OnOut_same _ e1 e2 e4]

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.K3.heardAt_same
#print axioms VerifiableInference.Desc.K3.k3OnIn_same
#print axioms VerifiableInference.Desc.K3.k3OnOut_same
#print axioms VerifiableInference.Desc.First.Look.lookInC_same
#print axioms VerifiableInference.Desc.First.Look.lookOutC_same
