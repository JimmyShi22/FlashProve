-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/WrittenShapes.lean: three
shapes of the linear claims are one: the one that the kind K13 reads off the first chain's
parameters as read back ((K13.whereOf Z).lin = Z.first.lin), the last chain's (P2Third.lastPar Z).S
and the shared chain's (p14Of Z.p.chains bp).par.S, both of which are the sized proof's batch's
shape. Statements with their proofs: calls of two fields of Written Z x
(Johnson/Goal/Numbers/WrittenAtZ.lean), and unfolding. A law file; no running text imports it.
  lin_last_of_written: (K13.whereOf Z).lin = (P2Third.lastPar Z).S, where the equations Written Z x
      hold: it is NOT by unfolding at a letter Z: one side is read back from parameter bytes, the
      other is the planner's sized value
  last_shared: (P2Third.lastPar Z).S = (p14Of Z.p.chains bp).par.S: by unfolding, at every Z and bp
  lin_shared_of_written: so the first and the third

What is not claimed. Written Z x at a seat: written_in_scope (WrittenInScope.lean beside this
file), under the door's pin. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.WrittenAtZ
import Johnson.Desc.ProofFile.Lot.LastChainFour

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params

/-- **K13's shape of the linear claims is the last chain's.** -/
theorem lin_last_of_written {Z : ProofFile.Pub} {x : LinSized} (W : Written Z x) :
    (VerifiableInference.Desc.K13.whereOf Z).lin = (P2Third.lastPar Z).S :=
  W.lin.trans W.shape.symm

/-- **The last chain's is the shared chain's.** -/
theorem last_shared (Z : ProofFile.Pub) (bp : List (Nat × Nat)) :
    (P2Third.lastPar Z).S = (p14Of Z.p.chains bp).par.S := rfl

theorem lin_shared_of_written {Z : ProofFile.Pub} {x : LinSized} (W : Written Z x)
    (bp : List (Nat × Nat)) :
    (VerifiableInference.Desc.K13.whereOf Z).lin = (p14Of Z.p.chains bp).par.S :=
  (lin_last_of_written W).trans (last_shared Z bp)

end Desc.K14.Law

#print axioms Desc.K14.Law.lin_last_of_written
#print axioms Desc.K14.Law.last_shared
#print axioms Desc.K14.Law.lin_shared_of_written
