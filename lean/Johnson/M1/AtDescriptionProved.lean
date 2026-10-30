-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- the clause at the description, proved.
/-
Johnson/M1/AtDescriptionProved.lean: `sameRounds`, and `atDescription` from the count. No property of
the protocol is claimed here.
-/
import Johnson.M1.AtDescription
import Johnson.M1.NumbersProved
import Johnson.M1.Rows

set_option autoImplicit false

namespace OnBytes.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At OnBytes.SendSim.Seat

theorem sameRounds : Spec.sameRounds := rfl

theorem atDescription : Spec.atDescription := by
  intro P hS hL F Z Bs base c A B O i hi
  refine OnBytes.SendSim.Seat.readsWithinOf _ F _ _ ?_
  rw [readsWithinB_tab, Johnson.M1.decl_of_live hS hL O, ← sameRounds]
  have h := count.2.2.1
  exact (Bool.and_eq_true_iff.1 (List.all_eq_true.1 h i (List.mem_range.2 hi))).2

end OnBytes.M1

#print axioms OnBytes.M1.sameRounds
#print axioms OnBytes.M1.atDescription
