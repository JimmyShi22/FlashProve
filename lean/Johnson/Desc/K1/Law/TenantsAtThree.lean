--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/TenantsAtThree.lean: THE SECOND HALF OF `seatsIn_written`
(Johnson/Desc/K1/Law/RadiiAtTwo.lean: each tenant at the border behind the first segment's opening
sits at a seat of a sampled message of that place) IS NOT TRUE FOR WANT OF A CASE: the list of
tenants at border 3, at the written numbers, has four members. On a reader's ask. Statements with
their proofs: closed facts by Lean's kernel, looked at with the evaluator first.

  `tenants_three`   BY LEAN's KERNEL: the list, written out: (0, 0), (0, 1), (0, 2), (1, 0)
  `tenants_three_ne`   so it is not empty
  `tenants_two_none`   the like sentence can fail: at border 2, in front of that place, the list is
      empty (by the evaluator it is empty at the borders 0, 1 and 2 and at no other of the 359)

What is not claimed. Nothing on any other border by a theorem. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.RadiiAtTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1

open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.First (flatPlacesOf)
open VerifiableInference.Desc.K13.Law (openAt)
open P5T (N0Full)

set_option maxRecDepth 1000000 in
theorem tenants_three :
    First.sampledIn N0Full (openAt linksFull (flatPlacesOf linksFull true) (2 + 1)) =
      [(0, 0), (0, 1), (0, 2), (1, 0)] := by
  decide +kernel

theorem tenants_three_ne :
    First.sampledIn N0Full (openAt linksFull (flatPlacesOf linksFull true) (2 + 1)) ≠ [] := by
  rw [tenants_three]
  exact List.cons_ne_nil _ _

set_option maxRecDepth 1000000 in
/-- The like sentence can fail. -/
theorem tenants_two_none :
    First.sampledIn N0Full (openAt linksFull (flatPlacesOf linksFull true) 2) = [] := by
  decide +kernel

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.tenants_three
#print axioms VerifiableInference.Desc.K1.tenants_three_ne
#print axioms VerifiableInference.Desc.K1.tenants_two_none
