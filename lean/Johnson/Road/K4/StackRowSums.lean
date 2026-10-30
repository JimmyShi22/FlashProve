-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StackRowSums.lean: the library's summand of the batched sumcheck of a layers'
sub-proof, on values of its end values, is a product of two sums. No letter of a verifier's text
occurs.

The library's summand of the batched sumcheck on values v of its end values (LdPartSm.pol,
Cb/Part/LdPartPsc.lean, at the terms of Cb/Pv/Lay/At/Sides.lean) has one term for each pair of a
part of the first side and a part of the second.

Main names:
  `inn_pol`: the summand is the product of two sums, one for each side. General in InnPar.
Limits. An identity on finite sums. Nothing on a run, on soundness or on hiding.


-/
import Cb.Pv.Lay.At.InnerSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset
open Cb Cb.Pv.Lay Cb.Pv.Lay.At

/-- The library's summand of a sumcheck of two sides, on values v of the parts' maps: the product of
the two sides' sums. -/
theorem inn_pol {E' : Type} [Field E'] [Fintype E'] (P : InnPar E') (st : P.St)
    (z : Fin P.k → E') (v : P.a.I ⊕ P.b.I → E') :
    P.inn.Sm.pol st z v =
      (∑ i, P.a.c i st z * v (.inl i)) * ∑ j, P.b.c j st z * v (.inr j) := by
  unfold LdPartSm.pol
  show (((Finset.univ : Finset (P.a.I × P.b.I)).toList.map P.term).map _).sum = _
  rw [List.map_map, Finset.sum_map_toList, Finset.sum_mul_sum, ← Finset.univ_product_univ,
    Finset.sum_product]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  show P.a.c i st z * P.b.c j st z * (v (.inl i) * (v (.inr j) * 1)) = _
  ring

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.inn_pol
