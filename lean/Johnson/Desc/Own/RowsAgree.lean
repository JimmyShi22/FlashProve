-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/RowsAgree.lean: the description's own tests on a row's summands
(Johnson/Desc/Own/Rows.lean) say just what the hand-written program's say, at all arguments.
  tableThere_agrees     OnBytes.Statement.has (OnBytes/Iop/Ground.lean)
  placeFits_agrees      OnBytes.Blk.placeOk (OnBytes/Iop/Ground.lean)
  coeffsInside_agrees   OnBytes.Coeffs.ok (OnBytes/Iop/Ground.lean)
  allZero_agrees        OnBytes.isZeroE (OnBytes/Field/Ext.lean)
A YARDSTICK BESIDE: no block imports this file. It says nothing on whether the tests ask enough.
No soundness is claimed.
-/
import Johnson.Desc.Own.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own

theorem tableThere_agrees (S : OnBytes.Statement) (o : Nat) (part : OnBytes.Part) :
    S.has o part = tableThere S o part := by
  unfold OnBytes.Statement.has tableThere
  cases S.oracles[o]? <;> rfl

theorem placeFits_agrees (S : OnBytes.Statement) (G : OnBytes.Group) (o : Nat)
    (part : OnBytes.Part) (vars index : Nat) :
    OnBytes.Blk.placeOk S G o part vars index = placeFits S G o part vars index := by
  unfold OnBytes.Blk.placeOk placeFits
  rw [tableThere_agrees]

theorem coeffsInside_agrees (c : OnBytes.Coeffs) : c.ok = coeffsInside c := by
  cases c <;> rfl

theorem allZero_agrees (a : OnBytes.E) : OnBytes.isZeroE a = allZero a := rfl

end VerifiableInference.Desc.Own

#print axioms VerifiableInference.Desc.Own.tableThere_agrees
#print axioms VerifiableInference.Desc.Own.placeFits_agrees
#print axioms VerifiableInference.Desc.Own.coeffsInside_agrees
#print axioms VerifiableInference.Desc.Own.allZero_agrees
