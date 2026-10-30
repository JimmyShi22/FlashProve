-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/PlanClosedB.lean: THE PART OF `planPubB` (HFDoorB.lean) THAT READS NO
STATE, AS A TEST OF ITS OWN: so that it can be evaluated, or held by the kernel, at the plan's list
and the description alone. A definition and a theorem. No text already in the library turns.

  `planClosedB G Lp o seat a`: the plan's list has (a tree, the seat's tenant) at o and a shape at
    that tree · the tree is 2 ^ a leaves long · where the description tells the seat's tree, the
    listed shape's two skips in front of the tenant are the description's.
  `planPubB_eq`: planPubB G t Lp o seat a = (decide (o < t.book.place.size) && planClosedB G Lp o
    seat a): by definition.
Limits. A test. Not evaluated here. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.HFDoorB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc (FileDescription)

def planClosedB {Xi : Type} (G : FileDescription Xi) (Lp : VerifiableInference.Desc.K12.Door.Laid)
    (o : ℕ) (seat : ℕ × ℕ) (a : ℕ) : Bool :=
  match Lp.places[o]? with
  | some q => decide (q.2 = seat.2) &&
    match Lp.shapes[q.1]? with
    | some sh0 => decide (sh0.logN = a) &&
      match G.oracleAt seat.1 with
      | some d =>
        decide ((sh0.mainSymbols.extract 0 seat.2).foldl (· + ·) 0 = d.mainSkip seat.2) &&
          decide (sh0.mainWidth + (sh0.maskSymbols.extract 0 seat.2).foldl (· + ·) 0 =
            d.maskSkip seat.2)
      | none => true
    | none => false
  | none => false

theorem planPubB_eq {Xi : Type} (G : FileDescription Xi) (t : First.S)
    (Lp : VerifiableInference.Desc.K12.Door.Laid) (o : ℕ) (seat : ℕ × ℕ) (a : ℕ) :
    planPubB G t Lp o seat a =
      (decide (o < t.book.place.size) && planClosedB G Lp o seat a) := rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.planPubB_eq
