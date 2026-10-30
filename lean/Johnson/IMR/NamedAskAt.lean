-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/NamedAskAt.lean (no file of this library imports it): THE LAW THAT THE ROW namedAt
(Johnson/Goal/Meaning/NamedAsk.lean) SERVES, AT THE VERY PUBLIC
PART OF WHICH THE IOP AS WRITTEN IN LEAN IS MADE: at the full size's shape a yes of the row gives
the fence Meaning.laidThere at the plan's own public parameters, the library's own sizes and the
layout of the request that the IOP reads. At every o; no scope.

Compiled with the whole library.


  laidThere_of_at   ProofFile.pureRoad.pub o pol ly KL = ok Z, fullShaped Z.p.X = true, namedAt Z = true
    give Meaning.laidThere Z.p.X (Meaning.sizesOf Z.p.X) Z.first.layout = true: by pub_layoutOk
    (Johnson/IMR/LayoutOkPub.lean: the programs' own test on the layout has been asked where Z is
    made), named_of_B (Johnson/Goal/Meaning/NamedAskLaw.lean) and Meaning.laidThere_of_named
    (Johnson/Goal/Meaning/LaidCovered.lean).

OBJECT: ProofFile.pureRoad.pub's value; Meaning.laidThere (Johnson/Goal/Meaning/HidSeatsOf.lean). USER:
none in Lean yet; meant: the laws that take laidThere … = true as a premise. LETTERS: o and the
three files: free.

WHAT IS LEFT TO THE SPENDER. That its X and its layout are Z.p.X and Z.first.layout. The bare row's
yes off the door's guarded one: in scope the door's guard (the full size's key) holds: the door's
own lemma. fullShaped in scope: fullShaped_scope, once Z.p.X is known to be what publicOf returns.
No soundness.
-/
import Johnson.Goal.Meaning.NamedAskLaw
import Johnson.IMR.LayoutOkPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.NamedAsk

open OnBytes OnBytes.Model
open ProofFile (Pub)

/-- **THE LAW THAT THE ROW SERVES**: at the very public part of which the IOP as written in Lean is
made, at the full size's shape: a yes of the bare row gives the fence laidThere. -/
theorem laidThere_of_at {o : ProofFile.SecondHashFunctionArgument} {pol ly KL : ByteArray} {Z : Pub}
    (h : ProofFile.pureRoad.pub o pol ly KL = .ok Z) (hF : fullShaped Z.p.X = true)
    (T : namedAt Z = true) :
    Meaning.laidThere Z.p.X (Meaning.sizesOf Z.p.X) Z.first.layout = true :=
  Meaning.laidThere_of_named (Meaning.K2.pub_layoutOk h) (named_of_B hF T)

#print axioms laidThere_of_at

end Meaning.NamedAsk
