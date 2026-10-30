-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeRider.lean: the honest side of the kind "lookup"
(K3): WHAT THE LOOKUP'S ROW OWES BEHIND ITS SUB-PROTOCOL: the row out's fourth item, on the caller's
riders. Theorems with proofs; no definition.

The fourth item (`K3OutRider`, Johnson/Top/H/K3RowOutRider.lean) says: the multilinear extension of
each of the caller's arrays is 0 at its own places of the lookup's key point. It names no form, no
slot and no value that was heard but that point. On the honest side it follows from what stands IN
FRONT of the lookup: each array is 0 at every vertex of its cube (`OnCubes`,
Cb/G6/Rider/Carrier.lean), so its extension is 0 at every point.

  `atCoords_of_onCubes`   arrays that are 0 on their cubes have extensions that are 0 at all
                          coordinates of all points: general in the family
  `outRider_of_onCubes`   CONDITIONAL ON `OnCubes` of the caller's family: the fourth item, at every
                          heard structure and every ledger
  `worthRider_of_onCubes`  the same as the item worth "rider" of Johnson/Top/H/K3Worth.lean,
                           at every state of the verifier

It leans on `Blocks.ext_zero_of_forall` (Blocks/Ext.lean).

Limits. That `OnCubes` holds of an honest witness's messages is not shown: it is what the item in
front (the caller's identity on its cube) says; who reads it off that item is not settled. No
instance of these hypotheses is exhibited in this file. Nothing on any property.
-/
import Johnson.Top.H.K3Worth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes.Model (Fork)
open Cb.Rider (OnCubes AtCoords)
open VerifiableInference.OnPublicFiles (K3OutRider K3WorthRider LookupCRCaller)

/-- **Arrays that are 0 on their cubes have extensions that are 0 at all coordinates
of all points.** -/
theorem atCoords_of_onCubes {E : Type} [Field E] [Fintype E] {St M ι : Type} (g : ι → Nat)
    (sel : ι → Nat → Nat) (f : ι → St → M → Nat → E) (st : St) (m : M) (h : OnCubes g f st m)
    (pt : Nat → E) : AtCoords g sel f st pt m :=
  fun i => Blocks.ext_zero_of_forall (h i) _

/-- **CONDITIONAL ON `OnCubes` of the caller's family: the row out's fourth item**, at every
heard structure and every ledger. No instance of these hypotheses is exhibited in this file. -/
theorem outRider_of_onCubes (r : LookupCRCaller) (lm first : Nat) (st : r.c.St₀) (m : r.c.Sg.Msg)
    (h : OnCubes r.g r.f st m) (g : OnBytes.Model.Forest.Heard) (F' : Fork) :
    K3OutRider r lm first st m g F' :=
  fun _ _ => atCoords_of_onCubes r.g r.sel r.f st m h _

/-- **CONDITIONAL ON `OnCubes` at the caller's state and the witness's messages: the item worth
"rider".** No instance of these hypotheses is exhibited in this file. -/
theorem worthRider_of_onCubes {S W : Type} (fork : S → Option Fork)
    (heard : S → Option OnBytes.Model.Forest.Heard) (r : LookupCRCaller) (lm first : Nat)
    (st : S → r.c.St₀) (ms : W → r.c.Sg.Msg) (s : S) (w : W) (h : OnCubes r.g r.f (st s) (ms w)) :
    K3WorthRider fork heard r lm first st ms s w :=
  fun g F' _ _ => outRider_of_onCubes r lm first (st s) (ms w) h g F'

#print axioms ProofFile.Honest.K3.Law.Exchange.atCoords_of_onCubes
#print axioms ProofFile.Honest.K3.Law.Exchange.outRider_of_onCubes
#print axioms ProofFile.Honest.K3.Law.Exchange.worthRider_of_onCubes

end ProofFile.Honest.K3.Law.Exchange
