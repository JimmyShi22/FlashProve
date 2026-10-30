-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.P5J.PlacesPaid
import Johnson.P5J.AtMg
/-
Johnson/Loose/H2K12/PlacesAtMg.lean:
THE PLACES OF THE PROOF FILE's FIRST CHAIN's SUB-PROTOCOLS ARE THE TABLE's WRITTEN LIST,
under the head AtMg (Johnson/P5J/AtMg.lean) at the format's second hash function. One theorem.
THE PROOF IS
places_paid (Johnson/P5J/PlacesPaid.lean: in scope, where the files are read and the
value is laid: blockPlaces cF.blocksInOrder = At.ps), called at the head's three fields;
blockPlaces bs is bs.map (·.place) by its text (Johnson/Desc/First/NumbersAtBlocks.lean).






  places_at_mg     cF.blocksInOrder.map (·.place) = At.ps
What for: it pays the premise "the flat list's places are the written list" of k12_kind_at_mg
(H2K12/K12KindAtMg.lean).
Limits. A place is a label: nothing is said on what a sub-protocol does. Whether AtMg can be met at
the release's own files is not shown in Lean. The full size alone. No soundness statement. Nothing
on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

/-- **The places of the first chain's flat list are the table's written list.** -/
theorem places_at_mg {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) : cF.blocksInOrder.map (·.place) = P5J.At.ps :=
  P5J.At.places_paid h.scope h.reads h.laid

end H2K12

#print axioms H2K12.places_at_mg
