-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/SwitchTestAccepts.lean: CONDITIONAL, UNDER THE LIBRARY's
HYPOTHESIS h ON THE PUBLIC FILES: THE PUBLIC TEST OF THE KIND "THE CODE SWITCH" ON AN INSTANCE
(publicOk, Honest/K2/Sim.lean) ACCEPTS AT EVERY WRITTEN PLACE OF THE KIND, AT THE HONEST FILLING's
OWN DATA OF THE MAIN ROWS AND LAYOUT, WHEREVER THE DESCRIPTION's OWN TEST ON THE INSTANCE ACCEPTS.
One theorem: three calls of laws that the library has, joined.

WHAT IT IS NOT. It says nothing on what the data hold, and not that the sender plays: publicOk asks
that each own message in front of the place has an address and that each array which the layout lays
into it is laid by the data; and, of each message of the switch's own sending but the last, that its
arrays are laid and that its data read no challenge. That any instance passes the description's test
is not shown here. Under the library's hypothesis h: the full size and the format's second hash function
alone; at the reference sizes alone. Closed facts by evaluation in Lean's kernel lie beneath the
three laws. Nothing on soundness, on completeness or on what a proof hides.

WHAT IT IS. The output head's own rounds read the mask row and six matrices out of a message of the
code switch into link 24; the laws on that message's text take publicOk at the input's public part
as a premise. Here that premise is exchanged for a plainer one, on the instance alone. The data:
K2.withSwitchData Sz.ref (K1.lotData Sz.ref), which is widerRows Sz.ref (Honest/AtPureWider.lean) by
that definition's text: the rows' data of the honest prover's filling. The layout: the ground's.

By. att_returns_at_open (Honest/K5/Law/AttValsAtHead.lean): the maker of the values of the vector of
reads returns at the twelve attention segments. readsLight_of_att
(Johnson/HonestTrace/U3Fit/ReadsDebt3.lean): so, at an instance that passes the description's test,
the light test on the reads' data accepts. publicOk_of_reads (Honest/K2/Law/PublicOkOfReads.lean):
so publicOk accepts at every place of the kind. places_at_head, segments_at_head
(Honest/K2/Law/PlacesWritten.lean): the places and the segments are the written ones.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicOkOfReads
import Johnson.Desc.ProofFile.Honest.K5.Law.AttValsAtHead
import Johnson.HonestTrace.U3Fit.ReadsDebt3

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6.Term
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open P5J (AtMgA TS F0T)
open ProofFile.Honest.K2 (SwitchPlace publicOk withSwitchData)
open ProofFile.Honest.K2.Law (placesW segsW places_at_head segments_at_head publicOk_of_reads)

/-- CONDITIONAL on the library's hypothesis h, on "G is the blank ground of the public part", on "p
is a written place of a code switch" and on startTestAccepts, which stays a premise: the
description's own test on the instance accepts. **THE CODE SWITCH's PUBLIC TEST ACCEPTS THE
INSTANCE, at the honest filling's data of the main rows and the ground's layout.** -/
theorem switchTestAccepts {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : ProofFile.Ground}
    (groundIsBlank : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {p : SwitchPlace}
    (placeIsWritten : p ∈ placesW) {ξ : ProofFile.Inst}
    (startTestAccepts : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true) :
    publicOk (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp G) G.first.layout p
      (segsW.take p.link) ξ = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans groundIsBlank)
  have accepts := publicOk_of_reads h O
    (OnBytes.HonestTrace.U3.Fit.readsLight_of_att h O startTestAccepts
      (OnBytes.HonestTrace.U3.Att.att_returns_at_open h O)) p
    (by rw [places_at_head h.toAtMg O]; exact placeIsWritten)
  rw [segments_at_head h.toAtMg O] at accepts
  exact accepts

end ProofFile.Honest.K6.Term

#print axioms ProofFile.Honest.K6.Term.switchTestAccepts
