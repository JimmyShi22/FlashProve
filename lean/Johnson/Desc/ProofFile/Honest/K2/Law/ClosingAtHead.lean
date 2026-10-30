-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ClosingAtHead.lean: the kind "the code switch" (K2): UNDER THE
HEAD `P5J.AtMg` AND THE OPENING IN ITS LETTERS: THE PUBLIC TEST `closingOk` (Honest/K2/Sim.lean: the
closing returns at zeros) SAYS YES AT EVERY MEMBER OF `switchPlaces Zp Bs.G₀`, AT THE SEGMENTS IN
FRONT OF IT: the premise hc of `switch_playsS` (Honest/K2/Law/PlaysScript.lean), in that file's own
term, at all 25 places. A join. Statements with their proofs: calls.

  `closingAt_all` the 25 yeses as one: ∀ i < 25
  `closingW_all` ∀ p ∈ placesW: the light test says yes
  `closing_at_head` THE TOP: ∀ p ∈ switchPlaces Zp Bs.G₀, closingOk freshTable ((segmentsOf Zp
                    Bs.G₀).take p.link) p = true

By: `closingW_0` to `closingW_24` (Honest/K2/Law/ClosingW0.lean to ClosingW4.lean: each by Lean's
kernel) · `closingAt_says` (Honest/K2/Law/ClosingTest.lean) · `placesW_count`
(Honest/K2/Law/PublicAtWritten.lean) · `closingOk_light` (Honest/K2/Law/ClosingLight.lean: the test
and its light twin say the same) · `places_at_head`, `segments_at_head`
(Honest/K2/Law/PlacesWritten.lean).

Limits. IT SAYS THAT A PUBLIC TEST PASSES: the closing RETURNS at zeros: nothing on what it leaves,
nothing on what a prover sends. 25 CLOSED FACTS BY LEAN's KERNEL LIE BENEATH, REPLAYED BY NO
INDEPENDENT CHECKER. THE HEAD IS SHOWN MET BY NOBODY HERE. Nothing is joined to `switch_playsS` here
(the join: `switch_playsS_at`, Honest/K2/Law/PlaysAtArms.lean). The full size alone; the format's
second hash function alone. It stands on files that are in no sealed library. Nothing on any
property.

-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingW0
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingW1
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingW2
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingW3
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingW4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- The 25 yeses as one. -/
theorem closingAt_all : ∀ i, i < 25 → closingAt i = true := by
  intro i hi
  interval_cases i
  · exact closingW_0
  · exact closingW_1
  · exact closingW_2
  · exact closingW_3
  · exact closingW_4
  · exact closingW_5
  · exact closingW_6
  · exact closingW_7
  · exact closingW_8
  · exact closingW_9
  · exact closingW_10
  · exact closingW_11
  · exact closingW_12
  · exact closingW_13
  · exact closingW_14
  · exact closingW_15
  · exact closingW_16
  · exact closingW_17
  · exact closingW_18
  · exact closingW_19
  · exact closingW_20
  · exact closingW_21
  · exact closingW_22
  · exact closingW_23
  · exact closingW_24

/-- **The light test says yes at every member of the closed list.** -/
theorem closingW_all : ∀ p ∈ placesW,
    closingOkLight freshTable (segsW.take p.link) p = true := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
  exact closingAt_says hi (closingAt_all i (by rw [← placesW_count]; exact hi))

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **Under the head and the opening the closing returns at zeros, at every place of the kind.** -/
theorem closing_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀,
      closingOk freshTable ((segmentsOf Zp Bs.G₀).take p.link) p = true := by
  rw [places_at_head h O, segments_at_head h O]
  intro p hp
  rw [closingOk_light]
  exact closingW_all p hp

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.closingAt_all
#print axioms ProofFile.Honest.K2.Law.closingW_all
#print axioms ProofFile.Honest.K2.Law.closing_at_head
