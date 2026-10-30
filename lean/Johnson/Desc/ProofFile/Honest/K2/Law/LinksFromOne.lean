-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/LinksFromOne.lean: the kind "the code switch" (K2): UNDER THE
HEAD `P5J.AtMg` AND THE OPENING IN ITS LETTERS, EVERY SWITCH OF THE PLAN HAS A LINK OF 1 OR MORE: so
each closes at least the first segment. Three statements with their proofs; no definition.

  `linksFromOneW`   BY LEAN's KERNEL, at the closed list of written places (`placesW`,
                    Honest/K2/Law/PlacesWritten.lean): each place's link is 1 or more
  `linksFromOneW_can_fail`   a control: "2 or more" fails at that list
  `link_pos_at_head`   ∀ p ∈ switchPlaces Zp Bs.G₀, 1 ≤ p.link: by `places_at_head` (there)

Why. `first_rows_at_closing` and its two sisters (Honest/K2/Law/FirstRowsAtClosing.lean) ask it as a
premise.

Limits. A PUBLIC FACT ON THE PLAN's NUMBERS: nothing on what a prover sends, nothing on a run. Two
closed facts by evaluation in Lean's kernel, one of them a control. The head is shown met by nobody
here. The full size alone; the format's second hash function alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

set_option maxRecDepth 1000000 in
/-- **At the written places each link is 1 or more.** -/
theorem linksFromOneW : (placesW.all fun p => decide (1 ≤ p.link)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: "2 or more" fails. -/
theorem linksFromOneW_can_fail : (placesW.all fun p => decide (2 ≤ p.link)) = false := by
  decide +kernel

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **Under the head and the opening every switch of the plan has a link of 1 or more.** -/
theorem link_pos_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, 1 ≤ p.link := by
  rw [places_at_head h O]
  intro p hp
  exact of_decide_eq_true (List.all_eq_true.1 linksFromOneW p hp)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.linksFromOneW
#print axioms ProofFile.Honest.K2.Law.linksFromOneW_can_fail
#print axioms ProofFile.Honest.K2.Law.link_pos_at_head
