-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/EndFiveMade.lean: THE FIVE FACTS AT EVERY REACHED LAST STATE OF THE FIRST CHAIN THAT
BEARS NO MARK, WITHOUT h5_planOk's PREMISE hB IN FRONT: a join of three files that lie. For the
premises h5 of Sh.reachOwed_in_scope (Johnson/Desc/K14/Law/SharedConstReachAt.lean) and hB of
Sh.reachOwed_paid (Johnson/Desc/K14/Law/SharedConstReachPaid.lean).

WHY. Johnson/IMR/EndFivePaid.lean's h5_planOk stands under hB: at every opening the test K12.Door.sendsAreB accepts at the table K12.Door.snAt. Johnson/IMR/SendsPinned.lean and Johnson/IMR/FivePinned.lean pay that test where the test PlanWritten.madeRow (Johnson/Desc/Ok/PlanWritten/MadeTest.lean) accepts and K12's sub-protocol passes its test on the plan; hp_of_planOk (Johnson/IMR/SendsFinal.lean) draws the latter from blocksOk c.blocksInOrder, and Johnson/IMR/PlanOkFlat.lean that from F.planOk.

WHAT IS SAID.
  hB_paid   at every opening: sendsAreB … = true: in the letters of Sh.reachOwed_paid's premise hB
  h5_paid   at every opening: the five facts: in the letters of Sh.reachOwed_in_scope's premise h5

THE PREMISES THAT ARE LEFT, AND WHOSE EACH IS. hS: the goals' scope · hF : F.planOk = true: the description's own test on the plan · hy : PlanWritten.madeRow Z = true: a test on the public files: under the head P5J.AtMg it is had (AtMg.pins, Johnson/P5T/FenceAtMg.lean); its payer in scope is LPFD.asks_pins (Johnson/Desc/Laid/ProofAsksLaw2.lean) · hL : K12.Door.laidAtCodes Z.first.codes Z.made.proof.1 = some L: the caller's own (laid_in_scope, Johnson/HB/LLHARD/PlanInScope.lean, not shown here).

What is not claimed. hF, hy, hL are shown nowhere here. At OnBytes.secondHashFunction alone. No soundness.

-/
import Johnson.IMR.EndFivePaid
import Johnson.IMR.FivePinned

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach)

variable {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {c : Chain S Cl} {P : VerifierAndGoals.PublicFiles}

/-- **The test on the sendings accepts at every opening**, in scope, where the description passes its test on the plan and madeRow accepts. -/
theorem hB_paid (hS : VerifierAndGoals.InScope P = true) (hF : F.planOk = true) (hy : VerifiableInference.PlanWritten.madeRow Z = true) : ∀ Bs base A B, IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B → K12.Door.sendsAreB Z.made.proof.1 358 (K12.Door.snAt Z Bs.G₀ IM.placesW) = true := by
  intro Bs base A B O
  obtain ⟨pp, hR⟩ := IM.reads_of_scope hS
  exact IM.sends_pinned_paid O hy (IM.hp_of_planOk hS hR O (IM.blocksOk_of_planOk O hF))

/-- **The five facts, with no premise left in front that the files of Johnson/IMR/ owe.** -/
theorem h5_paid (hS : VerifierAndGoals.InScope P = true) (hF : F.planOk = true) (hy : VerifiableInference.PlanWritten.madeRow Z = true) {L : K12.Door.Laid} (hL : K12.Door.laidAtCodes Z.first.codes Z.made.proof.1 = some L) : ∀ Bs base A B, IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B → ∀ p : ProofFile.InstPub × S, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) c.blocksInOrder.length p → p.2.failed = none → K12.Door.atFirstBook 0 p.2 = true ∧ Sound.bookFitsB p.2.book = true ∧ p.2.book.place.size = p.2.st.oracles.size ∧ p.2.st.codes = Z.first.codes ∧ K12.Door.atFirstSeats L p.2 = true :=
  h5_planOk hS hF (hB_paid hS hF hy) hL

end Meaning.K2

#print axioms Meaning.K2.hB_paid
#print axioms Meaning.K2.h5_paid
