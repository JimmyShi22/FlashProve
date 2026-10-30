-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ReadsWritten.lean: the kind "the code switch" (K2): closed facts
by Lean's kernel on the positions that the written description reads of the trees of the switches'
sendings.

  switchReadsW  the test on queried positions accepts at the 25 written places
  switchLaidW   at each of them the trees can be laid and every message lies in a tree, so the test
                skips no message
  switchAskedW  every message is asked at a tree for which positions are sampled
  switchReadsW_tight  a control: with one more position sampled for the first tree of each place's
                sending the test rejects at some place

By: readsWithinT, tabW, treesAt (Johnson/SendSim/Seat/ReadsAtWritten.lean), placesW.

Limits. Public numbers; no input, no coin. The test counts a position once for each opening.
-/
import Johnson.SendSim.Seat.ReadsAtWritten
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes.SendSim.Seat (readsWithinT treesAt tabW drawnTab)
open VerifiableInference.PlanWritten (cutFirstFull)

set_option maxRecDepth 1000000 in
/-- **The test on queried positions accepts at the 25 written places.** -/
theorem switchReadsW : (placesW.all fun p =>
    readsWithinT tabW (sendingPar p.sizes.codes (switchSent p.sizes p.others))
      (treesAt cutFirstFull p.place)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At each place the trees can be laid, and every message lies in a tree. -/
theorem switchLaidW : (placesW.all fun p =>
    (VerifiableInference.Desc.Own.treesMade p.sizes.codes (switchSent p.sizes p.others)).isSome &&
    (List.range (switchSent p.sizes p.others).size).all fun k =>
      (((VerifiableInference.Desc.Own.treesMade p.sizes.codes (switchSent p.sizes p.others)).getD {}).tree[k]?).isSome)
    = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Every message is asked at a tree for which positions are sampled. -/
theorem switchAskedW : (placesW.all fun p =>
    (List.range (switchSent p.sizes p.others).size).all fun k =>
      match ((VerifiableInference.Desc.Own.treesMade p.sizes.codes (switchSent p.sizes p.others)).getD {}).tree[k]? with
      | none => false
      | some τ => drawnTab tabW (treesAt cutFirstFull p.place + τ) != 0) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: one more position sampled for the first tree of each sending makes the test reject
at some place. -/
theorem switchReadsW_tight : (placesW.all fun p =>
    readsWithinT (((0, treesAt cutFirstFull p.place), 1) :: tabW)
      (sendingPar p.sizes.codes (switchSent p.sizes p.others))
      (treesAt cutFirstFull p.place)) = false := by
  decide +kernel

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.switchReadsW
#print axioms ProofFile.Honest.K2.Law.switchLaidW
#print axioms ProofFile.Honest.K2.Law.switchAskedW
#print axioms ProofFile.Honest.K2.Law.switchReadsW_tight
