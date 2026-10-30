-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- the law at the first chain's sendings, and the count at the description.
/-
Johnson/M1/Rows.lean: the written list of sendings against the code switch's places and the cut; and,
in the goals' scope where the gate accepts, that the description's declared rounds are the written
ones. No property of the protocol is claimed here.
-/
import Johnson.M1.NumbersProved
import Johnson.M1.K2Places
import Johnson.SendSim.Seat.ReadsAtLive
import Johnson.SendSim.Seat.ReadsCountProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open OnBytes.M1 (codesW treesBefore freshW)
open OnBytes.SendSim.Seat (treesAt)
open ProofFile.Honest.K2 (SwitchPlace sendingPar rideOf switchSent switchFresh)
open ProofFile.Honest.K2.Law (placesW)
open VerifiableInference.PlanWritten (cutFirstFull)

set_option maxRecDepth 1000000 in
/-- The code switch's 25 places are the sendings 3, 6, .., 75, message for message. -/
theorem sent_ties : (placesW.zipIdx.all fun x =>
    switchSent x.1.sizes x.1.others == OnBytes.M1.sentAt (3 * (x.2 + 1))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The fresh masks named by hand are the places' own. -/
theorem fresh_ties : (placesW.zipIdx.all fun x =>
    switchFresh x.1.sizes x.1.others x.1.foldVars == freshW (3 * (x.2 + 1))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The two counts of trees agree at the code switch's places: in front of a place the cut has as
many as the sendings. -/
theorem tree_ties : (placesW.zipIdx.all fun x =>
    treesAt cutFirstFull x.1.place == treesBefore (3 * (x.2 + 1))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At the finish and the last test's four switches the fold's row variables named by hand are the
stages' own numbers in the proof file's written sizes. -/
theorem fresh_last : ((List.range 5).all fun j =>
    ((freshW (75 + j)).map (·.2)) ==
      some (VerifiableInference.PlanWritten.proofSizedFull.request.last.getD j default).k) = true := by
  decide +kernel

/-- The trees that the cut tells, in order: log-length and words of a column. -/
def cutTrees : List (Nat × Nat) :=
  cutFirstFull.flatMap fun r => r.2.2.2.2.1.flatMap fun x => x.2.map fun o => (o.logLength, o.words)

/-- The trees that the sendings lay, in order: the same two numbers. -/
def sendTrees : List (Nat × Nat) :=
  (List.range 82).flatMap fun i =>
    ((Own.treesMade codesW (OnBytes.M1.sentAt i)).map fun L =>
      L.shapes.toList.map fun t =>
        (t.logN, t.mainSymbols.foldl (· + ·) 0 + t.maskSymbols.foldl (· + ·) 0)).getD []

set_option maxRecDepth 1000000 in
/-- The cut and the sendings tell one list of trees. -/
theorem trees_tie : cutTrees = sendTrees := by decide +kernel

section
variable {P : VerifierAndGoals.PublicFiles} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block First.S ProofFile.Cl)} {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In scope, where the gate accepts, at an opening of the maker's value, the description's declared
rounds are the written ones. -/
theorem decl_of_live (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) :
    F.roundsDeclaredByBlocks = Johnson.AtFull.Pub.DW := by
  obtain ⟨h2, h4⟩ := OnBytes.SendSim.Seat.plan_of_live hL O
  have PO := (F.planOk_ok).1 h2
  have hk := VerifiableInference.PlanWritten.key_in_scope_pure hS O.pub
  obtain ⟨hm, hc⟩ := LPFD.asks_pins h4 O.pub (decide_eq_true hk)
  have hy := VerifiableInference.PlanWritten.pinnedAt_of_row (Z := Z) (by rw [hm, Bool.or_true])
  have hD : Z.D = Johnson.AtFull.Pub.DW := OnBytes.SendSim.Seat.D_in_scope hS O.pub hy
  have hpl : F.plans = Z.D := by rw [O.desc]; rfl
  rw [← hD, ← hpl]
  exact Prod.ext PO.decl₁ (Prod.ext PO.decl₂ PO.decl₃)

end

end Johnson.M1

#print axioms Johnson.M1.decl_of_live
