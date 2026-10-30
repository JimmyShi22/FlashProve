-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/AtFull/Desc/SharedShare.lean: THE SHARED CHAIN's SHARE OF THE MASTER LEDGER: of A := what
onlineSharedChain Z returns: **every one of its twelve sub-protocols passes its test on the plan**
(PlanWordOwed.b₂) and **A.fileOk = true** (the first conjunct of PlanWordOwed.hF), under hypotheses
by field, at the written values of Johnson/AtFull/Desc/LaterSeats.lean (proofSizedFull · piU · piO ·
piW · p14W · sharedBack). The chain's cut (the shared part of PlanWordOwed.hC) is that file's
cut_shared_written: it is called here, not typed anew. Statements with their proofs.

What the seat (Desc.K14.sharedSeatAt, Johnson/Desc/ProofFile/Lot/K14SeatAtZ.lean) reads of Z:
Z.p.chains.made.sized.proof's set · codes · batch; what placesOfMade Z.made returns; and two Bools:
OkD.AtC.front2 Z.p.chains (its first sub-protocol's test on the plan) and
OkD.AtC.beside Z.p.X Z.p.chains (the caller's share of fileOk).

  shared_chain_written   the chain at the written values (the two steps that stand inside
                         cut_shared_written's proof, as a statement of its own).
  fullOk                 what Chain.retype and Chain.blocksInOrder ask of a sub-protocol outside a link: its
                         own test on the plan; no run of claims; no run behind a batching.
  back_planOk            [Lean's kernel] eleven of the twelve pass fullOk: K14's eight, K12's two at
                         piU | piO, the chain's end. back_bent_point · back_bent_stage: it can fail.
  flat_retype_ok         a chain without links whose members pass fullOk: every member of its flat
                         list, at another type of claims, passes its test on the plan.
  shared_planOk          **b₂**, under hFront : front2 Z.p.chains = true.
  fit_written · fit_bent [Lean's kernel] as many proximity tests as the shape asks.
  shared_fileOk          **A.fileOk = true**, under hBeside : beside Z.p.X Z.p.chains = true.
  shared_share           **the three in one sentence**, behind later_of_members' six hypotheses.

NOT PAID HERE: hFront · hBeside (the file's own share of the tests on the plan: on the planner's
chains, not on the seat) · the three fields · the three members.
Limits. No soundness is claimed. No example of the head is shown in this file; two, at storedPublicFiles and at
zGap alone, are AtFullSide.Top.headMember_zFull and headMember_zGap, whose own Limits say what they
are worth.

-/
import Johnson.AtFull.Desc.LaterSeats
import Johnson.Desc.OnPlan.OkBesideC
import Johnson.Desc.OnPlan.OkFrontC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Desc
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.PlanWritten
open VerifiableInference.Desc.K12.Seat (onGu onGomega onOwn)
open VerifiableInference.OnPublicFiles (OkD.AtC.front2 OkD.AtC.beside)
open H2K.JointK (sharedN p14N pGu pGomega pOwn)

/-! ## By Lean's kernel, at the written values -/

/-- What Chain.retype and Chain.blocksInOrder (Johnson/Desc/Block.lean) ask of a sub-protocol outside a link:
its own test on the plan; no run of claims; no run behind a batching. -/
def fullOk {S Cl : Type} (b : Block S Cl) : Bool :=
  b.planOk && b.claims.isEmpty && b.after.isEmpty

/-- **Eleven of the twelve pass.** -/
theorem back_planOk :
    (sharedBack p14W piU piO ++ [Seat.last (sharedBack p14W piU piO)]).all fullOk = true := by
  decide +kernel

/-- The test can fail: with no message named that must stand before the shared point. -/
theorem back_bent_point :
    (let b := sharedBack { p14W with beforePoint := [] } piU piO
     b ++ [Seat.last b]).all fullOk = false := by
  decide +kernel

/-- The test can fail: with one stage fewer in Omega's test. -/
theorem back_bent_stage :
    (let b := sharedBack p14W piU
      { piO with nums := { piO.nums with stages := piO.nums.stages.dropLast } }
     b ++ [Seat.last b]).all fullOk = false := by
  decide +kernel

/-- As many proximity tests as the shape asks. -/
theorem fit_written : _root_.Desc.K14.testsFit p14W
    [onGu (proximityTestKind guardedProximityTestParts piU), onGomega (proximityTestKind guardedProximityTestParts piO)] = true := by
  decide +kernel

/-- The test can fail: with one proximity test alone. -/
theorem fit_bent : _root_.Desc.K14.testsFit p14W [onGu (proximityTestKind guardedProximityTestParts piU)] = false := by
  decide +kernel

/-! ## A chain without links, carried to another type of claims and laid flat -/

theorem flat_retype_ok {S Cl Cl' : Type} (c : Chain S Cl) (hl : c.links = [])
    (h : ∀ x ∈ c.first :: c.front ++ c.back ++ [c.last], fullOk x = true) :
    ∀ b ∈ (c.retype (Cl' := Cl')).blocksInOrder, b.planOk = true := by
  have key : ∀ x : Block S Cl, fullOk x = true →
      ((x.retype (Cl' := Cl')).planOk && (x.retype (Cl' := Cl')).hasNoClaimsAndNothingAfter) = true := by
    intro x hx
    unfold fullOk at hx
    simp only [Bool.and_eq_true] at hx
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    show ((x.planOk && x.claims.isEmpty) &&
      ((x.retype (Cl' := Cl')).claims.isEmpty && x.after.isEmpty)) = true
    rw [h1, h2, h3]
    rfl
  intro b hb
  unfold Chain.blocksInOrder Chain.retype at hb
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.flatMap_nil, List.not_mem_nil,
    or_false] at hb
  rcases hb with ((rfl | ⟨y, ⟨x, hx, rfl⟩, rfl⟩) | ⟨y, ⟨x, hx, rfl⟩, rfl⟩) | rfl
  · have k := key c.first (h _ (by simp))
    show (((c.first.retype (Cl' := Cl')).planOk && c.links.isEmpty) &&
      (c.first.retype (Cl' := Cl')).hasNoClaimsAndNothingAfter) = true
    rw [hl]
    simp only [Bool.and_eq_true] at k ⊢
    exact ⟨⟨k.1, rfl⟩, k.2⟩
  · exact key x (h _ (by simp [hx]))
  · exact key x (h _ (by simp [hx]))
  · exact key c.last (h _ (by simp))

/-! ## At Z, under hypotheses by field -/

section
variable (Z : ProofFile.Pub) (N : H2U.Places4)
  (hset : Z.p.chains.made.sized.proof.set = proofSizedFull.set)
  (hcodes : Z.p.chains.made.sized.proof.codes = proofSizedFull.codes)
  (hbatch : Z.p.chains.made.sized.proof.batch = proofSizedFull.batch)
include hset hcodes hbatch

theorem p14_written (hW : pOwn N = piW) : p14N Z N = p14W := by
  have hW' : H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W = piW := hW
  unfold p14N _root_.Desc.K14.p14Of _root_.Desc.K14.beforePointOf p14W
  simp only [hset, hcodes, hbatch, hW']
  rfl

omit hset hcodes hbatch in
theorem tests_written (nO : H2U.PlaceNums) (hO : N.O = some nO) (hU : pGu N = piU)
    (hO' : pGomega nO = piO) :
    Seat.tests N = [onGu (proximityTestKind guardedProximityTestParts piU), onGomega (proximityTestKind guardedProximityTestParts piO)] := by
  have hU' : H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U = piU := hU
  have hO'' : H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO = piO := hO'
  unfold Seat.tests
  rw [hO, hU']
  simp only [Option.toList, List.map_cons, List.map_nil, hO'', List.cons_append, List.nil_append]

/-- The chain at the written values. -/
theorem shared_chain_written (nO : H2U.PlaceNums) (hO : N.O = some nO) (hU : pGu N = piU)
    (hO' : pGomega nO = piO) (hW : pOwn N = piW) :
    (sharedN Z N).chain = _root_.Desc.K14.chainOf Z.p.chains p14W
      [onGu (proximityTestKind guardedProximityTestParts piU), onGomega (proximityTestKind guardedProximityTestParts piO)] Seat.last := by
  have e : (sharedN Z N).chain = _root_.Desc.K14.chainOf Z.p.chains (p14N Z N) (Seat.tests N)
      Seat.last := rfl
  rw [e, p14_written Z N hset hcodes hbatch hW, tests_written N nO hO hU hO']

/-- **b₂: every sub-protocol of the shared chain passes its test on the plan.** -/
theorem shared_planOk (nO : H2U.PlaceNums) (hO : N.O = some nO) (hU : pGu N = piU)
    (hO' : pGomega nO = piO) (hW : pOwn N = piW)
    (hFront : VerifiableInference.OnPublicFiles.OkD.AtC.front2 Z.p.chains = true) (Cl' : Type) :
    ∀ b ∈ ((sharedN Z N).chain.retype (Cl' := Cl')).blocksInOrder, b.planOk = true := by
  rw [shared_chain_written Z N hset hcodes hbatch nO hO hU hO' hW]
  refine flat_retype_ok _ rfl ?_
  intro x hx
  rcases List.mem_append.1 hx with h1 | h1
  · rcases List.mem_append.1 h1 with h2 | h2
    · have h3 : x ∈ [_root_.Desc.K14.frontBlock Z.p.chains] := h2
      obtain rfl := List.mem_singleton.1 h3
      show (VerifiableInference.OnPublicFiles.OkD.AtC.front2 Z.p.chains && true && true) = true
      rw [hFront]
      rfl
    · have h3 : x ∈ sharedBack p14W piU piO := h2
      exact List.all_eq_true.1 back_planOk x (List.mem_append_left _ h3)
  · have h3 : x ∈ [Seat.last (sharedBack p14W piU piO)] := h1
    exact List.all_eq_true.1 back_planOk x (List.mem_append_right _ h3)

/-- **The first conjunct of hF: the seat's fileOk.** -/
theorem shared_fileOk (nO : H2U.PlaceNums) (hO : N.O = some nO) (hU : pGu N = piU)
    (hO' : pGomega nO = piO) (hW : pOwn N = piW)
    (hBeside : VerifiableInference.OnPublicFiles.OkD.AtC.beside Z.p.X Z.p.chains = true) :
    (sharedN Z N).fileOk = true := by
  have e : (sharedN Z N).fileOk = (_root_.Desc.K14.testsFit (p14N Z N) (Seat.tests N) &&
      VerifiableInference.OnPublicFiles.OkD.AtC.beside Z.p.X Z.p.chains) := rfl
  rw [e, p14_written Z N hset hcodes hbatch hW, tests_written N nO hO hU hO', fit_written, hBeside]
  rfl

end

/-- **The shared chain's share, in one sentence.** -/
theorem shared_share (Z : ProofFile.Pub)
    (hset : Z.p.chains.made.sized.proof.set = proofSizedFull.set)
    (hcodes : Z.p.chains.made.sized.proof.codes = proofSizedFull.codes)
    (hbatch : Z.p.chains.made.sized.proof.batch = proofSizedFull.batch)
    (e₁ : H2U.p12FoldedOfMade Z.made 9 = piU) (e₂ : H2U.p12OmegaOfMade Z.made 10 = piO)
    (e₃ : H2U.p12OwnOfMade Z.made 2 = piW)
    (hFront : VerifiableInference.OnPublicFiles.OkD.AtC.front2 Z.p.chains = true)
    (hBeside : VerifiableInference.OnPublicFiles.OkD.AtC.beside Z.p.X Z.p.chains = true) :
    ∃ A : ProofFile.SharedSeat, ProofFile.onlineSharedChain Z = some A ∧ A.fileOk = true ∧
      (∀ b ∈ (A.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder, b.planOk = true) ∧
      cutOf (A.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder = cutSharedFull := by
  obtain ⟨N, nO, hN, hO, hU, hO', hW⟩ := places_of_members Z.made e₁ e₂ e₃
  exact ⟨_, (later_return Z N hN).1,
    shared_fileOk Z N hset hcodes hbatch nO hO hU hO' hW hBeside,
    shared_planOk Z N hset hcodes hbatch nO hO hU hO' hW hFront _,
    cut_shared_written Z N hset hcodes hbatch nO hO hU hO' hW _⟩

end Johnson.AtFull.Desc

#print axioms Johnson.AtFull.Desc.back_planOk
#print axioms Johnson.AtFull.Desc.back_bent_point
#print axioms Johnson.AtFull.Desc.back_bent_stage
#print axioms Johnson.AtFull.Desc.flat_retype_ok
#print axioms Johnson.AtFull.Desc.fit_written
#print axioms Johnson.AtFull.Desc.fit_bent
#print axioms Johnson.AtFull.Desc.p14_written
#print axioms Johnson.AtFull.Desc.tests_written
#print axioms Johnson.AtFull.Desc.shared_chain_written
#print axioms Johnson.AtFull.Desc.shared_planOk
#print axioms Johnson.AtFull.Desc.shared_fileOk
#print axioms Johnson.AtFull.Desc.shared_share
