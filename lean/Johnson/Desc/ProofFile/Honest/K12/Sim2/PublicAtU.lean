-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the public premises of the row of the test on G_u, at the proof file.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/PublicAtU.lean: under the head, at the proof file's shared chain: the numbers and the cut that a row at the test on G_u asks, as Sim2/RowFoldedPub.lean has them at the
key file: the public premises of On at a run at U.

  fold_pub_proof, room_U, withU_proof   closed facts at the written plan and place, by Lean's kernel
  numbers_U        hQ, hcf, hfr, hroom, hwU, hwO at the seated place and the shared chain's own plan
  CutsU            the rounds in front of the test and the two sendings' places in the shared list: hpre, the two cuts, hdU, hdO, hinU, hinO, hat, hsrc
  cuts_U           it holds under the head

Limits. The filling's hg, hgU, hgO and the book's hT, hb are not here. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.FitAtHead
import Johnson.Desc.ProofFile.Honest.K12.TreeIsColumnAtHead
import Johnson.Desc.ProofFile.Honest.K12.TableIsColumn
import Johnson.Desc.ProofFile.Honest.K12.SendFitAtHead
import Johnson.Desc.ProofFile.Honest.K12.DoorAtWalk
import Johnson.Desc.ProofFile.Honest.K12.Sim.ShownAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstPubAtHead
import Johnson.Desc.ProofFile.Honest.K14.PaidAll
import Johnson.Desc.ProofFile.Honest.K14.BudRows
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain alike₂_rounds)
open VerifiableInference.Desc.K1 (realSized)
open H2K.Member (piUFull)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K14 (SendPub jobU jobOmega sendingsFit sendPlace SendDeclared)
open Desc.K14 (St blocks readsAtLoc)
open Desc.K14.Honest (ReadsNone flatOf_carried)
open Johnson.G.OfPlan (rootsOf)
open P2Law.ProofPlan (WP)

/-- The closed facts on the plan. -/
theorem fold_pub_proof : (realSized.all fun q => sendingsFit (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape).P &&
    colFitsU (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape) piUFull && widthFits (jobU (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)) 0 &&
    widthFits (jobOmega (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)) 1) = true := by decide +kernel

theorem room_U : 2 * (stage₀ piUFull).k + 1 ≤ (stage₀ piUFull).h + (stage₀ piUFull).Z.l := by decide +kernel

theorem src_U : piUFull.nums.first.map (fun o => ProofFile.Honest.srcOf 1 o.2) = [(1, 0), (1, 2)] := by decide +kernel

/-- The trees in front of the two sendings, off the written rounds. -/
theorem roots_WP : rootsOf ((WP.shared.blocksInOrder.take 2).flatMap (·.rounds)) = 0 ∧
    rootsOf ((WP.shared.blocksInOrder.take 5).flatMap (·.rounds)) = 1 := by decide +kernel

attribute [local irreducible] P2Law.ProofPlan.WP

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

local notation "𝔽" => P5J.F0T o Zp Np cF

/-- **The numbers of the test on G_u at the seated place and the chain's own plan.** -/
theorem numbers_U (h : P5J.AtMg o Z D r₀ Zp Np cF) :
    sendingsFit (VerifiableInference.Desc.K1.qAt Zp Np) = true ∧ colFitsU ⟨VerifiableInference.Desc.K1.qAt Zp Np, 0⟩ (fourOf Np).U = true ∧
      freshFitsU ⟨VerifiableInference.Desc.K1.qAt Zp Np, 0⟩ (fourOf Np).U = true ∧
      2 * (stage₀ (fourOf Np).U).k + 1 ≤ (stage₀ (fourOf Np).U).h + (stage₀ (fourOf Np).U).Z.l ∧
      widthFits (jobU ⟨VerifiableInference.Desc.K1.qAt Zp Np, 0⟩) 0 = true ∧ widthFits (jobOmega ⟨VerifiableInference.Desc.K1.qAt Zp Np, 0⟩) 1 = true := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  obtain ⟨sU, -, -⟩ := places_at_head h
  obtain ⟨-, hfr, -⟩ := fits_at_head h
  have k := fold_pub_proof
  rw [hx] at k
  have k' : (sendingsFit (ProofFile.Honest.K12.Light.planOf Johnson.G.codesFull2 x.shape).P &&
      colFitsU (ProofFile.Honest.K12.Light.planOf Johnson.G.codesFull2 x.shape) piUFull &&
      widthFits (jobU (ProofFile.Honest.K12.Light.planOf Johnson.G.codesFull2 x.shape)) 0 &&
      widthFits (jobOmega (ProofFile.Honest.K12.Light.planOf Johnson.G.codesFull2 x.shape)) 1) = true := k
  simp only [Bool.and_eq_true] at k'
  obtain ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩ := k'
  refine ⟨?_, ?_, hfr, ?_, ?_, ?_⟩
  · rw [sendingsFit_plan, ProofFile.Honest.K12.Light.qAt_written Wr Np]
    exact k1
  · rw [colFitsU_plan, ProofFile.Honest.K12.Light.qAt_written Wr Np, colFitsU_stages _ sU]
    exact k2
  · have e : stage₀ (fourOf Np).U = stage₀ piUFull := by
      unfold stage₀
      rw [sU]
    rw [e]
    exact room_U
  · rw [(widthFits_plan _ 0).1, ProofFile.Honest.K12.Light.qAt_written Wr Np]
    exact k3
  · rw [(widthFits_plan _ 1).2, ProofFile.Honest.K12.Light.qAt_written Wr Np]
    exact k4

/-- **What a row at G_u asks of the rounds in front and of the two sendings.** -/
structure CutsU (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl)
    (preU tU preO tO : List (Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl))
    (bU bO : Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl)
    (d0 d1 d2 : Fmt.DeclaredRound) (e : Fmt.Entry) (post : List Fmt.DeclaredRound) : Prop where
  h0 : ReadsNone d0
  h1 : ReadsNone d1
  h2 : ReadsNone d2
  hpre : ((P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9).flatMap (·.rounds) =
    d0 :: d1 :: d2 :: { entry := e, stored := [readsAtLoc (VerifiableInference.Desc.K1.qAt Zp Np).S.fold (VerifiableInference.Desc.K1.qAt Zp Np).item] } :: post
  hcutU : (P5J.F0T o Zp Np cF).shared.blocksInOrder = preU ++ bU :: tU
  hcutO : (P5J.F0T o Zp Np cF).shared.blocksInOrder = preO ++ bO :: tO
  hpU : bU.place = sendPlace 2
  hpO : bO.place = sendPlace 5
  hdU : SendDeclared bU (jobU ⟨VerifiableInference.Desc.K1.qAt Zp Np, 0⟩)
  hdO : SendDeclared bO (jobOmega ⟨VerifiableInference.Desc.K1.qAt Zp Np, 0⟩)
  hinU : (preU.flatMap (·.rounds)).length + 2 ≤
    (((P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9).flatMap (·.rounds)).length
  hinO : (preO.flatMap (·.rounds)).length + 2 ≤
    (((P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9).flatMap (·.rounds)).length
  hat : 0 < (preU.flatMap (·.rounds)).length
  hsrc : (fourOf Np).U.nums.first.map (fun o => ProofFile.Honest.srcOf 1 o.2) =
    [(1, rootsOf (preU.flatMap (·.rounds)) + 0), (1, rootsOf (preO.flatMap (·.rounds)) + 1)]

/-- **Under the head the cut stands.** -/
theorem cuts_U (h : P5J.AtMg o Z D r₀ Zp Np cF) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (VerifiableInference.Desc.K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∃ preU tU preO tO bU bO d0 d1 d2 e post, CutsU o Zp Np cF preU tU preO tO bU bO d0 d1 d2 e post := by
  obtain ⟨hsn, -, hw⟩ := facts_at_head h
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := lengths_eight _ _ b1 b2 b3 b4 b5 b6 b7 b8 hb hw hsn
  obtain ⟨dU, pU, dO, pO⟩ := ProofFile.Honest.K14.send_declares (VerifiableInference.Desc.K1.qAt Zp Np) 0 b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨d0, d1, d2, e, post, q0, q1, q2, eq⟩ := rounds_eight _ _ b1 b2 b3 b4 b5 b6 b7 b8 hb hw
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, ef, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :=
    (flatOf_carried Zp.p.chains (VerifiableInference.Desc.K1.qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last hb :
      Desc.K14.Honest.FlatOf (𝔽).shared.blocksInOrder Zp.p.chains b1 b2 b3 b4 b5 b6 b7 b8)
  have ef' : (𝔽).shared.blocksInOrder = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl := ef
  have A := ProofFile.Honest.K14.alike_shared_at_laid h.scope h.laid
  have hfront : x0.rounds = [] := l0.rounds
  have hR9 : ((𝔽).shared.blocksInOrder.take 9).flatMap (·.rounds) = [b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds) := by
    rw [ef']
    show ([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block (𝔽).S₂ (𝔽).Cl)).flatMap (·.rounds) = _
    simp [hfront, l1.rounds, l2.rounds, l3.rounds, l4.rounds, l5.rounds, l6.rounds, l7.rounds, l8.rounds]
  have hRn : ∀ n, ((𝔽).shared.blocksInOrder.take n).flatMap (·.rounds) = (WP.shared.blocksInOrder.take n).flatMap (·.rounds) :=
    fun n => (alike₂_rounds _ _ (List.forall₂_take n A)).symm
  have r2 : ([x0, x1] : List (Block (𝔽).S₂ (𝔽).Cl)).flatMap (·.rounds) = ((𝔽).shared.blocksInOrder.take 2).flatMap (·.rounds) := by
    rw [ef']
    rfl
  have r5 : ([x0, x1, x2, x3, x4] : List (Block (𝔽).S₂ (𝔽).Cl)).flatMap (·.rounds) = ((𝔽).shared.blocksInOrder.take 5).flatMap (·.rounds) := by
    rw [ef']
    rfl
  have L9 : (((𝔽).shared.blocksInOrder.take 9).flatMap (·.rounds)).length = 8 := by
    rw [hR9]
    simp [n1, n2, n3, n4, n5, n6, n7, n8]
  have L2 : (([x0, x1] : List (Block (𝔽).S₂ (𝔽).Cl)).flatMap (·.rounds)).length = 1 := by
    simp [hfront, l1.rounds, n1]
  have L5 : (([x0, x1, x2, x3, x4] : List (Block (𝔽).S₂ (𝔽).Cl)).flatMap (·.rounds)).length = 4 := by
    simp [hfront, l1.rounds, l2.rounds, l3.rounds, l4.rounds, n1, n2, n3, n4]
  refine ⟨[x0, x1], x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl, [x0, x1, x2, x3, x4], x6 :: x7 :: x8 :: tl, x2, x5,
    d0, d1, d2, e, post, ⟨q0, q1, q2, hR9.trans eq, ef', ef', l2.place.trans pU, l5.place.trans pO,
    ProofFile.Honest.K14.sendDeclared_like l2.rounds l2.oracles dU, ProofFile.Honest.K14.sendDeclared_like l5.rounds l5.oracles dO,
    ?_, ?_, ?_, ?_⟩⟩
  · rw [L9, L2]
    omega
  · rw [L9, L5]
    omega
  · rw [L2]
    omega
  · rw [nums_head_U h, src_U, r2, r5, hRn, hRn, roots_WP.1, roots_WP.2]

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.fold_pub_proof
#print axioms ProofFile.Honest.K12.Sim2.numbers_U
#print axioms ProofFile.Honest.K12.Sim2.cuts_U
