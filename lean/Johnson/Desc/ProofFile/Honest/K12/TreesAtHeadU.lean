-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TreesAtHeadU.lean: the premise hTrees of `onFreeT_head_U`
(OnFreeTAtHeadU.lean) and `onFreeT_head_U_six` (OnFreeTAtHeadUSix.lean), TO THE LETTER, under the
library's head (`P5J.AtMg`), at a job whose first member carries no vector of its own (u? := none):
the clause trees of the condition at the second part's entry, at the proximity test on G_u of the
proof file's shared chain, at a run of the frame's walking prover.

A conditional: nothing here shows that `ready` or `runC` returns, that the part is called, or that a
filling holds the two sendings' sides. The head has members at the two named sets of files
(`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean); that these premises hold with it is shown
by nothing that we know.

OF WHAT KIND IT IS. Its premise hbk (`bookCutsU`, CutOfBookAt.lean) is a tie between what one part
is handed of a run's values and what another part is handed of them. The statement names no value
and states no law over random values.

What is left as premises. On the run: hR, hrun, hc, S, h9. On the filling: hgU, hgO. The tie of
values: hbk. THREE PUBLIC FACTS ON THE PLAN THAT ARE NOT DRAWN FROM THE HEAD HERE: hσ (the test's
place); hr0, hr1 (the roots that the rounds in front of the two sendings declare: none; one).

  `trees_head_U`   the statement

By what. `trees_at_run_U` (Sim/TreesAtRunU.lean). Public, under the head: `sendingsFit_head`
(SendFitAtHead.lean); `colFits_head`, `room_head_U` (TreeIsColumnAtHead.lean); `fits_at_head`
(FitAtHead.lean); `width_head` (TableIsColumn.lean); `first_head_U` (Sim/RestTiesAtHeadU.lean);
`facts_at_head` (NearAtHead.lean); `lengths_eight` (Sim/ShownAtRun.lean); the library's
`flatOf_carried` (Johnson/Desc/K14/Honest/FlatForm.lean); `send_declares`, `sendDeclared_like`, of
the authors of the honest side of the linear claim's shared rounds.

Limits. The test on G_u alone. The full size alone. Of the walk (`runC`). It moves no count. Nothing
on completeness, soundness or hiding.
The stand is the state that `midSharedAtW` (Honest/MidW.lean) returns. That `runC`'s own walk goes
through that state is not said here.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesAtRunU
import Johnson.Desc.ProofFile.Honest.K12.OnFreeTAtHeadU
import Johnson.Desc.ProofFile.Honest.K12.Sim.ShownAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.RestTiesAtHeadU

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (TableKey)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc (K1.qAt)
open Desc.K14 (St blocks)
open Desc.K14.Honest (flatOf_carried)
open Johnson.G.OfPlan (rootsOf)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Common StandsAt Face ready runC
  midSharedAtW carriedAt storedShown Part Weights TableRand)
open ProofFile.Honest.K14 (jobU jobOmega sendingPart liftSend sendPlace send_declares sendDeclared_like)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **hTrees, TO THE LETTER, UNDER THE HEAD, AT u? := none.** The premises are sorted in the file's
head. -/
theorem trees_head_U {W₀ Rc Tr X₀ Y : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst TableKey Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)}
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (J : TestJob (Common W₀ Rc TableKey) X₀) (hJ : J = (jobHeadU Zp Np
        [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand none).toRun.toTest)
    (Js : SimJob TableKey)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side St ProofFile.Cl Empty (Common W₀ Rc TableKey) X₀ TableKey)
    (pre t : List (Block St ProofFile.Cl))
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ (restMember J Js) pre t
      (firstLen J.p.nums.stages))
    (h9 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = true)
    (hgU : (P.shared.find? fun g => g.place == sendPlace 2) = some ⟨sendPlace 2,
      [(liftSend (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand) (sendingPart (jobU ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀)]⟩)
    (hgO : (P.shared.find? fun g => g.place == sendPlace 5) = some ⟨sendPlace 5,
      [(liftSend (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand)
        (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)) : Part Empty (Common W₀ Rc TableKey) X₀)]⟩)
    (hbk : bookCutsU Bk ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U = true)
    (hσ : σ.block.place = (fourOf Np).U.place)
    (hr0 : rootsOf (((P5J.F0T o Zp Np cF).shared.blocksInOrder.take 2).flatMap (·.rounds)) = 0)
    (hr1 : rootsOf (((P5J.F0T o Zp Np cF).shared.blocksInOrder.take 5).flatMap (·.rounds)) = 1) :
    ∀ m ca, midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ
        ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = .ok (some m) →
      carriedAt Bk k 1 ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩
          (restMember (V := Empty) J Js).part = .ok ca →
      (J.trees₀ m.st.input (restFront J m) (stretches _ ca) (rowsAt J (stretches _ ca) m)).map
          (·.1) = (fourOf Np).U.nums.first.map (·.1.a) ∧
        ∀ (i : ℕ) (o' : Fmt.Shape × Fmt.TreeSource) (Tr' : Tree), (fourOf Np).U.nums.first[i]?
            = some o' →
          (J.trees₀ m.st.input (restFront J m) (stretches _ ca)
            (rowsAt J (stretches _ ca) m))[i]? = some Tr' →
          ∃ cols, (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
              ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩).treeCols (ProofFile.Honest.srcOf 1
                  o'.2).1 (ProofFile.Honest.srcOf 1 o'.2).2 = some cols ∧
            ∀ q ∈ cols, q.2 = Tr'.2 q.1 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, eF, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :=
    flatOf_carried (Cl := ProofFile.Cl) Zp.p.chains (K1.qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last hb
  obtain ⟨hSN, -, hU⟩ := facts_at_head h
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := lengths_eight _ _ b1 b2 b3 b4 b5 b6 b7 b8 hb hU hSN
  obtain ⟨dU, pU, dO, pO⟩ := send_declares (K1.qAt Zp Np) 0 b1 b2 b3 b4 b5 b6 b7 b8 hb
  have eF' : (P5J.F0T o Zp Np cF).shared.blocksInOrder =
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl := eF
  have eU : (P5J.F0T o Zp Np cF).shared.blocksInOrder =
      [x0, x1] ++ x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl := eF
  have eO : (P5J.F0T o Zp Np cF).shared.blocksInOrder =
      [x0, x1, x2, x3, x4] ++ x5 :: x6 :: x7 :: x8 :: tl := eF
  have epre : pre = [x0, x1, x2, x3, x4, x5, x6, x7, x8] := by
    rw [h9, eF']
    rfl
  have hNU : ([x0, x1].flatMap (·.rounds)).length = 1 := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      l0.rounds, l1.rounds, n1]
    rfl
  have hNO : ([x0, x1, x2, x3, x4].flatMap (·.rounds)).length = 4 := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      l0.rounds, l1.rounds, l2.rounds, l3.rounds, l4.rounds, n1, n2, n3, n4]
    rfl
  have hNp : (pre.flatMap (·.rounds)).length = 8 := by
    rw [epre]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      l0.rounds, l1.rounds, l2.rounds, l3.rounds, l4.rounds, l5.rounds, l6.rounds, l7.rounds,
      l8.rounds, n1, n2, n3, n4, n5, n6, n7, n8]
    rfl
  have hpU : x2.place = sendPlace 2 := l2.place.trans pU
  have hpO : x5.place = sendPlace 5 := l5.place.trans pO
  have hr0' : rootsOf ([x0, x1].flatMap (·.rounds)) = 0 := by
    rw [eF'] at hr0
    exact hr0
  have hr1' : rootsOf ([x0, x1, x2, x3, x4].flatMap (·.rounds)) = 1 := by
    rw [eF'] at hr1
    exact hr1
  -- the same five, at the description's own names for the two types
  have kU : (List.flatMap (fun y : Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl =>
      y.rounds) [x0, x1]).length = 1 := hNU
  have kO : (List.flatMap (fun y : Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl =>
      y.rounds) [x0, x1, x2, x3, x4]).length = 4 := hNO
  have kp : (List.flatMap (fun y : Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl =>
      y.rounds) pre).length = 8 := hNp
  have k0 : rootsOf (List.flatMap (fun y : Block (P5J.F0T o Zp Np cF).S₂
      (P5J.F0T o Zp Np cF).Cl => y.rounds) [x0, x1]) = 0 := hr0'
  have k1 : rootsOf (List.flatMap (fun y : Block (P5J.F0T o Zp Np cF).S₂
      (P5J.F0T o Zp Np cF).Cl => y.rounds) [x0, x1, x2, x3, x4]) = 1 := hr1'
  refine trees_at_run_U h.laid.planOk hR hrun ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U _ weights rand J hJ
    Js σ hσ pre t S hc [x0, x1] _ [x0, x1, x2, x3, x4] _ x2 x5 eU eO hpU hpO
    (by rw [hpU]; exact hgU) (by rw [hpO]; exact hgO)
    (sendDeclared_like l2.rounds l2.oracles dU) (sendDeclared_like l5.rounds l5.oracles dO)
    (by rw [kU, kp]; decide) (by rw [kO, kp]; decide) hbk (sendingsFit_head h)
    (colFits_head h 0).1 (fits_at_head h).2.1 (room_head_U h) (width_head h 0).1
    (width_head h 0).2 (by rw [kU]; exact Nat.zero_lt_one) ?_ _
  rw [first_head_U h, k0, k1]
  rfl

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.trees_head_U
