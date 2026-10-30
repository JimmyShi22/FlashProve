-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at the proximity test on G_omega: the clause on the first opening's columns under the head.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/TreesHead.lean: `trees_at_run_omega` (SimO/TreesOmega.lean) under the library's head (`P5J.AtMg`), at the list `firstListAtOmega`: its public premises are paid here.

  `roots_omega_written`, `rounds_omega_written`   at the written description: the roots and the rounds in front of the sending and of the test: one evaluation by Lean's kernel
  `width0_real`, `width0_head`   the check on o_omega's tree
  `trees_head_omega`   **the clause under the head**

What is left as premises. On the run: hR, hrun, hc, S, h10. On the filling: hg, hgO, hlaid. On the plan's letters: hb. On the book: hbk, e₂, hf, ho, hst, hmem, evaluated on no real book. FirstTies T, hk, hrows.

Limits. A conditional. At the job with `omega? := none`. Of the walk (`runC`). No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.SimO.TreesOmega
import Johnson.Desc.ProofFile.Honest.K12.SimO.AtHead
import Johnson.Desc.ProofFile.Honest.K12.TreesAtHeadUPub

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Light
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place K1.qAt alike₂_rounds)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.K12 (P12 T12)
open Desc.K14 (St blocks)
open Desc.K14.Honest (flatOf_carried)
open P2Law.ProofPlan (WP)
open Johnson.G.OfPlan (rootsOf)
open H2K.Pub (sgOf)
open H2K.Member (piOFull)
open H2K.JointK (laidOf)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Common StandsAt ready runC midSharedAtW
  carriedAt storedShown Part Placed Member Weights TableRand carryE Ahead)
open ProofFile.Honest.K14 (jobOmega sendingPart liftSend sendPlace send_declares sendDeclared_like)
open Johnson.Prover.Link (μOf)
open ProofFile.Honest.K12.AtProof (fourOf)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

theorem roots_omega_written :
    [5, 10].map (fun n => rootsOf ((WP.shared.blocksInOrder.take n).flatMap (·.rounds))) = [1, 7] := by
  decide +kernel

theorem rounds_omega_written :
    [5, 10].map (fun n => ((WP.shared.blocksInOrder.take n).flatMap (·.rounds)).length) = [4, 43] := by
  decide +kernel

theorem width0_real : (realSized.all fun q =>
    ProofFile.Honest.K12.Light.widthFits (jobOmega (planOf q.2 q.1.shape)) 0) = true := by
  decide +kernel

theorem width0_head (h : P5J.AtMg o Z D r₀ Zp Np cF) (n : ℕ) :
    widthFits (jobOmega ⟨K1.qAt Zp Np, n⟩) 0 = true := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have k := width0_real
  rw [hx] at k
  have k' : widthFits (jobOmega (planOf Johnson.G.codesFull2 x.shape)) 0 = true := k
  rw [(widthFits_plan _ 0).2, qAt_written Wr Np]
  exact k'

theorem src_omega_written :
    firstListAtOmega.map (fun o => ProofFile.Honest.srcOf 1 o.2) = [(1, 1 + 0), (1, 1 + 1), (1, 7)] := by
  decide +kernel

theorem dep_omega_written :
    [depthOf piOFull 0, depthOf piOFull 1, (piOFull.nums.stages.headD default).Z.a] =
      firstListAtOmega.map (·.1.a) := by
  decide +kernel

/-- **The clause on the first opening's columns, under the head.** -/
theorem trees_head_omega {W₀ Rc Tr X₀ Y Pb : Type} {pO : P12} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (hO : (fourOf Np).O = some pO) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst TableKey Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)}
    (door : Common W₀ Rc TableKey → Front X₀ → T12)
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (J : TestJob (Common W₀ Rc TableKey) X₀)
    (hJ : J = (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand none).toRun.toTest)
    (Js : SimJob Pb) (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side St ProofFile.Cl Empty (Common W₀ Rc TableKey) X₀ Pb) (hσ : σ.block.place = pO.place)
    (pre t : List (Block St ProofFile.Cl))
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ
      (restMember J Js : Member Empty _ _ _).guarded pre t (firstLen J.p.nums.stages))
    (h10 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 10)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (hg : (P.shared.find? fun g => g.place == σ.block.place) =
      some (proverSideOfProximityTest J : Placed Empty _ _).needsField)
    (hlaid : σ.block.rounds.zip σ.block.oracles = J.laid)
    (hgO : (P.shared.find? fun g => g.place == sendPlace 5) = some ⟨sendPlace 5,
      [(liftSend (askOf ⟨K1.qAt Zp Np, 0⟩ weights rand) (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀)]⟩)
    (hbk : bookCutsOmega Bk ⟨K1.qAt Zp Np, 0⟩ pO = true)
    (e₂ : Ahead) (hf : (carryE Bk ⟨J.p.place, 0 + 1⟩)[J.members.length]? = some e₂)
    (ho : e₂.owner = ⟨J.p.place, 0⟩) (hst : e₂.start = ⟨0, 0⟩)
    (hmem : ∀ t, t < J.members.length → ∃ a a', (carryE Bk ⟨J.p.place, 0⟩)[t]? = some a ∧
      (carryE Bk ⟨J.p.place, 0 + 1⟩)[t]? = some a' ∧ a.owner = a'.owner ∧ a.start = a'.start ∧
      a.count = a'.count)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (Dd : ℕ → Fmt.Drawn)
    (T : FirstTies J s next rest Dd
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)))
    (hk : s.h ≤ s.k)
    (hrows : ∀ (w : Common W₀ Rc TableKey) (fr : Front X₀) (mem mem' : ℕ → Stretch),
      (∀ t, t < J.members.length → mem t = mem' t) →
      μOf (sgOf s) (J.rows₀ w fr mem) = μOf (sgOf s) (J.rows₀ w fr mem'))
    (st : List (ℕ × ℕ × List UInt64)) :
    ∀ m ca, midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) →
      carriedAt Bk k 1 ⟨σ.block.place, 1⟩
        (restPart J : Part Empty (Common W₀ Rc TableKey) X₀).needsField = .ok ca →
      (J.trees₀ m.st.input (restFront J m) (ProofFile.Honest.K12.stretches _ ca)
          (rowsAt J (ProofFile.Honest.K12.stretches _ ca) m)).map (·.1) = firstListAtOmega.map (·.1.a) ∧
        ∀ (i : ℕ) (o' : Fmt.Shape × Fmt.TreeSource) (Tr' : Tree), firstListAtOmega[i]? = some o' →
          (J.trees₀ m.st.input (restFront J m) (ProofFile.Honest.K12.stretches _ ca)
            (rowsAt J (ProofFile.Honest.K12.stretches _ ca) m))[i]? = some Tr' →
          ∃ cols, (r.run.beforeAt st ⟨σ.block.place, 1⟩).treeCols
                (ProofFile.Honest.srcOf 1 o'.2).1 (ProofFile.Honest.srcOf 1 o'.2).2 = some cols ∧
            ∀ q ∈ cols, q.2 = Tr'.2 q.1 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, eF, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :=
    flatOf_carried (Cl := ProofFile.Cl) Zp.p.chains (K1.qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last hb
  obtain ⟨dU, pU, dO, pO'⟩ := send_declares (K1.qAt Zp Np) 0 b1 b2 b3 b4 b5 b6 b7 b8 hb
  have eO : (P5J.F0T o Zp Np cF).shared.blocksInOrder =
      [x0, x1, x2, x3, x4] ++ x5 :: x6 :: x7 :: x8 :: tl := eF
  have e5 : (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 5 = [x0, x1, x2, x3, x4] := by
    rw [eO]
    rfl
  have hh := rounds_take_head h 5
  rw [e5] at hh
  have hpO : x5.place = sendPlace 5 := l5.place.trans pO'
  have w1 := rounds_omega_written
  have w2 := roots_omega_written
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at w1 w2
  have kO : (List.flatMap (fun y : Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl =>
      y.rounds) [x0, x1, x2, x3, x4]).length = 4 :=
    (congrArg List.length hh).trans w1.1
  have kp : (List.flatMap (fun y : Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl =>
      y.rounds) pre).length = 43 := by
    rw [h10]
    exact (congrArg List.length (rounds_take_head h 10)).trans w1.2
  have r5 : rootsOf (List.flatMap (fun y : Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl =>
      y.rounds) [x0, x1, x2, x3, x4]) = 1 :=
    (congrArg rootsOf hh).trans w2.1
  have r10 : rootsOf (List.flatMap (fun y : Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl =>
      y.rounds) pre) = 7 := by
    rw [h10]
    exact (congrArg rootsOf (rounds_take_head h 10)).trans w2.2
  have hn := nums_head_O h hO
  obtain ⟨-, q, hq, hcf⟩ := colFits_head h 0
  obtain rfl : q = pO := Option.some.inj (hq.symm.trans hO)
  refine trees_at_run_omega h.laid.planOk hR hrun ⟨K1.qAt Zp Np, 0⟩ q door weights rand J hJ Js σ hσ
    pre t S hc hg hlaid [x0, x1, x2, x3, x4] _ x5 eO hpO (by rw [hpO]; exact hgO)
    (sendDeclared_like l5.rounds l5.oracles dO) (by rw [kO, kp]; decide) hbk (sendingsFit_head h) hcf
    (width0_head h 0) (width_head h 0).2 (by rw [kO]; show 0 < 4; decide) e₂ hf ho hst hmem s next rest Dd T hk hrows
    firstListAtOmega ?_ ?_ st
  · rw [r5, r10]
    exact src_omega_written
  · unfold depthOf
    rw [hn]
    exact dep_omega_written

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.trees_head_omega
#print axioms ProofFile.Honest.K12.Light.roots_omega_written
#print axioms ProofFile.Honest.K12.Light.rounds_omega_written
#print axioms ProofFile.Honest.K12.Light.width0_real
#print axioms ProofFile.Honest.K12.Light.width0_head
