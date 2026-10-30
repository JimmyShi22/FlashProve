-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TreesAtHeadUPub.lean: the three public facts on the plan that
`trees_head_U` (TreesAtHeadU.lean) takes as premises, drawn from the library's head (`P5J.AtMg`);
and so the premise hTrees of `onFreeT_head_U` and `onFreeT_head_U_six`, to the letter, with these
three paid.

What is left as premises of the top. On the plan's letters: hb (the eight sub-protocols are those
that the plan's `blocks` returns), h9 (the nine in front of the test). On the run: hR, hrun, hc, S.
On the filling: hgU, hgO. The tie of values: hbk (`bookCutsU`): a tie between what one part is
handed of a run's values and what another part is handed of them.

A conditional, as TreesAtHeadU.lean's head says.

  `roots_W`      at the written description: the roots that the rounds of the shared list's first 2,
                 3, 5 and 6 sub-protocols declare: one evaluation by Lean's kernel
  `rounds_take_head`   under the head the proof file's own shared list declares, in its first n
                 sub-protocols, the rounds that the written description declares there
  `place9_head`  under the head the sub-protocol behind the first nine stands at the seated place of
                 the test on G_u
  `trees_head_U_pub`   the statement

By what. `alike_shared_at_laid`, of the authors of the honest side of the linear claim's shared
rounds (Honest/K14/WrittenAtHead.lean); the library's `alike₂_rounds`; `places_WU`
(Sim/AloneAtU.lean), whose `cut_WU` shows the manner; `H2K.JointK.place_of_p12At`.
Kin. The matter of `place9_head` also stands without the head, from the plan's eight sub-protocols:
`ninth_at_U` (AtProof/SideAtU.lean), which makes the cut where this lemma is handed it. This lemma
does not give that one: it wants the head and makes no cut. That one would give this one wherever
its one premise holds (the eight are those that the plan's `blocks` returns), which
`trees_head_U_pub` has among its own premises (hb): two roads to one fact.

Limits. `roots_W`'s second and fourth numbers are two facts more, which show where the count moves:
no control: no line here says no. The full size alone. It moves no count. Nothing on completeness,
soundness or hiding.
The stand is the state that `midSharedAtW` (Honest/MidW.lean) returns. That `runC`'s own walk goes
through that state is not said here.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.TreesAtHeadU
import Johnson.Desc.ProofFile.Honest.K12.Sim.AloneAtU

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place alike₂_rounds)
open VerifiableInference.Desc (K1.qAt)
open Desc.K14 (St blocks)
open P2Law.ProofPlan (WP)
open Johnson.G.OfPlan (rootsOf)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light.AtU (places_WU)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Common StandsAt Face ready runC
  midSharedAtW carriedAt storedShown Part Weights TableRand)
open ProofFile.Honest.K14 (jobU jobOmega sendingPart liftSend sendPlace alike_shared_at_laid)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

set_option maxRecDepth 1000000 in
/-- At the written description: the roots that the rounds of the shared list's first 2, 3, 5 and 6
sub-protocols declare. The numbers move just where the two sendings stand (numbers 2 and 5). -/
theorem roots_W : [2, 3, 5, 6].map (fun n => rootsOf ((WP.shared.blocksInOrder.take n).flatMap (·.rounds))) =
    [0, 1, 1, 3] := by
  decide +kernel

/-- Under the head the proof file's own shared list declares, in its first n sub-protocols, the
rounds that the written description declares there. -/
theorem rounds_take_head (h : P5J.AtMg o Z D r₀ Zp Np cF) (n : ℕ) :
    ((P5J.F0T o Zp Np cF).shared.blocksInOrder.take n).flatMap (·.rounds) =
      (WP.shared.blocksInOrder.take n).flatMap (·.rounds) :=
  (alike₂_rounds _ _ (List.forall₂_take n (alike_shared_at_laid h.scope h.laid))).symm

/-- Under the head the sub-protocol behind the shared list's first nine stands at the seated place
of the test on G_u. -/
theorem place9_head (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (pre t : List (Block St ProofFile.Cl)) (b : Block St ProofFile.Cl)
    (hcut : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre ++ b :: t)
    (h9 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9) :
    b.place = (fourOf Np).U.place := by
  have A := alike_shared_at_laid h.scope h.laid
  have hl : pre.length = 9 := by
    have e9 : pre.length = min 9 (P5J.F0T o Zp Np cF).shared.blocksInOrder.length :=
      (congrArg List.length h9).trans List.length_take
    have e : (P5J.F0T o Zp Np cF).shared.blocksInOrder.length = pre.length + (t.length + 1) :=
      (congrArg List.length hcut).trans List.length_append
    omega
  rw [hcut] at A
  have A2 := List.forall₂_drop_append _ pre (b :: t) A
  obtain ⟨bW, tl, hbW, -, hd⟩ := List.forall₂_cons_right_iff.1 A2
  have hget : WP.shared.blocksInOrder[pre.length]? = some bW := by
    have e := congrArg List.head? hd
    rw [List.head?_drop] at e
    exact e
  rw [hl] at hget
  have hp : (WP.shared.blocksInOrder.map (·.place))[9]? = some bW.place := by
    rw [List.getElem?_map, hget]
    rfl
  rw [places_WU] at hp
  have hp' : (⟨2, none, 9, .K12⟩ : Place) = bW.place := Option.some.inj hp
  exact (hbW.1.symm.trans hp'.symm).trans (H2K.JointK.place_of_p12At _ _).symm

/-- **hTrees, TO THE LETTER, UNDER THE HEAD, AT u? := none, WITH THE THREE PUBLIC FACTS PAID.** What
is left is sorted in the file's head. -/
theorem trees_head_U_pub {W₀ Rc Tr X₀ Y : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
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
    (hbk : bookCutsU Bk ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U = true) :
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
  have q := roots_W
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at q
  obtain ⟨q2, -, q5, -⟩ := q
  exact trees_head_U h b1 b2 b3 b4 b5 b6 b7 b8 hb weights rand J hJ Js hR σ pre t S h9 hrun hc hgU
    hgO hbk (place9_head h pre t σ.block S.cut h9) (by rw [rounds_take_head h 2]; exact q2)
    (by rw [rounds_take_head h 5]; exact q5)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.roots_W
#print axioms ProofFile.Honest.K12.Light.rounds_take_head
#print axioms ProofFile.Honest.K12.Light.place9_head
#print axioms ProofFile.Honest.K12.Light.trees_head_U_pub
