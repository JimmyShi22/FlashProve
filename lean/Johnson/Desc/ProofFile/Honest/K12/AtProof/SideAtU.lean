-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/SideAtU.lean: the side that `testSide` (K12/Sim/Row.lean)
seats at the proximity test on G_u, under the library's head: its place, what its block declares,
the cut of the shared chain in front of it, and that the test's second member stands there. These
are four hypotheses of `onFreeT_head_U` (K12/OnFreeTAtHeadU.lean) and of the laws made of it: hg's
place, hlaid, h9 and S. No definition; five theorems.

First, what it does not give. `stands_at_U` hangs on hR: that `ready` returns at a prover whose
shared list holds the pair. Nothing that we know shows it.

  `side_place_U`   the side stands at `placeU`. No head
  `side_laid_U`    hlaid: its block's declared rounds with their oracle messages are the job's
  `ninth_at_U`     where the eight are made: the shared chain's member number 9 stands at `placeU`.
                 No head
  `nine_of_cut`    h9: every cut of the shared chain at a block that stands at `placeU` is the cut
                 at nine
  `stands_at_U`    S and h9 together, from hg at `placeU` (`found_of_shared`, JoinAtWider.lean) and
                 `ready`'s return

By what. Ours: `testSide_place` (K12/Blind/AtHandAtFinish.lean), `p12At_place`, `tests_four`
(Places.lean), `find_gu` (K12/Sim/FirstSeatAtHead.lean), `zip_laid` (K12/PlaysK12.lean),
`planOk_head_U` (K12/NearAtHead.lean), `first_any_head_U` (K12/Sim/FirstAnyAtHeadU.lean),
`stands_rest` (K12/Sim/FrameAtRun.lean), `rest_moves` (K12/HalfSteps.lean), `len_movesFrom`
(K12/Sim/ExactSide.lean), `nums_head_U` (K12/Sim/FirstPubAtHead.lean). Of the frame's authors:
`cut_unique`, `places_nodup` (Honest/Law/Cuts.lean). Sealed: `flat_retype_all`
(Johnson/Desc/K14/Law/SharedFlat.lean), `H2K.JointK.k12_place`
(Johnson/Loose/H2K12/SitsInPure.lean). The road of `side_laid_U` stands as a step inside a proof of
K12/Sim/DebtAtU.lean; that of `stands_at_U` follows `meets_filled_U` (K12/Sim/StandsOfFilling.lean),
which is on the first member. The matter of `ninth_at_U` stands a second time, by another road:
`place9_head` (K12/TreesAtHeadUPub.lean): under the head, without the eight, at a cut that it is
handed.

Limits.
- hb, that the library makes the eight at the head's parameters, stays a hypothesis.
- That the head's job and its simulator's job meet hp, hfr, hs and ho is not stated here.
- Nothing is played or evaluated here. The test on G_u alone.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.K14.Law.SharedFlat
import Johnson.Loose.H2K12.SitsInPure
import Johnson.Desc.ProofFile.Honest.Law.Cuts
import Johnson.Desc.ProofFile.Honest.K12.PlaysK12
import Johnson.Desc.ProofFile.Honest.K12.NearAtHead
import Johnson.Desc.ProofFile.Honest.K12.Sim.FrameAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstAnyAtHeadU
import Johnson.Desc.ProofFile.Honest.K12.Blind.AtHandAtFinish
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc (K1.qAt)
open Desc.K14 (St blocks)
open ProofFile.Honest (ProverCoinCounts Prover Coins Ready Side Common StandsAt Fall ready)
open ProofFile.Honest.K12.Light (find_gu first_any_head_U stands_rest planOk_head_U nums_head_U)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **The side that `testSide` seats for a job at the planner's record for G_u stands at
`placeU`.** -/
theorem side_place_U {σ₀ Cl V W X Pb : Type} {bs : List (Block σ₀ Cl)} {J : TestJob W X}
    {Js : SimJob Pb} {fs : List (Fall σ₀)} {σ : Side σ₀ Cl V W X Pb}
    (hσ : testSide bs J Js fs = some σ) (hp : J.p = (fourOf Np).U) : σ.block.place = placeU := by
  rw [Blind.testSide_place hσ, hp]
  exact p12At_place _ _

/-- **hlaid, under the head.** -/
theorem side_laid_U {V W X Pb : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF) {J : TestJob W X}
    {Js : SimJob Pb} {fs : List (Fall St)} {σ : Side St ProofFile.Cl V W X Pb}
    (hσ : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js fs = some σ) (hp : J.p = (fourOf Np).U) :
    σ.block.rounds.zip σ.block.oracles = J.laid := by
  obtain ⟨b, hf, -, hr, hor⟩ := find_gu h
  have hb : σ.block = b := by
    unfold testSide Side.seated at hσ
    rw [hp, hf] at hσ
    obtain rfl := Option.some.inj hσ
    rfl
  rw [hb, hr, hor, zip_laid _ (planOk_head_U h), ← hp]
  rfl

/-- **Where the eight are made: the shared chain's member number 9 stands at `placeU`.** No head:
by the description's own text. -/
theorem ninth_at_U (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∃ b tl, (P5J.F0T o Zp Np cF).shared.blocksInOrder = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9 ++ b :: tl ∧
      b.place = placeU ∧ ((P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9).length = 9 := by
  have e : (P5J.F0T o Zp Np cF).shared.blocksInOrder = Desc.K14.Law.frontOf Zp.p.chains ::
      ([b1, b2, b3, b4, b5, b6, b7, b8].map Block.retype ++
        ((VerifiableInference.Desc.K12.Seat.tests Np ++
          [VerifiableInference.Desc.K12.Seat.last ([b1, b2, b3, b4, b5, b6, b7, b8] ++
            VerifiableInference.Desc.K12.Seat.tests Np)]).map Block.retype).map
          Desc.K14.Law.bareOf) :=
    Desc.K14.Law.flat_retype_all Zp.p.chains (K1.qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last hb
  rw [e, tests_four]
  refine ⟨_, _, rfl, ?_, rfl⟩
  show (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts (fourOf Np).U :
    Block VerifiableInference.Desc.K12.T12 Unit).place = placeU
  rw [H2K.JointK.k12_place]
  exact p12At_place _ _

/-- **h9: every cut of the shared chain at a block that stands at `placeU` is the cut at nine.** -/
theorem nine_of_cut (h : P5J.AtMg o Z D r₀ Zp Np cF) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (c : Block St ProofFile.Cl) (pre t : List (Block St ProofFile.Cl))
    (hcut : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre ++ c :: t) (hc : c.place = placeU) :
    pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9 := by
  obtain ⟨b, tl, e, hbp, -⟩ := ninth_at_U (o := o) (cF := cF) b1 b2 b3 b4 b5 b6 b7 b8 hb
  have hn := (places_nodup (((P5J.F0T o Zp Np cF).planOk_ok).1 h.laid.planOk).places).2.1
  have hcm : c ∈ (P5J.F0T o Zp Np cF).shared.blocksInOrder := by
    rw [hcut]
    exact List.mem_append_right _ List.mem_cons_self
  have hbm : b ∈ (P5J.F0T o Zp Np cF).shared.blocksInOrder := by
    rw [e]
    exact List.mem_append_right _ List.mem_cons_self
  have hcb : c = b := List.inj_on_of_nodup_map hn hcm hbm (hc.trans hbp.symm)
  subst hcb
  exact (cut_unique (·.place) pre _ c t tl (hcut.symm.trans e) (hcut ▸ hn)).1

/-- **S and h9 together.** -/
theorem stands_at_U (h : P5J.AtMg o Z D r₀ Zp Np cF) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    {W₀ Rc Ky Tr X₀ Y : Type} {Bk : ProverCoinCounts} {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc}
    {x : ProofFile.Inst} {k : Coins Bk} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y}
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (J : TestJob (Common W₀ Rc Ky) X₀) (Js : SimJob Ky) (hp : J.p = (fourOf Np).U)
    (hfr : J.fresh.isNone = false) (hs : Js.p = (fourOf Np).U) (ho : Js.own = false)
    (fs : List (Fall St)) (σ : Side St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hσ : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js fs = some σ)
    (hg : (P.shared.find? fun g => g.place == placeU) = some (proverSideOfProximityTest J)) :
    ∃ t, StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ (restMember J Js)
      ((P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9) t (firstLen J.p.nums.stages) := by
  obtain ⟨f1, hm, -⟩ := (first_any_head_U (V := Empty) h J Js hp hfr hs ho).2.2 fs σ hσ
  have hσ' := hσ
  unfold testSide Side.seated at hσ'
  obtain ⟨b, hbf, e⟩ := Option.map_eq_some_iff.1 hσ'
  have hblk : σ.block ∈ (P5J.F0T o Zp Np cF).shared.blocksInOrder := by
    rw [← e]
    exact List.mem_of_find?_eq_some hbf
  have hrow : σ.row = testPairs J Js := by rw [← e]
  have hmem : restMember J Js ∈ σ.members := by
    have hm' : σ.members = [firstMember J Js, restMember J Js] := hm
    rw [hm']
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have hst : J.p.nums.stages = H2K.Member.piUFull.nums.stages := by rw [hp, nums_head_U h]
  obtain ⟨s, t', rest, es⟩ : ∃ s t' rest, H2K.Member.piUFull.nums.stages = s :: t' :: rest :=
    ⟨_, _, _, rfl⟩
  have hpos : (restPart J : Part Empty (Common W₀ Rc Ky) X₀).moves.length ≠ 0 := by
    rw [(congrArg List.length (rest_moves J s t' rest (hst.trans es))).trans
      (len_movesFrom J _ _ _), hst]
    decide
  have hg' : (P.shared.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J) := by
    rw [side_place_U hσ hp]
    exact hg
  obtain ⟨pre, t, S⟩ := stands_rest h.laid.planOk hR J Js σ hblk hrow f1 hmem hpos _ hg' rfl
  have e9 := nine_of_cut h b1 b2 b3 b4 b5 b6 b7 b8 hb σ.block pre t S.cut (side_place_U hσ hp)
  exact ⟨t, e9 ▸ S⟩

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.side_place_U
#print axioms ProofFile.Honest.K12.AtProof.side_laid_U
#print axioms ProofFile.Honest.K12.AtProof.ninth_at_U
#print axioms ProofFile.Honest.K12.AtProof.nine_of_cut
#print axioms ProofFile.Honest.K12.AtProof.stands_at_U
