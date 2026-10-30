-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the simulators' state on entry at the first chain's last test.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/DoorAtL.lean: stateAtFirstChainTest, the state on entry of the first chain's
proximity test, as the simulators' letter: stateFromView (DoorTrue.lean) at the blocks in front of the
place, at the description's own start read off the public instance, at the way in. And at a called
part of a run: it is the record T that door_moves_at_L names, with which the prover's wiped door
agrees but for targets.

  stateAtFirstChainTest          the letter: of the public part and the Before alone, at every Before
  door_at_firstChainTest     the statement, at any member

No patch stands here: stateAtFirstChainTest is one function at every Before.
Under the head. Of the walk (runC). No law. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.DoorStand
import Johnson.Desc.ProofFile.Honest.K12.AtProof.LotAtDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain OpenedColumn FileDescription foldBlocks Place)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof

variable {V W₀ Rc Tr X : Type}

/-- **The simulators' state on entry at the first chain's last test.** -/
def stateAtFirstChainTest (Z : ProofFile.Pub) : ProofFile.Inst → Before → T12 :=
  stateFromView ((flatL Z).takeWhile (·.place != placeL)) (fun x => ProofFile.startS Z x.pub) enterFinish idleT12

/-- **At a called part of the side that testSide seats**: the wiped door of the job agrees with the
record T at the run's front, and stateAtFirstChainTest at the front cut back by i is T. -/
theorem door_at_firstChainTest {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Ky X₀ Y Pb : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side S ProofFile.Cl V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (u : Member V (Local W₀ Rc ProofFile.Inst Tr) Y Pb) (pre t : List (Block S ProofFile.Cl)) (i : ℕ)
    (St : StandsAt cF.blocksInOrder R.first σ u pre t i)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (D : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing) (pl : K2.SwitchPlace)
    (Js : SimJob Pb) (fs : List (Fall S))
    (hσ : testSide cF.blocksInOrder
      (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) Js fs = some σ) :
    ∃ (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y) (T : T12),
      midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ =
        .ok (some m) ∧
      m.seen.length = (pre.flatMap (·.rounds)).length + i ∧
      (∀ fr : Front Y, fr.seen.rounds = m.seen.take (pre.flatMap (·.rounds)).length →
        Blind.Agree (doorAtL Zp m.st.input fr) T) ∧
      m.st.input.x = x ∧
      (∃ (s : S) (cs : List OpenedColumn), enterFinish s = .ok T ∧
        foldBlocks 0 pre ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₁
          ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).pub x))
          (m.seen.take (pre.flatMap (·.rounds)).length) cs = .ok (s, [], []) ∧
        fillCols (readsOf 0 0 (P.storedWords w₀ rc)
          (treeOwn (r.run.played.1.take (pre.flatMap (·.rounds)).length)) (pre.flatMap (·.rounds))
          ((m.seen.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cs) ∧
      stateAtFirstChainTest Zp x ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
        ⟨σ.block.place, u.number⟩).cut i) = T := by
  obtain ⟨m, s, cs, more, rest, tr, a1, a2, a3, a4, a5, a6, a7, a8, T, hT, b, -⟩ :=
    door_moves_at_L h hR σ u pre t i St hrun hc D readers closing pl Js fs hσ
  have hp : (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl :
      TestJob (Local W₀ Rc ProofFile.Inst Tr) Y).p = (fourOf Np).L := numbersL_at_head h
  have hpl : σ.block.place = placeL :=
    (Blind.testSide_place hσ).trans (hp ▸ Blind.placeL_of_four Np)
  have hn := (places_nodup (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).planOk_ok).1 h.laid.planOk).places).1
  have hcut : cF.blocksInOrder = pre ++ σ.block :: t := St.cut
  have hn' : ((pre ++ σ.block :: t).map (·.place)).Nodup := hcut ▸ hn
  have hpre : (flatL Zp).takeWhile (·.place != placeL) = pre := by
    rw [flatL_at_head h, ← hpl, hcut]
    exact Blind.takeWhile_cut pre t σ.block (Blind.apart_of_nodup hn')
  refine ⟨m, T, a1, a5, fun fr hf => (b fr hf).2, by rw [a3], ⟨s, cs, hT, a7, a8⟩, ?_⟩
  have e := stateFromView_at_stand h.laid.planOk hR hrun σ u pre t i St hc m a1 _ s cs a7 a8
    (fun x : ProofFile.Inst => ProofFile.startS Zp x.pub) enterFinish idleT12 x rfl
  have e2 : (enterFinish s).toOption.getD idleT12 = T := by
    rw [hT]
    rfl
  unfold stateAtFirstChainTest
  rw [hpre]
  exact e.trans e2

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.stateAtFirstChainTest
#print axioms ProofFile.Honest.K12.Sim2.door_at_firstChainTest
