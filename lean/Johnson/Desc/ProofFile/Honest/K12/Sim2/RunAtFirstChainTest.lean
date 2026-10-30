-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: what is left of the condition at a run of the first chain's last test.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/RunAtFirstChainTest.lean: at a called second member of the
first chain's last proximity test, at a run of the frame's walking prover, under the head: the
condition OnEntry (Entry.lean) at the run's own stand, carried values and front. Joined here: the
five clauses of the stand (five_L, StandL.lean), the first opening's columns (trees_first, TreesL.lean),
the door and the agreement (onEntry_at_firstChainTest, EntryAtL.lean).

  onEntry_at_run   the statement

The seat comes from seat_at_last_test; hcut names the block in front of the test. What stays a
premise. hasks: the two clauses ShapeAsksD, DataAsks at the job that stands in: the
claim true on the rows lies there. On the filling and the book: hg, hgK (the prover holds the test's
half and the finish's), hT, hTies. Public: hfit, hW, hos, hsrc, hj. patch with its two laws. Of the
walk (runC). Nothing shows that ready or runC returns. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.EntryAtL
import Johnson.Desc.ProofFile.Honest.K12.Sim2.StandL
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesL

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof

variable {W₀ Rc Tr : Type}

/-- **The seat, at the cut that names what stands in front of the test.** The chain's places are
distinct, so the cut is the seat's. -/
theorem stands_of_cut {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Ky X₀ Y : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y}
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k = .ok R)
    (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y) (hp : J.p = (fourOf Np).L)
    (hfrN : J.fresh.isNone = false) (Js : SimJob ProofFile.Inst) (hs : Js.p = (fourOf Np).L)
    (ho : Js.own = false) (fs : List (Fall S))
    (σ : Side S ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y ProofFile.Inst)
    (hσ : testSide cF.blocksInOrder J Js fs = some σ)
    (hg : (P.first.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J))
    (pre t : List (Block S ProofFile.Cl)) (hcut : cF.blocksInOrder = pre ++ σ.block :: t) :
    StandsAt cF.blocksInOrder R.first σ (restMember J Js) pre t (firstLen J.p.nums.stages) := by
  obtain ⟨pre₀, t₀, -, -, -, St₀, -⟩ := seat_at_last_test h hR J hp hfrN Js hs ho fs σ hσ hg
  have hn := (places_nodup (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).planOk_ok).1 h.laid.planOk).places).1
  have hc₀ : cF.blocksInOrder = pre₀ ++ σ.block :: t₀ := St₀.cut
  have n₀ : ((pre₀ ++ σ.block :: t₀).map (·.place)).Nodup := hc₀ ▸ hn
  have n₁ : ((pre ++ σ.block :: t).map (·.place)).Nodup := hcut ▸ hn
  have e₁ : pre₀ = pre := by
    have a := Blind.takeWhile_cut pre₀ t₀ σ.block (Blind.apart_of_nodup n₀)
    have c := Blind.takeWhile_cut pre t σ.block (Blind.apart_of_nodup n₁)
    rw [← hc₀] at a
    rw [← hcut] at c
    exact a.symm.trans c
  subst e₁
  have e₂ : t₀ = t := by
    have := hc₀.symm.trans hcut
    simpa using this
  subst e₂
  exact St₀

/-- **What is left of the condition at a run.** -/
theorem onEntry_at_run {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Ky X₀ Y : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k = .ok R)
    (D : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing)
    (pl : K2.SwitchPlace) (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y)
    (hJ : J = jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl)
    (Js : SimJob ProofFile.Inst) (hJs : Js.rec₀ = stateAtFirstChainTest Zp)
    (hs : Js.p = H2U.p12OfMade Zp.made) (ho : Js.own = false) (fs : List (Fall S))
    (σ : Side S ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y ProofFile.Inst)
    (hσ : testSide cF.blocksInOrder J Js fs = some σ) (pre : List (Block S ProofFile.Cl)) (b : Block S ProofFile.Cl)
    (t : List (Block S ProofFile.Cl))
    (hcut : cF.blocksInOrder = (pre ++ [b]) ++ σ.block :: t)
    (hg : (P.first.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J))
    (hT : tiesB Bk (H2U.p12OfMade Zp.made).place (membersL pl).length = true)
    (hgK : (P.first.find? fun g => g.place == b.place) =
      some (K2.switchHalf (K2.coreSender K2.freshTable) D readers closing pl))
    (hfit : fitsL (H2U.p12OfMade Zp.made) pl = true)
    (hW : columnWidth (finishSending pl) 0 = ((finishTrees pl).shapes.getD 0 default).mainWidth +
      ((finishTrees pl).shapes.getD 0 default).maskWidth)
    (hTies : bookTiesAtFinish Bk ⟨σ.block.place, 1⟩ ⟨b.place, 0⟩ pl = true)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (hos : os = (H2U.p12OfMade Zp.made).nums.first) (j : ℕ)
    (hsrc : ∀ o ∈ os, o.2 = Fmt.TreeSource.own j)
    (hj : treesTo cF.blocksInOrder pre.length = j)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (patch : Local W₀ Rc ProofFile.Inst Tr → Front Y → T12 → Local W₀ Rc ProofFile.Inst Tr → Front Y → T12)
    (hP₁ : ∀ w fr T, patch w fr T w fr = T)
    (hP₂ : ∀ w fr T, Blind.Agree (J.rec₀ w fr) T → ∀ w' fr',
      Blind.Agree (J.rec₀ w' fr') (patch w fr T w' fr'))
    (K : OnBytes.Codes)
    (hasks : ∀ (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y)
      (ca : CsAll (restMember (V := Local W₀ Rc ProofFile.Inst Tr) J Js).part.carries),
      midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) →
      carriedAt Bk k 0 ⟨σ.block.place, 1⟩ (restMember (V := Local W₀ Rc ProofFile.Inst Tr) J Js).part =
        .ok ca →
      ∃ Dp cc Rw, Dp.ts.length = os.length ∧
        ShapeAsksD { J with rec₀ := (patch m.st.input (restFront J m)
            (stateAtFirstChainTest Zp x
              ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
                ⟨σ.block.place, 1⟩).cut (firstLen J.p.nums.stages)))) }
          m.st.input (restFront J m) (carriedCoins J (stretches _ ca)) (heardIn J m) K Dp ∧
        DataAsks { J with rec₀ := (patch m.st.input (restFront J m)
            (stateAtFirstChainTest Zp x
              ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
                ⟨σ.block.place, 1⟩).cut (firstLen J.p.nums.stages)))) }
          m.st.input (restFront J m) (carriedCoins J (stretches _ ca)) (heardIn J m) Dp cc Rw) :
    ∃ (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y)
      (ca : CsAll (restMember (V := Local W₀ Rc ProofFile.Inst Tr) J Js).part.carries),
      midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) ∧
      carriedAt Bk k 0 ⟨σ.block.place, 1⟩ (restMember (V := Local W₀ Rc ProofFile.Inst Tr) J Js).part =
        .ok ca ∧
      OnEntry Face.own J Js K 0 os (restMember J Js) ca m
        (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
          ⟨σ.block.place, 1⟩) := by
  subst hJ
  have hp := numbersL_at_head h
  have St := stands_of_cut h hR _ hp rfl Js (hs.trans hp) ho fs σ hσ hg (pre ++ [b]) t hcut
  obtain ⟨c, m, hm, hca, -, h5⟩ := five_L h hρ hR (doorAtL Zp) D readers closing pl Js hs ho fs σ hσ
    hg hT hrun hc (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
  refine ⟨m, c.2.1.2.2, hm, hca, ?_⟩
  have htr := trees_first h.laid.planOk hR hrun (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers
    closing pl Js σ pre b t St hc hgK hfit hW hTies os hos j hsrc hj
    (storedShown (P.storedWords w₀ rc) r.run.storedAsked) m hm c.2.1.2.2 hca
  exact onEntry_at_firstChainTest h hR D readers closing pl _ rfl Js hJs fs σ hσ (pre ++ [b]) t St
    hrun hc patch hP₁ hP₂ K 0 os m hm c.2.1.2.2 _ rfl h5 (hasks m _ hm hca) htr

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.stands_of_cut
#print axioms ProofFile.Honest.K12.Sim2.onEntry_at_run
