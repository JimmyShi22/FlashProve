-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the condition OnEntry at a stand of a run, at the first chain's last test.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/EntryAtL.lean: at a called second member of the first chain's
last proximity test, at a run of the frame's walking prover, under the head: the condition OnEntry
(Entry.lean), at the stand that midAt returns and the run's own front, from three named parts: the
five clauses of the stand (FiveAt), the clause on the asks at the job that stands in, and the clause
on the first opening's columns (TreesAt). What is paid here: the clause door and the agreement, by
door_at_firstChainTest (DoorAtL.lean). The state that stands in is the job patched at that one stand with what
stateAtFirstChainTest makes of the run's front; patch is a letter with its two laws: it stands only on the real side.

  onEntry_at_firstChainTest   the statement

Conditional. Nothing here shows that ready or runC returns. The three parts are premises. The
condition reads the input and the rows: no later law may take it as a hypothesis on a run and speak
of the random values as sampled anew. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.Entry
import Johnson.Desc.ProofFile.Honest.K12.Sim2.DoorAtL

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof

variable {W₀ Rc Tr : Type}

/-- The two laws of the letter patch can be met: the job's state with T laid at one input and front. A
test that the letter is not empty: the one text of the patch is not this file's. -/
theorem patch_exists {A B : Type} (d : A → B → T12) :
    ∃ patch : A → B → T12 → A → B → T12, (∀ w fr T, patch w fr T w fr = T) ∧
      ∀ w fr T, Blind.Agree (d w fr) T → ∀ w' fr', Blind.Agree (d w' fr') (patch w fr T w' fr') := by
  classical
  refine ⟨fun w fr T w' fr' => if w' = w ∧ fr' = fr then T else d w' fr', fun w fr T => by simp,
    fun w fr T h w' fr' => ?_⟩
  by_cases c : w' = w ∧ fr' = fr
  · obtain ⟨rfl, rfl⟩ := c
    simpa using h
  · simp only [if_neg c]
    rfl

/-- **The condition at a run.** -/
theorem onEntry_at_firstChainTest {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Ky X₀ Y : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k = .ok R)
    (D : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing)
    (pl : K2.SwitchPlace) (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y)
    (hJ : J = jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl)
    (Js : SimJob ProofFile.Inst) (hJs : Js.rec₀ = stateAtFirstChainTest Zp) (fs : List (Fall S))
    (σ : Side S ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y ProofFile.Inst)
    (hσ : testSide cF.blocksInOrder J Js fs = some σ) (pre t : List (Block S ProofFile.Cl))
    (St : StandsAt cF.blocksInOrder R.first σ (restMember J Js) pre t (firstLen J.p.nums.stages))
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (patch : Local W₀ Rc ProofFile.Inst Tr → Front Y → T12 → Local W₀ Rc ProofFile.Inst Tr → Front Y → T12)
    (hP₁ : ∀ w fr T, patch w fr T w fr = T)
    (hP₂ : ∀ w fr T, Blind.Agree (J.rec₀ w fr) T → ∀ w' fr',
      Blind.Agree (J.rec₀ w' fr') (patch w fr T w' fr'))
    (K : OnBytes.Codes) (chain : ℕ) (os : List (Fmt.Shape × Fmt.TreeSource))
    (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y)
    (hm : midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m))
    (ca : CsAll (restMember (V := Local W₀ Rc ProofFile.Inst Tr) J Js).part.carries)
    (front : Before)
    (hfront : front =
      r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked) ⟨σ.block.place, 1⟩)
    (h5 : FiveAt J (stretches _ ca) m front)
    (hasks : ∃ Dp cc Rw, Dp.ts.length = os.length ∧
      ShapeAsksD { J with rec₀ := (patch m.st.input (restFront J m)
            (stateAtFirstChainTest Zp x (front.cut (firstLen J.p.nums.stages)))) }
        m.st.input (restFront J m) (carriedCoins J (stretches _ ca)) (heardIn J m) K Dp ∧
      DataAsks { J with rec₀ := (patch m.st.input (restFront J m)
            (stateAtFirstChainTest Zp x (front.cut (firstLen J.p.nums.stages)))) }
        m.st.input (restFront J m) (carriedCoins J (stretches _ ca)) (heardIn J m) Dp cc Rw)
    (htr : TreesAt J chain os (stretches _ ca) m front) :
    OnEntry Face.own J Js K chain os (restMember J Js) ca m front := by
  subst hfront
  obtain ⟨m', T, a1, a5, ag, hx, -, e⟩ := door_at_firstChainTest h hR σ (restMember J Js) pre t _ St hrun hc D
    readers closing pl Js fs (hJ ▸ hσ)
  obtain rfl : m' = m := Option.some.inj (Except.ok.inj (a1.symm.trans hm))
  have hfr := AtProof.restFront_seen J m' _ a5
  have hag : Blind.Agree (J.rec₀ m'.st.input (restFront J m'))
      (stateAtFirstChainTest Zp x ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
        ⟨σ.block.place, 1⟩).cut (firstLen J.p.nums.stages))) := by
    have e' : stateAtFirstChainTest Zp x ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
        ⟨σ.block.place, 1⟩).cut (firstLen J.p.nums.stages)) = T := e
    rw [e']
    have g := ag (restFront J m') hfr
    rw [hJ]
    rw [hJ] at g
    exact g
  refine onEntry_of_parts Face.own J Js K chain os ca m' _
    (patch m'.st.input (restFront J m')
      (stateAtFirstChainTest Zp x ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
        ⟨σ.block.place, 1⟩).cut (firstLen J.p.nums.stages))))
    (hP₂ _ _ _ hag) h5 ?_ hasks htr
  rw [hP₁, hJs]
  show _ = stateAtFirstChainTest Zp m'.st.input.x _
  rw [hx]

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.patch_exists
#print axioms ProofFile.Honest.K12.Sim2.onEntry_at_firstChainTest
