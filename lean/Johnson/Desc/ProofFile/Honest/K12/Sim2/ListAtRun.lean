-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the list of the first chain's last test in the form of the rule on On at a run.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/ListAtRun.lean: OnAtRun₁ (Law/OwedAtRun.lean) at a list of the
first chain that holds the parts of jobL at doorAtL with their simulators, at the condition OnEntry.
So the list pays its own clause at the run, beside lists that pay through the rule's other road.

  AsksAtStand        the two clauses ShapeAsksD, DataAsks at the state that stands in: the hasks of
                     onEntry_at_run, by name: THE ONE CLAUSE ON VALUES that this theorem does not pay
  onAtRun_firstChainTest   the statement; its premise hasks asks AsksAtStand at every stand of the
                     run, and hands its payer the invariant at the stand (InsideOf), the rounds, the
                     carried values, called and the stand's equation

Premises on the filling, the book and the plan as in onEntry_at_run. No property of the protocol is
claimed: the rule moves the debt and pays none of it.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RunAtFirstChainTest
import Johnson.Desc.ProofFile.Honest.Law.OwedAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof

variable {W₀ Rc Tr : Type}

/-- **The two clauses at the state that stands in**, at one stand. -/
def AsksAtStand {Y : Type} (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y)
    (patch : Local W₀ Rc ProofFile.Inst Tr → Front Y → T12 → Local W₀ Rc ProofFile.Inst Tr → Front Y → T12)
    (T : T12) (K : OnBytes.Codes) (os : List (Fmt.Shape × Fmt.TreeSource))
    (mem : ℕ → Stretch) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y) : Prop :=
  ∃ Dp cc Rw, Dp.ts.length = os.length ∧
    ShapeAsksD { J with rec₀ := (patch m.st.input (restFront J m) T) }
      m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) K Dp ∧
    DataAsks { J with rec₀ := (patch m.st.input (restFront J m) T) }
      m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) Dp cc Rw

/-- **The clause of the rule at this list.** -/
theorem onAtRun_firstChainTest {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Ky X₀ Y : Type} {Bk : ProverCoinCounts}
    {H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk W₀ Rc Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc}
    {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (T : ThreadsP (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k ρ = .ok r)
    (D : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing)
    (pl : K2.SwitchPlace) (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y)
    (hJ : J = jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl)
    (Js : SimJob ProofFile.Inst) (hJs : Js.rec₀ = stateAtFirstChainTest Zp)
    (hs : Js.p = H2U.p12OfMade Zp.made) (ho : Js.own = false)
    (K : OnBytes.Codes) (os : List (Fmt.Shape × Fmt.TreeSource))
    (L : Lettered Bk S ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y ProofFile.Inst)
    (hplace : L.place = J.p.place) (hrow : L.row = testPairs J Js)
    (hOn : L.On = OnEntry Face.own J Js K 0 os)
    (hg : ((G.prover H).first.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J))
    (hT : tiesB Bk (H2U.p12OfMade Zp.made).place (membersL pl).length = true)
    (hfit : fitsL (H2U.p12OfMade Zp.made) pl = true)
    (hW : columnWidth (finishSending pl) 0 = ((finishTrees pl).shapes.getD 0 default).mainWidth +
      ((finishTrees pl).shapes.getD 0 default).maskWidth)
    (hos : os = (H2U.p12OfMade Zp.made).nums.first) (j : ℕ)
    (hsrc : ∀ o ∈ os, o.2 = Fmt.TreeSource.own j)
    (hfront : ∀ (blk : Block S ProofFile.Cl) (pre' t' : List (Block S ProofFile.Cl)),
      cF.blocksInOrder = pre' ++ blk :: t' → blk.place = J.p.place →
      ∃ (pre : List (Block S ProofFile.Cl)) (b : Block S ProofFile.Cl), pre' = pre ++ [b] ∧
        ((G.prover H).first.find? fun g => g.place == b.place) =
          some (K2.switchHalf (K2.coreSender K2.freshTable) D readers closing pl) ∧
        bookTiesAtFinish Bk ⟨J.p.place, 1⟩ ⟨b.place, 0⟩ pl = true ∧ treesTo cF.blocksInOrder pre.length = j)
    (patch : Local W₀ Rc ProofFile.Inst Tr → Front Y → T12 → Local W₀ Rc ProofFile.Inst Tr → Front Y → T12)
    (hP₁ : ∀ w fr T, patch w fr T w fr = T)
    (hP₂ : ∀ w fr T, Blind.Agree (J.rec₀ w fr) T → ∀ w' fr',
      Blind.Agree (J.rec₀ w' fr') (patch w fr T w' fr'))
    (hasks : ∀ (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y)
      (ca : CsAll (restMember (V := Local W₀ Rc ProofFile.Inst Tr) J Js).part.carries)
      (σ : Side S ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y ProofFile.Inst)
      (pre' t' : List (Block S ProofFile.Cl)), cF.blocksInOrder = pre' ++ σ.block :: t' →
      testSide cF.blocksInOrder J Js [] = some σ →
      InsideOf .own Bk 0 (G.prover H).first σ.block (T.I₁ pre'.length) (σ.roundsTo 1) k m
        (envOf (H.storedWords w₀ rc) (fun _ _ => none)
          (r.run.played.1.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1))) →
      m.seen = roundsOf (r.run.played.1.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1)) →
      r.called ⟨L.place, 1⟩ = true →
      carriedAt Bk k 0 ⟨L.place, 1⟩ (restMember (V := Local W₀ Rc ProofFile.Inst Tr) J Js).part = .ok ca →
      midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k ρ ⟨L.place, 1⟩ =
        .ok (some m) →
      AsksAtStand J patch (stateAtFirstChainTest Zp x
        ((r.run.beforeAt (storedShown ((G.prover H).storedWords w₀ rc) r.run.storedAsked)
          ⟨L.place, 1⟩).cut (firstLen J.p.nums.stages))) K os (stretches _ ca) m) :
    OnAtRun₁ T ρ r L := by
  subst hJ
  intro σ hσ u hu pre' t' hcut m ca hin hseen hca hc hmid hfr
  have hpl : σ.block.place = L.place := side_place hσ
  have hσ' : testSide cF.blocksInOrder (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) Js [] =
      some σ := by
    unfold testSide
    rw [← hplace, ← hrow]
    exact hσ
  have hp := numbersL_at_head h
  obtain ⟨-, hmem, -⟩ := (ProofFile.Honest.K12.Light.first_any_head_L (V := Local W₀ Rc ProofFile.Inst Tr) h _ Js hp rfl
    (hs.trans hp) ho).2.2 [] σ hσ'
  rw [hOn, hfr]
  rw [hmem] at hu
  rcases List.mem_cons.1 hu with rfl | hu'
  · intro hn
    cases hn
  obtain rfl := List.mem_singleton.1 hu'
  obtain ⟨pre, b, rfl, hgK, hTies, hj⟩ := hfront σ.block pre' t' hcut (hpl.trans hplace)
  have hpl' : σ.block.place = (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl :
      TestJob (Local W₀ Rc ProofFile.Inst Tr) Y).p.place := hpl.trans hplace
  have hmain := onEntry_at_run h hρ hR D readers closing pl _ rfl Js hJs hs ho [] σ hσ' pre b t'
    hcut (by rw [hpl']; exact hg) hT hgK hfit hW (by rw [hpl']; exact hTies) os hos j hsrc hj hrun
    (by rw [hpl]; exact hc) patch hP₁ hP₂ K (fun m₀ ca₀ hm₀ hca₀ => by
      rw [hpl] at hm₀ hca₀
      have e₁ : ca₀ = ca := Except.ok.inj (hca₀.symm.trans hca)
      have e₂ : m₀ = m := by
        have hmid' : orRefused (midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k ρ
            ⟨L.place, 1⟩) = .ok m := hmid
        rw [hm₀] at hmid'
        exact Except.ok.inj (show (Except.ok m₀ : Except Refusal _) = .ok m from hmid')
      subst e₁
      subst e₂
      rw [hpl]
      exact hasks m₀ ca₀ σ _ t' hcut hσ' hin hseen hc hca₀ hm₀)
  rw [hpl] at hmain
  obtain ⟨m₁, c₁, g₁, g₂, g₃⟩ := hmain
  have e₁ : c₁ = ca := Except.ok.inj (g₂.symm.trans hca)
  have hmid' : orRefused (midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k ρ
      ⟨L.place, 1⟩) = .ok m := hmid
  rw [g₁] at hmid'
  have e₂ : m₁ = m := Except.ok.inj (show (Except.ok m₁ : Except Refusal _) = .ok m from hmid')
  subst e₁
  subst e₂
  exact g₃

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.AsksAtStand
#print axioms ProofFile.Honest.K12.Sim2.onAtRun_firstChainTest
