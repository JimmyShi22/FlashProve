-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the two clauses at a run, at the simulators' own state.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/AsksAtRun.lean: AsksAtStand at the state that stateAtFirstChainTest
makes of the run's front, at a called second member of the first chain's last test: the record of
asksAtStand_of_front is that state, since the state reached is the run's own fold's
(door_at_firstChainTest), and reach_below_of_fold (Thread/SaidOk.lean) reaches it.

  reach_of_stand   the fold of a stand reaches its state under below
  asks_at_run               the statement

What stays a premise: hok: every word that the rounds in front show is below the prime. pre's length
is 354. h5, hE, hst, FP, hplan, hfits, hheard, hRw, hs as in asksAtStand_of_front, at this record:
hs is the clause on values. The test on the open rows is paid by claimsB_at_L (AtFile/ClosingClaims.lean). No property of the protocol is claimed.
NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head). This
file's ground. First kind: hR, hrun, hc, hm, hok, h5, hfits, hheard, hRw, hs: they read k, ρ, rc. Second kind: the run's ready gives that the index is in
range and has a trace: a law names the relation. Made terms and lemmas that
lift the bar: none: the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.AsksAtFirstChainTest
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingClaims

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks fieldPrimeWord viewWordsBelowPrime)
open VerifiableInference.Desc.K12 (T12 P12 enterFinish)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open ProofFile.Honest.Sh (testSh claimsB)
open H2K.First (Plain Seat1)
open H2K.Member (codesFull)
open OnBytes (TreeLay)
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb VerifiableInference.Desc
  VerifiableInference.Desc.Ground.Sh

variable {W₀ Rc Tr : Type}

/-- **The fold of a stand reaches its state.** -/
theorem reach_of_stand {Zp : ProofFile.Pub} {cF : Chain S ProofFile.Cl} {pre t : List (Block S ProofFile.Cl)}
    {blk : Block S ProofFile.Cl} (hcut : cF.blocksInOrder = pre ++ blk :: t) (z : ProofFile.InstPub) {s : S}
    {rs : List Fmt.RoundView} {cs : List OpenedColumn} {stored : Nat → Nat → Option (List UInt64)}
    {tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table)} {ds : List Fmt.Drawn}
    (hok : viewWordsBelowPrime ⟨rs, []⟩ = true) (hst : ∀ i x u, stored i x = some u → ∀ a ∈ u, a < fieldPrimeWord)
    (hfold : foldBlocks 0 pre (ProofFile.startS Zp z) rs cs = .ok (s, [], []))
    (hfill : fillCols (readsOf 0 0 stored tree (pre.flatMap (·.rounds)) ds) [] = .ok cs) :
    Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) pre.length (z, s) := by
  have hw := fillCols_words _ _ _ (readsOf_words 0 0 stored tree hst _ _)
    (fun _ hx => by cases hx) hfill
  have ht : cF.blocksInOrder.take pre.length = pre := by
    rw [hcut]
    simp
  exact reach_below_of_fold hok hw pre.length (by rw [hcut]; simp) s [] [] (by rw [ht]; exact hfold)

/-- **The two clauses at a run**, at the simulators' state at the run's front.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem asks_at_run {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀) {Ky X₀ Y Pb : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k = .ok R)
    (D : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing)
    (pl : K2.SwitchPlace) (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y)
    (hJ : J = jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl)
    (Js : SimJob Pb) (fs : List (Fall S))
    (σ : Side S ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (hσ : testSide cF.blocksInOrder J Js fs = some σ)
    (u : Member (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (pre t : List (Block S ProofFile.Cl)) (i : ℕ) (St : StandsAt cF.blocksInOrder R.first σ u pre t i)
    (hlen : pre.length = 354)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y)
    (hm : midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ =
      .ok (some m))
    (hok : viewWordsBelowPrime ⟨m.seen.take (pre.flatMap (·.rounds)).length, []⟩ = true)
    (patch : Local W₀ Rc ProofFile.Inst Tr → Front Y → T12 → Local W₀ Rc ProofFile.Inst Tr → Front Y → T12)
    (T : T12)
    (hTs : T = stateAtFirstChainTest Zp x
      ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
        ⟨σ.block.place, u.number⟩).cut i))
    (os : List (Fmt.Shape × Fmt.TreeSource)) (mem : ℕ → Stretch)
    (hP₁ : patch m.st.input (restFront J m) T m.st.input (restFront J m) = T)
    (hE : J.p.early = true) (h5 : frontFiveB J.p codesFull (testSh T) = true)
    (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = a :: next :: rest) (FP : FormPub J.p a next rest)
    (hheard : drawsFit (((H2K.JointK.laidOf J.p).take (2 + a.k)).map (·.1))
      (m.st.lately (firstLen J.p.nums.stages)) = true)
    (hos : os.length = 1) (hplan : planB J.p codesFull 1 = true)
    (hfits : ∀ Dp : Plain, FrontAsksD { J with rec₀ := (patch m.st.input (restFront J m) T) }
        m.st.input (restFront J m) codesFull Dp →
      ∃ (s' : Seat1) (u' : ℕ) (Ly : TreeLay), FitsAtL J.p pl Dp s' u' Ly)
    {Rw : Johnson.Prover.Send.Rows}
    (hRw : carryRows D readers closing pl m.st.input (heardL (restFront J m))
      (carriedCoins J mem).mem = .ok Rw)
    (hs : ∀ G, T.st.groups[T.g]? = some G →
      AllSay rdE (begun T.st T.g G) (runRows T.st G).toList
        (ProofFile.Honest.K12.wordsAt (begun T.st T.g G) (layoutOf T.st G)
          (plainL Rw (J.first m.st.input (restFront J m) (carriedCoins J mem))))) :
    AsksAtStand J patch T codesFull os mem m := by
  obtain ⟨m', T', a1, -, -, -, ⟨s, cs, hT, hf, hfill⟩, e⟩ := door_at_firstChainTest h.toAtMg hR σ u
    pre t i St hrun hc D readers closing pl Js fs (hJ ▸ hσ)
  obtain rfl : m' = m := Option.some.inj (Except.ok.inj (a1.symm.trans hm))
  have hr := reach_of_stand (Zp := Zp) St.cut x.pub hok (storedWords_lt P w₀ rc) hf hfill
  rw [hlen] at hr
  have he : enterFinish s = .ok T := by
    rw [hTs, e]
    exact hT
  exact asksAtStand_of_front h _ (doorAtL Zp) D readers closing pl J hJ patch T os mem m' hP₁ hr he
    hE h5 (claimsB_at_L h hr he h5) a next rest hst FP hheard hos hplan hfits hRw hs

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.reach_of_stand
#print axioms ProofFile.Honest.K12.Sim2.asks_at_run
