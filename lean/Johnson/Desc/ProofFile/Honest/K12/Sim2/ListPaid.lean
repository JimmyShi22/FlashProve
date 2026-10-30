-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the clause of the rule at the first chain's last test, with what is left by name.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/ListPaid.lean: OnAtRun₁ at the list of the first chain's last
test, with the patch (recAtStand, AtFile/ClosingStand.lean). What stays is one
structure at each stand, LeftAtStand, and public premises.

  LeftAtStand   at a stand: ok: the words in front are below the prime (ok_of_inside,
                OkAtInside.lean, pays it from SaidOk); shape: a test at the simulators' state T; fits: FitsAtL at the plain data; rowsSay: THE CLAUSE ON VALUES:
                the rows that the group takes in say their claims of the sender's words
  onAtRun_paid  the statement

Paid here, at every stand: the door and the agreement; FiveAt; the first opening's columns; that the
sender's text returns; Reach at 354 with the run's own state; that state is the simulators'. No
property of the protocol is claimed: the rule moves the debt and pays none of it.
NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head). This
file's ground. First kind: hR, hrun, hleft (LeftAtStand's five fields read the run at its coins), T: they read k, ρ, rc. Second kind: the run's ready gives that the index is in
range and has a trace: a law names the relation. hρ: ρ and the description alone: public. Made terms and lemmas that
lift the bar: none: the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.AsksAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim2.CarryAtFirst
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingStand

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks fieldPrimeWord viewWordsBelowPrime)
open VerifiableInference.Desc.K12 (T12 P12 enterFinish)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open ProofFile.Honest.Sh (testSh claimsB)
open H2K.First (Plain Seat1)
open H2K.Member (codesFull)
open OnBytes (TreeLay)
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb VerifiableInference.Desc
  VerifiableInference.Desc.Ground.Sh

variable {W₀ Rc Tr : Type}

/-- **What is left at a stand.** n: the rounds in front of the test. T: the simulators' state. -/
structure LeftAtStand {Y : Type} (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y) (D : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing) (pl : K2.SwitchPlace)
    (n : ℕ) (T : T12) (mem : ℕ → Stretch) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y) : Prop where
  ok : viewWordsBelowPrime ⟨m.seen.take n, []⟩ = true
  shape : frontFiveB J.p codesFull (testSh T) = true
  fits : ∀ Dp : Plain, FrontAsksD (atStand J m.st.input (restFront J m) T)
      m.st.input (restFront J m) codesFull Dp →
    ∃ (s' : Seat1) (u' : ℕ) (Ly : TreeLay), FitsAtL J.p pl Dp s' u' Ly
  rowsSay : ∀ Rw : Johnson.Prover.Send.Rows,
    carryRows D readers closing pl m.st.input (heardL (restFront J m))
      (carriedCoins J mem).mem = .ok Rw →
    ∀ G, T.st.groups[T.g]? = some G →
      AllSay rdE (begun T.st T.g G) (runRows T.st G).toList
        (ProofFile.Honest.K12.wordsAt (begun T.st T.g G) (layoutOf T.st G)
          (plainL Rw (J.first m.st.input (restFront J m) (carriedCoins J mem))))

/-- **The clause of the rule at this list.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem onAtRun_paid {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀) {Ky X₀ Y : Type} {Bk : ProverCoinCounts}
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
    (os : List (Fmt.Shape × Fmt.TreeSource))
    (L : Lettered Bk S ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y ProofFile.Inst)
    (hplace : L.place = J.p.place) (hrow : L.row = testPairs J Js)
    (hOn : L.On = OnEntry Face.own J Js codesFull 0 os)
    (hg : ((G.prover H).first.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J))
    (hT : tiesB Bk (H2U.p12OfMade Zp.made).place (membersL pl).length = true)
    (hfit : fitsL (H2U.p12OfMade Zp.made) pl = true)
    (hW : columnWidth (finishSending pl) 0 = ((finishTrees pl).shapes.getD 0 default).mainWidth +
      ((finishTrees pl).shapes.getD 0 default).maskWidth)
    (hos : os = (H2U.p12OfMade Zp.made).nums.first) (hos₁ : os.length = 1) (j : ℕ)
    (hsrc : ∀ o ∈ os, o.2 = Fmt.TreeSource.own j)
    (hfront : ∀ (blk : Block S ProofFile.Cl) (pre' t' : List (Block S ProofFile.Cl)),
      cF.blocksInOrder = pre' ++ blk :: t' → blk.place = J.p.place →
      pre'.length = 354 ∧
      ∃ (pre : List (Block S ProofFile.Cl)) (b : Block S ProofFile.Cl), pre' = pre ++ [b] ∧
        ((G.prover H).first.find? fun g => g.place == b.place) =
          some (K2.switchHalf (K2.coreSender K2.freshTable) D readers closing pl) ∧
        bookTiesAtFinish Bk ⟨J.p.place, 1⟩ ⟨b.place, 0⟩ pl = true ∧ treesTo cF.blocksInOrder pre.length = j)
    (hE : J.p.early = true) (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = a :: next :: rest) (FP : FormPub J.p a next rest)
    (hplan : planB J.p codesFull 1 = true)
    (hleft : ∀ (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y)
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
      LeftAtStand J D readers closing pl (pre'.flatMap (·.rounds)).length
        (stateAtFirstChainTest Zp x
          ((r.run.beforeAt (storedShown ((G.prover H).storedWords w₀ rc) r.run.storedAsked)
            ⟨L.place, 1⟩).cut (firstLen J.p.nums.stages))) (stretches _ ca) m) :
    OnAtRun₁ T ρ r L := by
  refine onAtRun_firstChainTest h.toAtMg T hρ hR hrun D readers closing pl J hJ Js hJs hs ho codesFull
    os L hplace hrow hOn hg hT hfit hW hos j hsrc
    (fun blk pre' t' c e => (hfront blk pre' t' c e).2)
    (fun w fr T' => recAtStand J w fr T') (fun w fr T' => atStand_here J w fr T')
    (fun w fr T' ha w' fr' => recAtStand_agrees ha w' fr') ?_
  intro m ca σ pre' t' hcut hσ hin hseen hc hca hm
  have left := hleft m ca σ pre' t' hcut hσ hin hseen hc hca hm
  have hJp : J.p = H2U.p12OfMade Zp.made := by rw [hJ]; rfl
  have hp : J.p = (fourOf Np).L := hJp.trans (numbersL_at_head h.toAtMg)
  have hfrN : J.fresh.isNone = false := by rw [hJ]; rfl
  have hpl : σ.block.place = L.place := (Blind.testSide_place hσ).trans hplace.symm
  have hpl' : σ.block.place = J.p.place := hpl.trans hplace
  obtain ⟨h354, pre, b, e₀, hgK, hTies, hj⟩ := hfront σ.block pre' t' hcut hpl'
  have hg' : ((G.prover H).first.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J) := by
    rw [hpl']
    exact hg
  have St := stands_of_cut h.toAtMg hR J hp hfrN Js (hs.trans (numbersL_at_head h.toAtMg)) ho [] σ hσ
    hg' pre' t' hcut
  rw [← hpl] at hc hca hm left
  subst hJ
  obtain ⟨c, m₁, hm₁, hca₁, -, f5⟩ := five_L h.toAtMg hρ hR (doorAtL Zp) D readers closing pl Js hs ho
    [] σ hσ hg' hT hrun hc (storedShown ((G.prover H).storedWords w₀ rc) r.run.storedAsked)
  obtain rfl : m₁ = m := Option.some.inj (Except.ok.inj (hm₁.symm.trans hm))
  have eF : firstLen (H2U.p12OfMade Zp.made).nums.stages = 2 + a.k := by
    show firstLen (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl :
      TestJob (Local W₀ Rc ProofFile.Inst Tr) Y).p.nums.stages = _
    rw [hst]
    rfl
  have hheard := f5.heardFit
  subst e₀
  obtain ⟨Rw, hRw⟩ := carry_returns_first h.toAtMg.laid.planOk hR hrun (H2U.p12OfMade Zp.made)
    (doorAtL Zp) D readers closing pl Js σ pre b t' St hc hgK hfit
    (by rw [hpl']; exact hTies) [] m₁ hm ca hca
  rw [← hpl]
  exact asks_at_run h hR D readers closing pl _ rfl Js [] σ hσ _ (pre ++ [b]) t' _ St h354 hrun hc m₁
    hm left.ok _ _ rfl os (stretches _ ca) (atStand_here _ _ _ _) hE left.shape a next rest
    hst FP (by
      have e' := hheard
      rw [show firstLen (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl :
        TestJob (Local W₀ Rc ProofFile.Inst Tr) Y).p.nums.stages = 2 + a.k from eF] at e'
      show drawsFit _ (m₁.st.lately (firstLen (H2U.p12OfMade Zp.made).nums.stages)) = true
      rw [eF]
      exact e') hos₁ hplan left.fits hRw (left.rowsSay Rw hRw)

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.LeftAtStand
#print axioms ProofFile.Honest.K12.Sim2.onAtRun_paid
