-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the clause of the rule at the first chain's last test, public premises paid.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/ListAtHead.lean: onAtRun_paid (ListPaid.lean) under the head,
at the written finish: every public premise is paid. What stays: T, the rule's own letter: the thread at
its coins, the heaviest; on the filling hg, hgK; on the book hT, hTies (payers: ties_at_laid_L,
ties_at_maker); at a stand hleft (LeftAtStand). hf: that the lot's finish is the written one at the
maker's ground: finish_at_head, at ListAtMaker.

  onAtRun_head   the statement

No property of the protocol is claimed: the rule moves the debt and pays none of it.
NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head). This
file's ground. First kind: hR, hrun, hleft, T: they read k, ρ, rc. Second kind: the run's ready gives that the index is in
range and has a trace: a law names the relation. hρ: ρ and the description alone: public. Made terms and lemmas that
lift the bar: none: the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListPaid
import Johnson.Desc.ProofFile.Honest.K12.Sim2.PublicAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim2.KeystoneL

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain viewWordsBelowPrime)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open H2K.Member (codesFull piLFull)

variable {W₀ Rc Tr : Type}

/-- **The clause of the rule, public premises paid.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem onAtRun_head {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀) {Ky X₀ Y : Type} {Bk : ProverCoinCounts} {H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk W₀ Rc Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc}
    {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (T : ThreadsP (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k ρ = .ok r)
    (D : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing)
    {pl : K2.SwitchPlace} (hf : finishWritten = some pl)
    (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y)
    (hJ : J = jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl)
    (Js : SimJob ProofFile.Inst) (hJs : Js.rec₀ = stateAtFirstChainTest Zp)
    (hs : Js.p = H2U.p12OfMade Zp.made) (ho : Js.own = false)
    (L : Lettered Bk S ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y ProofFile.Inst)
    (hplace : L.place = J.p.place) (hrow : L.row = testPairs J Js)
    (hOn : L.On = OnEntry Face.own J Js codesFull 0 osL)
    (hg : ((G.prover H).first.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J))
    (hT : tiesB Bk (H2U.p12OfMade Zp.made).place (membersL pl).length = true)
    (hgK : ((G.prover H).first.find? fun g => g.place == pl.place) =
      some (K2.switchHalf (K2.coreSender K2.freshTable) D readers closing pl))
    (hTies : bookTiesAtFinish Bk ⟨J.p.place, 1⟩ ⟨pl.place, 0⟩ pl = true)
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
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hJp : J.p = H2U.p12OfMade Zp.made := by rw [hJ]; rfl
  have hfit := fits_at_head h.toAtMg hf
  have hW := width_at_finish hf
  have hos : osL = (H2U.p12OfMade Zp.made).nums.first := osL_at_head h.toAtMg
  obtain ⟨a, next, rest, hst, FP⟩ := form_public h.toAtMg
  have hplL : J.p.place = placeL := by
    rw [hJp, (seated_written h.toAtMg).2]
    decide +kernel
  refine onAtRun_paid h T hρ hR hrun D readers closing pl J hJ Js hJs hs ho osL L hplace hrow hOn hg hT
    hfit hW hos osL_length 76 (fun o ho' => source_at_head h.toAtMg o (hos ▸ ho'))
    (fun blk pre' t' c e => ?_) (by rw [hJp]; exact early_public h.toAtMg) a next rest
    (by rw [hJp]; exact hst) (by rw [hJp]; exact FP)
    (by
      rw [hJp, numbersL_at_head h.toAtMg]
      exact planB_head_L h.toAtMg) hleft
  obtain ⟨h354, pre, b, e₀, hb, hj⟩ := front_public h.toAtMg O hf c (e.trans hplL)
  refine ⟨h354, pre, b, e₀, ?_, ?_, hj⟩
  · rw [hb]
    exact hgK
  · rw [hb]
    exact hTies

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.onAtRun_head
