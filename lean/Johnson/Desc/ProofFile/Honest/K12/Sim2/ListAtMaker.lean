-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the clause of the rule at the first chain's last test, at the maker.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/ListAtMaker.lean: onAtRun_head (ListAtHead.lean) at the list that
the filling's own row lays, where onlineProverFromPublicFiles has returned at the filling: what stood on the filling and
the book is paid: the search at the test (last_test_found), at the finish (finish_found), the test on
the book at the members (hT_head_L) and at the finish (ties_at_maker). What stays: hleft
(LeftAtStand at each stand) and that the run's prover holds the maker's first list (hH). Beside it
the list's debt to BudDebts.

  onAtRun_at_maker   the statement
  budOwed_at_maker   budOwed_at_L at this list

No property of the protocol is claimed: the rule moves the debt and pays none of it.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListAtHead
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesLFound
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesLBook
import AtFullSide.K12.TiesAtHeadL
import Johnson.M1.BudTestL

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open H2K.Member (codesFull)

variable {W₀ : Type}

/-- **The clause of the rule at the filling's own list.** -/
theorem onAtRun_at_maker {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀)
    (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S' : OnBytes.HonestTrace.Sz) (Op : OnlineProverArguments)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o S' Op) = .ok A)
    {pl : K2.SwitchPlace} (hf : finishWritten = some pl)
    {Ky X₀ : Type} {H : Prover W₀ IndexCommitterCoins ProofFile.Inst Ky Cells X₀ Unit}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.B W₀ IndexCommitterCoins Ky Cells X₀ Unit} {w₀ : W₀}
    {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins A.B} {ρ : Draws}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst Ky Cells X₀ Unit}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (T : ThreadsP (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.B (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.B (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.B (G.prover H) w₀ rc x k ρ = .ok r)
    (hH : (G.prover H).first = A.H.first)
    (Tl : Local W₀ IndexCommitterCoins Inst Cells → Thread A.B S ProofFile.Cl (Local W₀ IndexCommitterCoins Inst Cells)
      (Local W₀ IndexCommitterCoins Inst Cells) Unit Inst)
    (Sd : Local W₀ IndexCommitterCoins Inst Cells → ℕ → Coins A.B → Mid (Local W₀ IndexCommitterCoins Inst Cells) Unit → Prop)
    (bs : List (Block S ProofFile.Cl))
    (hleft : ∀ (m : Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
      (ca : CsAll (restMember (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
        (jobOfLot I S' Zp A.G pl : TestJob _ Unit) (simulatorJobOfLot Zp)).part.carries)
      (σ : Side S ProofFile.Cl (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit
        ProofFile.Inst)
      (pre' t' : List (Block S ProofFile.Cl)), cF.blocksInOrder = pre' ++ σ.block :: t' →
      testSide cF.blocksInOrder (jobOfLot I S' Zp A.G pl : TestJob _ Unit) (simulatorJobOfLot Zp) [] =
        some σ →
      InsideOf .own A.B 0 (G.prover H).first σ.block (T.I₁ pre'.length) (σ.roundsTo 1) k m
        (envOf (H.storedWords w₀ rc) (fun _ _ => none)
          (r.run.played.1.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1))) →
      m.seen = roundsOf (r.run.played.1.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1)) →
      r.called ⟨(H2U.p12OfMade Zp.made).place, 1⟩ = true →
      carriedAt A.B k 0 ⟨(H2U.p12OfMade Zp.made).place, 1⟩
        (restMember (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
          (jobOfLot I S' Zp A.G pl : TestJob _ Unit) (simulatorJobOfLot Zp)).part = .ok ca →
      midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.B (G.prover H) w₀ rc x k ρ
        ⟨(H2U.p12OfMade Zp.made).place, 1⟩ = .ok (some m) →
      LeftAtStand (jobOfLot I S' Zp A.G pl : TestJob _ Unit) (widerRows S' Zp A.G)
        (fillReaders I Zp) (K2.lotClosingAt A.G.first.layout (K2.segmentsOf Zp A.G)) pl
        (pre'.flatMap (·.rounds)).length
        (stateAtFirstChainTest Zp x
          ((r.run.beforeAt (storedShown ((G.prover H).storedWords w₀ rc) r.run.storedAsked)
            ⟨(H2U.p12OfMade Zp.made).place, 1⟩).cut
              (firstLen (H2U.p12OfMade Zp.made).nums.stages))) (stretches _ ca) m) :
    OnAtRun₁ T ρ r ((rowOfJob Zp (jobOfLot I S' Zp A.G pl)).lay Tl Sd bs) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hZ, hG, -⟩ := atPure_ok hA
  have eZ : Zp = A.Z := Except.ok.inj (O.pub.symm.trans hZ)
  have hG' : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by rw [eZ]; exact hG
  have eG : Bs.G₀ = A.G := Option.some.inj (O.blank.symm.trans hG')
  have hfZ : finishAt Zp A.G = some pl := by
    rw [← eG, finish_at_head h.toAtMg O, hf]
  have hfit := fits_at_head h.toAtMg hf
  have hpm : pl ∈ K2.switchPlaces Zp A.G := by
    have e := hfZ
    unfold finishAt at e
    exact List.mem_of_find?_eq_some e
  have hpp : pl.place = ⟨1, none, 1, .K2⟩ := by
    have e := finishWritten_place
    rw [hf] at e
    exact Option.some.inj e
  have hqp : (H2U.p12OfMade Zp.made).place = ⟨1, none, 2, .K12⟩ := proxPlace Zp
  obtain ⟨f1, f2, f3, -, f5, f6, f7⟩ :=
    row_facts Zp (jobOfLot I S' Zp A.G pl : TestJob _ Unit) Tl Sd bs
  refine onAtRun_head h T hρ hR hrun (widerRows S' Zp A.G) (fillReaders I Zp)
    (K2.lotClosingAt A.G.first.layout (K2.segmentsOf Zp A.G)) hf _ rfl (simulatorJobOfLot Zp) f5 f6
    f7 _ f1 f2 f3 ?_ ?_ ?_ ?_ hleft
  · rw [hH]
    have e := last_test_found I o S' Op hA pl (by rw [← eZ]; exact hfZ)
      (by rw [← eZ]; exact hfit)
    rw [← eZ] at e
    show List.find? (fun g => g.place == (H2U.p12OfMade Zp.made).place) A.H.first = _
    rw [show (H2U.p12OfMade Zp.made).place = placeL from proxPlace Zp]
    exact e
  · have hB := ProofFile.Honest.K14.atPure_book_at_head h hA
    rw [ProofFile.Honest.K14.made_sends_at_files h.scope h.laid] at hB
    exact AtFullSide.K12.hT_head_L (X := Unit) h.toAtMg hB hG' hfZ (doorAtL Zp) (widerRows S' Zp A.G)
      (fillReaders I Zp) (K2.lotClosingAt A.G.first.layout (K2.segmentsOf Zp A.G))
  · rw [hH]
    have e := finish_found I o S' Op hA (p := pl) (by rw [← eZ]; exact hpm)
    rw [← eZ] at e
    exact e
  · show bookTiesAtFinish A.B ⟨(H2U.p12OfMade Zp.made).place, 1⟩ ⟨pl.place, 0⟩ pl = true
    rw [hqp, hpp]
    exact ties_at_maker h hA hf

/-- **The list's debt to BudDebts.** -/
theorem budOwed_at_maker {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) (I : WiderIn W₀) (S' : OnBytes.HonestTrace.Sz)
    (Gr : Ground) (pl : K2.SwitchPlace) {Bk : ProverCoinCounts}
    (Tl : Local W₀ IndexCommitterCoins Inst Cells → Thread Bk S ProofFile.Cl (Local W₀ IndexCommitterCoins Inst Cells)
      (Local W₀ IndexCommitterCoins Inst Cells) Unit Inst)
    (Sd : Local W₀ IndexCommitterCoins Inst Cells → ℕ → Coins Bk → Mid (Local W₀ IndexCommitterCoins Inst Cells) Unit → Prop)
    (bs : List (Block S ProofFile.Cl)) :
    Johnson.M1.BudOwed (P5J.F0T OnBytes.secondHashFunction Zp Np cF)
      ((rowOfJob Zp (jobOfLot I S' Zp Gr pl : TestJob _ Unit)).lay Tl Sd bs) :=
  budOwed_at_L h _ (jobOfLot I S' Zp Gr pl) (numbersL_at_head h) rfl (simulatorJobOfLot Zp)
    (numbersL_at_head h) rfl rfl rfl fun _ _ _ x => x

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.onAtRun_at_maker
#print axioms ProofFile.Honest.K12.Sim2.budOwed_at_maker
