-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the request's own test at a run, at the wide filling's return.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/ListWAtReturn.lean: CONDITIONAL. Statements with their
proofs; no
definition.

Can the hypotheses be met together at a real run? NOT KNOWN: that the maker returns at the wide
filling (hAr), that ready and runC return there, that the part is called and that a value of
`ThreadsP` is had there, is not shown here.

What is here. `onAtRun_W_lines_numbers_paid` (Sim2/ListWTreesNumbers.lean) AT THE RETURN OF THE WIDE
FILLING `onlineProverPartsInUse`: the four premises on the filling, hheard, hatO, hGf, hA, hmsg and hg
are
paid.

  `k1_lot_there`, `k1_lot_alone`   the two premises of `k1_first_fill`
  (Honest/K1/Law/HalfAtFill.lean) at
      this filling: K1's lot is among its lots; every other lot has no half of the kind K1 with a
      link. No premise. After the pattern of `hex_wM`, `ho_wM` (Honest/K1/Law/WSideAtFill.lean).
  `eight_blocks_at_head`   under the head the shared chain's plan makes eight blocks.
  `onAtRun_W_lines_at_return`   **the statement.**

THE END IS `OnAtRun₃` ITSELF.

OF THE SENDERS' 71 PREMISES FIVE ARE LEFT, BY NAME, ALL ON THE BOOK (to the letter
the
five ends of `own_proof_at`, Sim2/OwnProofBook.lean; not called here): hbkI
·
hbkW · hbkF · hbkO · hnotO.
ALL THE PREMISES, SORTED. PUBLIC: h (the stronger head `AtMgA`). ON THE FILLING: hAr (the maker
returns Ar) · hL (the filling's last list is not empty) · hP (the rule's prover is the maker's). THE
RUN: T · hρ · hR · hrun. WHICH OBJECTS: hM (M is the job that `jobRealW` makes there) · hq (the list
bears the row of `lotW` at M). ON THE BOOK: hT and the five. LEFT AT EVERY STAND:
hlines (`LeftAtOwnLines`: six tests on the state on entry, and the rows' sentence `SaysAt`, WHICH
HAS NO PAYER).
THE PROVER ALONE IS THE RETURN's: the description is the head's, and Bk is any book.

The wide filling is defined in Honest/K1/Law/WSideAtFill.lean.
This file does not show that the maker returns at it.
Two things are not shown here or beneath:
Sim2/ListU.lean's head names them.

By. `k1_first_fill` · `half_w_wM` · `sendings_found` (Sim2/TreesSharedTest.lean) ·
`own_test_found_of_laid` (Sim2/FoundOwnAndShared.lean) · `sendPub_at_head`
(K12/AtProof/HalfAtPure.lean)
· `Meaning.K2.blank_first` · `ready_ok` · `k13_wHeard_at_head`, `rounds356W`
(AtFullSide/K13/WFillAtHead.lean:
W's data hears 48,290 challenges, the written count of rounds in front of W's sender).

Limits. Those of the files named; Sim2/PublicAtW.lean and Sim2/JobsAtW.lean lie
beneath. Nothing on completeness, soundness or hiding.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListWTreesNumbers
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesSharedTest
import Johnson.Desc.ProofFile.Honest.K1.Law.HalfAtFill
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfAtPure
import AtFullSide.K13.WFillAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain FileDescription Oracle Place KindName)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.K1 (qFull)
open VerifiableInference.Desc.K13.Law (wMsgFull wMsg_written)
open H2K.Member (codesFull piWFull)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open Johnson.Prover.Send (col shapeAt)
open ProofFile.Honest.K14 (SendJob jobOmega Ask columnOf sendingsFit)

variable {W₀ : Type}

attribute [local irreducible] P2Law.ProofPlan.WP

/-- **K1's lot is among this filling's lots.** No premise. -/
theorem k1_lot_there (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Zq : Pub) (G : Ground) :
    ∃ M ∈ (onlineProverPartsInUse I o S O).lots, M.halves Zq G =
      K1.lotHalves (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => (⟨w.x, ⟨w.trace, I.weights Zq w.w₀,
                w.rc⟩⟩ : K1.PlaceIn ProofFile.Inst)) (K1.lotNo o Zq) (K1.lotData S) Zq G := by
  refine ⟨HLot.byPub I.weights (LongLots.plain o S O).k1, ?_, rfl⟩
  rw [widerFillAtCPUOWM_lots, widerFillAt_lots]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.2 ⟨_, List.Mem.head _, rfl⟩)))

/-- **Every lot of this filling has no half of the kind K1 with a link, or is K1's.** No premise. -/
theorem k1_lot_alone (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Zq : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots,
      (∀ g ∈ M.halves Zq G, g.place.kind = .K1 → g.place.link = none) ∨
      M.halves Zq G =
        K1.lotHalves (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => (⟨w.x, ⟨w.trace, I.weights Zq w.w₀,
                  w.rc⟩⟩ : K1.PlaceIn ProofFile.Inst)) (K1.lotNo o Zq) (K1.lotData S) Zq G := by
  intro M hM
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((hM | rfl) | rfl) | rfl
  · rw [widerFillAt_lots] at hM
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hM
    by_cases k : q.2 = .K1
    · have e' : q = (HLot.byPub I.weights (LongLots.plain o S O).k1, .K1) :=
        List.inj_on_of_nodup_map widerPairs_nodup hq (List.Mem.head _) k
      rw [e']
      exact .inr rfl
    · refine .inl fun g hg hk => ?_
      have hk' := (FirstFill.widerKinds I o S O Zq G).all q hq g hg
      exact absurd (hk'.symm.trans hk) k
  · refine .inl fun g hg hk => ?_
    have hk' := closeLotAt_kinds I S Zq G g hg
    rw [hk] at hk'
    cases hk'
  · refine .inl fun g hg hk => ?_
    have hk' := proxLotAt_kinds I S Zq G g hg
    rw [hk] at hk'
    cases hk'
  · refine .inl fun g hg _ => ?_
    rw [wLotAt_halves] at hg
    obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 (Option.mem_toList.1 hg)
    rfl

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- Under the head the shared chain's plan makes eight blocks. -/
theorem eight_blocks_at_head (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) :
    ∃ b1 b2 b3 b4 b5 b6 b7 b8, Desc.K14.blocks (VerifiableInference.Desc.K1.qAt Zp Np) =
      some [b1, b2, b3, b4, b5, b6, b7, b8] := by
  obtain ⟨_, _, hw⟩ := facts_at_head h
  unfold Desc.K14.blocks
  rw [hw]
  exact ⟨_, _, _, _, _, _, _, _, rfl⟩

/-- CONDITIONAL on all its premises. **The clause of the rule at the list that bears the lot's row,
at
the wide filling's return: of the senders' 71 premises five are left, all on the book.** -/
theorem onAtRun_W_lines_at_return {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀) (I : WiderIn W₀)
    (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {Ar : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hAr : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S' O) =
      .ok Ar)
    (hL : secondW (X := Unit) I OnBytes.secondHashFunction S' O Ar.Z Ar.G ≠ []) {Bk : ProverCoinCounts}
    {H : Prover W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk W₀ IndexCommitterCoins OnBytes.TableKey Cells Unit Unit}
    (hP : G.prover H = Ar.H) {w₀ : W₀} {rc : IndexCommitterCoins}
    {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (T : ThreadsP (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k ρ = .ok r)
    (M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (hM : jobRealW S' (P5J.F0T OnBytes.secondHashFunction Zp Np cF) enterOwn O.pile (K1.lotNo OnBytes.secondHashFunction Zp)
      (fun w => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩) (fun w => I.weights Zp w.w₀)
      (fun P w => randAt P w.rc) Zp Ar.G = some M)
    (L : Lettered Bk (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl
      (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (hq : L.bare = rowAtW Face.own OnBytes.secondHashFunction Zp Np cF M.toRun.toTest)
    -- on the book
    (hT : tiesB Bk placeW M.toRun.toTest.members.length = true)
    (hbkI : k1CutFits Bk ⟨placeW, 1⟩ 0 senderI PIw rideIw 4 = true)
    (hbkW : k1CutFits Bk ⟨placeW, 1⟩ 1 senderW PWw rideWw 0 = true)
    (hbkF : k1CutFits Bk ⟨placeW, 1⟩ 3 senderW PWw rideWw 1 = true)
    (hbkO : Light.cutFits Bk ⟨placeW, 1⟩ 2 senderO (jobOmega (⟨VerifiableInference.Desc.K1.qAt Zp
        Np, 0⟩ : K14.SendPub)) 0 = true)
    (hnotO : ∀ r ∈ Bk.first, r.1 ≠ senderO)
    -- at every stand of the run: what is left
    (hlines : ∀ (m : Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
      (ca : CsAll (restMember (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) M.toRun.toTest (simAtW
                OnBytes.secondHashFunction Zp Np cF)).part.carries)
      (σ : Side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl
        (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
      (pre' t' pre t : List (Block (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl)),
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = pre' ++ σ.block :: t' →
      Side.seated (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder placeW
        (guardRow (testPairs M.toRun.toTest (simAtW OnBytes.secondHashFunction Zp Np cF))) [] = some σ →
      StandsAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder R.second σ
        (restMember M.toRun.toTest (simAtW OnBytes.secondHashFunction Zp Np cF)).guarded pre t (firstLen
                        M.toRun.toTest.p.nums.stages) →
      InsideOf .own Bk 2 (G.prover H).second σ.block (T.I₃ pre'.length) (σ.roundsTo 1) k m
        (envOf (H.storedWords w₀ rc) (taken₃ r.run.played.1 r.run.played.2.1)
          (r.run.played.2.2.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1))) →
      m.seen = roundsOf r.run.played.1 ++ roundsOf r.run.played.2.1 ++
        roundsOf (r.run.played.2.2.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1)) →
      r.called ⟨L.place, 1⟩ = true →
      carriedAt Bk k 2 ⟨L.place, 1⟩ (restMember (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) M.toRun.toTest
          (simAtW OnBytes.secondHashFunction Zp Np cF)).part =
        .ok ca →
      midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k ρ ⟨L.place, 1⟩ =
        .ok (some m) →
      m.st.input = R.own →
      FiveAt M.toRun.toTest (stretches _ ca) m
        (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨L.place, 1⟩) →
      M.toRun.toTest.rec₀ m.st.input (restFront M.toRun.toTest m) =
        stateAtOwnTest OnBytes.secondHashFunction Zp Np cF x
          ((r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨L.place, 1⟩).cut
            (firstLen M.toRun.toTest.p.nums.stages)) →
      (laidOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF) ρ r.run.played.1 r.run.played.2.1
          (r.run.played.2.2.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1))).front 2
          (storedShown (H.storedWords w₀ rc) (storedAsks (P5J.F0T OnBytes.secondHashFunction Zp Np cF) ρ)) =
        r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨L.place, 1⟩ →
      LeftAtOwnLines M codesFull (stretches _ ca) m) :
    OnAtRun₃ T ρ r L := by
  have h' := h.toAtMg
  obtain ⟨hZ0, hG0, -⟩ := atPure_ok hAr
  obtain rfl : Ar.Z = Zp := Except.ok.inj (hZ0.symm.trans h'.laid.pub)
  have hGf : Ar.G.first = Ar.Z.first := _root_.Meaning.K2.blank_first hG0
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ := eight_blocks_at_head h'
  have hA := sendPub_at_head h' b1 b2 b3 b4 b5 b6 b7 b8 hb
  have hmsg : OnBytes.linMessageW Ar.Z.first.lin = some wMsgFull :=
    (VerifiableInference.Desc.K1.wMsg_full (like_head h').1).trans wMsg_written
  -- the test's own half
  obtain ⟨N, c, M', hN', hc', hM', -, -, -, hg⟩ :=
    own_test_found_of_laid I OnBytes.secondHashFunction S' O hAr hL
  obtain rfl : N = Np := Except.ok.inj (hN'.symm.trans h'.laid.places)
  obtain rfl : c = cF := Except.ok.inj (hc'.symm.trans h'.laid.chain)
  have eMM : M' = M := Option.some.inj (hM'.symm.trans hM)
  rw [eMM] at hg
  -- the three senders
  have hgI := K1.k1_first_fill hAr (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => (⟨w.x, ⟨w.trace,
            I.weights Ar.Z w.w₀, w.rc⟩⟩ : K1.PlaceIn ProofFile.Inst))
    (K1.lotNo OnBytes.secondHashFunction Ar.Z) (K1.lotData S') (k1_lot_there I OnBytes.secondHashFunction S' O Ar.Z Ar.G)
    (k1_lot_alone I OnBytes.secondHashFunction S' O Ar.Z Ar.G)
  have hgW := half_w_wM h I OnBytes.secondHashFunction S' O hAr rfl
  have hgO := (sendings_found h I OnBytes.secondHashFunction S' O hAr).2
  obtain ⟨-, tr, -, hown, hcom, -⟩ := ready_ok hR
  refine onAtRun_W_lines_numbers_paid h' T hρ hR hrun I S' O Ar.G hGf M hM _ hA _ hmsg L hq
    (by rw [hP]; exact hg) hT _ _ (by rw [hP]; exact hgI) (by rw [hP]; exact hgW) _
    (by rw [hP]; exact hgO) (by rw [hown, hcom]; rfl) hbkI hbkW hbkF hbkO hnotO
    (fun _ => (AtFullSide.K13.k13_wHeard_at_head h).le.trans AtFullSide.K13.rounds356W.ge)
    (by show (0 : ℕ) < 4; decide) hlines

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.k1_lot_there
#print axioms ProofFile.Honest.K12.Sim2.k1_lot_alone
#print axioms ProofFile.Honest.K12.Sim2.eight_blocks_at_head
#print axioms ProofFile.Honest.K12.Sim2.onAtRun_W_lines_at_return
