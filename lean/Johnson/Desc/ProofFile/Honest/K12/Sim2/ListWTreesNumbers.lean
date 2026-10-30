-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the request's own test at a run: of the senders' 71 premises 60 are paid.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/ListWTreesNumbers.lean: CONDITIONAL. One statement with its
proof;
no definition.

Can the hypotheses be met together at a real run? NOT KNOWN: as at Sim2/ListW.lean.

What is here. `onAtRun_W_lines_at_lot` (Sim2/ListWAtLot.lean: `OnAtRun₃` at the list that bears the
row
of `lotW` at the request's own proximity test) WITH 60 OF THE 71 PREMISES FOR THE
CLAUSE trees PAID under the head: what the job is (5) · hPI, hrI · where the three senders stand (9)
·
the 43 public numbers and shapes · ha' (from the challenges' declared form).

  `onAtRun_W_lines_numbers_paid`   the statement, at a free prover `G.prover H`.

THE END IS `OnAtRun₃` ITSELF.

LEFT OF THE 71, ELEVEN, BY NAME, each now at the filling's and the written plans' own terms:
  ON THE FILLING (4): hgI · hgW · hgO (the halves that the search finds at the three senders'
  places) ·
      haskO (Omega's reader at the run's common input is the job's at the run's own).
  ON THE BOOK (5): hbkI · hbkW · hbkF · hbkO · hnotO.

      TO THE LETTER THE FIVE ENDS OF `own_proof_at` (Sim2/OwnProofBook.lean; not called here).
  ON WHAT W's DATA HEARS (1): hheard, at the run's own input, against the written count of rounds in
      front of W's sender.
  ON Omega's SENDER (1): hatO: "LIN point" stands among the four rounds in front of Omega's sending.
AND ONE NEW PREMISE, hGf: the ground's first chain's numbers are the public part's.
BESIDE THEM: h · the run (T, hρ, hR, hrun) · which objects (hM, hA, hmsg, hq) · hg · hT · hlines
(`LeftAtOwnLines`: six tests on the state on entry and the rows' sentence).

By. Sim2/ListWNumbers.lean; `ownP_numbers`, `ownP_I_full`, `ownP_W_full`, `ownP_cut`
(Sim2/PublicAtW.lean: closed facts by Lean's kernel, and the cut under the head) and
Sim2/JobsAtW.lean.

Limits. Those of the files named. Nothing on completeness, soundness or hiding.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListWNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain FileDescription Oracle Place)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.K1 (qFull)
open H2K.Member (codesFull piWFull)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open Johnson.Prover.Send (col shapeAt)
open OnBytes.Slice (GE codeOf)
open H2K.Pub (sgOf)
open ProofFile.Honest.K14 (SendJob jobOmega Ask columnOf sendingsFit)

variable {W₀ : Type}

attribute [local irreducible] P2Law.ProofPlan.WP

/-- CONDITIONAL on all its premises. **The clause of the rule at the list that bears the lot's row:
of
the senders' 71 premises eleven are left.** -/
theorem onAtRun_W_lines_numbers_paid {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ :
            LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Ky X₀ : Type} {Bk : ProverCoinCounts}
    {H : Prover W₀ IndexCommitterCoins ProofFile.Inst Ky Cells X₀ Unit}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk W₀ IndexCommitterCoins Ky Cells X₀ Unit} {w₀ : W₀} {rc :
                    IndexCommitterCoins}
    {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ IndexCommitterCoins ProofFile.Inst Ky Cells X₀ Unit}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (T : ThreadsP (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k ρ = .ok r)
    -- the job that the filling's text makes, and the list: it bears the lot's row
    (I : WiderIn W₀) (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Gr : ProofFile.Ground)
    (hGf : Gr.first = Zp.first)
    (M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (hM : jobRealW S' (P5J.F0T OnBytes.secondHashFunction Zp Np cF) enterOwn O.pile (K1.lotNo OnBytes.secondHashFunction Zp)
      (fun w => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩) (fun w => I.weights Zp w.w₀)
      (fun P w => randAt P w.rc) Zp Gr = some M)
    (A : K14.SendPub) (hA : sendPub Zp = some A) (msg : Array OnBytes.OracleNotice)
    (hmsg : OnBytes.linMessageW Zp.first.lin = some msg)
    (L : Lettered Bk (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl
      (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (hq : L.bare = rowAtW Face.own OnBytes.secondHashFunction Zp Np cF M.toRun.toTest)
    -- on the filling
    (hg : ((G.prover H).second.find? fun g => g.place == placeW) =
      some ((proverSideOfProximityTest M.toRun.toTest : Placed (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins
                                 ProofFile.Inst Cells) Unit).needsField))
    -- on the book: a test with code
    (hT : tiesB Bk placeW M.toRun.toTest.members.length = true)
    -- on the filling: the three senders as the search finds them; Omega's reader
    (noI : ℕ) (DI : RowDataOf ProofFile.Inst)
    (hgI : ((G.prover H).first.find? fun g => g.place == ⟨1, some 0, 1, .K1⟩) =
      some (K1.placeHalf (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (inOf (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst
                Cells => (⟨w.trace, I.weights Zp w.w₀, w.rc⟩ : Readers)))
        (K1.placeJob (VerifiableInference.Desc.K1.firstPar Gr.first
          (VerifiableInference.Desc.K1.gpOf Zp)) noI (K1.firstFold Gr.first) DI)))
    (hgW : ((G.prover H).first.find? fun g => g.place == ⟨1, none, 4, .K1⟩) =
      some (K1.placeHalf (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (inOf (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst
                Cells => (⟨w.trace, I.weights Zp w.w₀, w.rc⟩ : Readers)))
        (K1.wJobAt Zp.first (K1.wGp Zp) 4 msg (K1.lotNo OnBytes.secondHashFunction Zp ⟨1, none, 4, .K1⟩)
            (K13.wDataAt O.pile Zp Gr))))
    (witO : Common W₀ IndexCommitterCoins Ky → Ask)
    (hgO : ((G.prover H).shared.find? fun g => g.place == K14.sendPlace 5) =
      some ⟨K14.sendPlace 5, [(K14.liftSend witO (K14.sendingPart (jobOmega A)) :
        Part Empty (Common W₀ IndexCommitterCoins Ky) X₀)]⟩)
    (haskO : witO R.common = (askOf A (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => I.weights Zp w.w₀)
        (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => randAt A.P w.rc)) R.own)
    -- on the book: four tests with code and one sentence, to the letter of own_proof_at's ends
    (hbkI : k1CutFits Bk ⟨placeW, 1⟩ 0 senderI PIw rideIw 4 = true)
    (hbkW : k1CutFits Bk ⟨placeW, 1⟩ 1 senderW PWw rideWw 0 = true)
    (hbkF : k1CutFits Bk ⟨placeW, 1⟩ 3 senderW PWw rideWw 1 = true)
    (hbkO : Light.cutFits Bk ⟨placeW, 1⟩ 2 senderO (jobOmega A) 0 = true)
    (hnotO : ∀ r ∈ Bk.first, r.1 ≠ senderO)
    -- on what W's data hears, at the run's own input; where "LIN point" stands
    (hheard : ∀ a', ((K13.wDataAt O.pile Zp Gr) (inOf (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells =>
        (⟨w.trace, I.weights Zp w.w₀, w.rc⟩ : Readers)) R.own).x).heardAt a' ≤
      ((P2Law.ProofPlan.WP.first.blocksInOrder.take 356).flatMap (·.rounds)).length)
    (hatO : A.atPoint < 4)
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
  obtain ⟨⟨Fo, hF, hp⟩, -, -⟩ := real_job_letters _ _ _ _ _ _ _ _ _ _ hM
  obtain rfl : Fo = fourOf Np := Option.some.inj (hF.symm.trans (four_at_head h))
  have eM := real_job_written h S' O.pile (K1.lotNo OnBytes.secondHashFunction Zp) (fun w : Local W₀ IndexCommitterCoins
                  ProofFile.Inst Cells => (⟨w.trace, I.weights Zp w.w₀, w.rc⟩ : Readers))
    (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => I.weights Zp w.w₀) (fun (P : Desc.K14.P14) (w : Local
              W₀ IndexCommitterCoins ProofFile.Inst Cells) => randAt P w.rc) Gr hM hA hmsg
  have eS : M.s₀ = ownS := own_stage_written h M hp
  have ePI := first_plan_written h hGf S'
  have eRI := first_ride_written h hGf S'
  obtain ⟨n1, n2, -, -, -⟩ := ownP_numbers
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ownP_I_full
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14⟩ := ownP_W_full
  obtain ⟨⟨prI, bI, tI, cI, plI, neI, jI⟩, ⟨prW, bW, tW, cW, plW, neW, jW, lenW⟩,
    ⟨prO, bO, tO, cO, plO, neO, jO, lenO⟩⟩ := ownP_cut h
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := omega_numbers_written h hA A.atPoint
  have h4 : (K1.firstJob (X := Unit) S' Zp Gr).P.sent.size - 1 = 4 := by rw [ePI, i3]
  -- the three members' shapes
  have sh := member_shapes_written h hA (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.flatMap
      (·.rounds)).length + A.atPoint)
  rw [← ePI] at sh
  have sh' : [memShape (shapeAt (K1.firstJob (X := Unit) S' Zp Gr).P ((K1.firstJob (X := Unit) S' Zp
      Gr).P.sent.size - 1)) ((firstsOf (shapesW (K1.firstJob (X := Unit) S' Zp Gr).P PWw ((jobOmega
          ⟨A.P, ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.flatMap (·.rounds)).length +
              A.atPoint⟩).Q.sent.getD 0 default).shape)).getD 0 (none, none)),
      memShape (shapeAt PWw 0) ((firstsOf (shapesW (K1.firstJob (X := Unit) S' Zp Gr).P PWw
          ((jobOmega ⟨A.P, ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.flatMap (·.rounds)).length
              + A.atPoint⟩).Q.sent.getD 0 default).shape)).getD 1 (none, none)),
      memShape ((jobOmega ⟨A.P, ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.flatMap
          (·.rounds)).length + A.atPoint⟩).Q.sent.getD 0 default).shape ((firstsOf (shapesW
              (K1.firstJob (X := Unit) S' Zp Gr).P PWw ((jobOmega ⟨A.P, ((P5J.F0T OnBytes.secondHashFunction Zp
                  Np cF).first.blocksInOrder.flatMap (·.rounds)).length + A.atPoint⟩).Q.sent.getD 0
                      default).shape)).getD 2 (none, none))] =
      [⟨0, 0, 0, 1, true⟩, ⟨16, 1, 1, 1, false⟩, ⟨0, 12, 0, 0, false⟩] := sh
  rw [h4] at sh'
  injection sh' with e0 sh1
  injection sh1 with e1₀ sh2
  injection sh2 with e2 _
  have e1 : memShape (shapeAt (K1.placeJob (X := Unit) PWw (K1.lotNo OnBytes.secondHashFunction Zp ⟨1, none, 4,
                  .K1⟩) (K1.wFold qFull.lin) (K13.wDataAt O.pile Zp Gr)).P 0) ((firstsOf (shapesW (K1.firstJob
                      (X := Unit) S' Zp Gr).P PWw ((jobOmega ⟨A.P, ((P5J.F0T OnBytes.secondHashFunction Zp Np
                          cF).first.blocksInOrder.flatMap (·.rounds)).length + A.atPoint⟩).Q.sent.getD 0
                              default).shape)).getD 1 (none, none)) =
      ⟨16, 1, 1, 1, false⟩ := e1₀
  have hK : ownS.k = 5 := by decide +kernel
  have hH : ownS.h = 1 := by decide +kernel
  -- the two senders of the first chain, at the written plans
  have hgI' := hgI
  rw [firstPar_head h hGf, first_fold_written h hGf] at hgI'
  have hgW' : ((G.prover H).first.find? fun g => g.place == ⟨1, none, 4, .K1⟩) =
      some (K1.placeHalf (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (inOf (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst
                Cells => (⟨w.trace, I.weights Zp w.w₀, w.rc⟩ : Readers)))
        (K1.placeJob (VerifiableInference.Desc.K1.parW Zp.first (K1.wGp Zp) 4 msg) (K1.lotNo
            OnBytes.secondHashFunction Zp ⟨1, none, 4, .K1⟩)
          (K1.wFold Zp.first.lin) (K13.wDataAt O.pile Zp Gr))) := hgW
  rw [(parW_head h hmsg).2, wFold_head h] at hgW'
  have hlen : ρ.first.length = ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.flatMap
      (·.rounds)).length := by
    unfold Draws.due at hρ
    simp only [Bool.and_eq_true] at hρ
    exact drawsFit_length _ _ hρ.1.1.1
  refine onAtRun_W_lines_at_lot h T hρ hR hrun I S' O Gr M hM L hq hg hT
    ?hk
    A.P
    ?hQ
    A.atPoint
    (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.flatMap (·.rounds)).length + A.atPoint)
    (memK1 (K1.firstJob (X := Unit) S' Zp Gr) (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => (⟨w.trace,
              I.weights Zp w.w₀, w.rc⟩ : Readers)) senderI 4 ((firstsOf (shapesW (K1.firstJob (X := Unit)
                  S' Zp Gr).P PWw ((jobOmega ⟨A.P, ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.flatMap
                      (·.rounds)).length + A.atPoint⟩).Q.sent.getD 0 default).shape)).getD 0 (none,
                          none)))
    (memK1 (K1.placeJob (X := Unit) PWw (K1.lotNo OnBytes.secondHashFunction Zp ⟨1, none, 4, .K1⟩) (K1.wFold
                    qFull.lin) (K13.wDataAt O.pile Zp Gr)) (inOf (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells =>
                        (⟨w.trace, I.weights Zp w.w₀, w.rc⟩ : Readers))) senderW 0 ((firstsOf (shapesW
                            (K1.firstJob (X := Unit) S' Zp Gr).P PWw ((jobOmega ⟨A.P, ((P5J.F0T OnBytes.secondHashFunction
                                Zp Np cF).first.blocksInOrder.flatMap (·.rounds)).length + A.atPoint⟩).Q.sent.getD 0
                                    default).shape)).getD 1 (none, none)))
    senderO
    ((firstsOf (shapesW (K1.firstJob (X := Unit) S' Zp Gr).P PWw ((jobOmega ⟨A.P, ((P5J.F0T
        OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.flatMap (·.rounds)).length + A.atPoint⟩).Q.sent.getD 0
            default).shape)).getD 2 (none, none))
    (askOf A (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => I.weights Zp w.w₀) (fun w : Local W₀ IndexCommitterCoins
              ProofFile.Inst Cells => randAt A.P w.rc))
    ?hm
    (depthOf (fourOf Np).W 0)
    (depthOf (fourOf Np).W 1)
    (depthOf (fourOf Np).W 2)
    ?ht
    ?hd
    1
    82
    1
    ?hsrc
    prI
    prW
    bI
    bW
    tI
    tW
    ?hcutI
    ?hcutW
    ?hbI
    ?hbW
    (inOf (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => (⟨w.trace, I.weights Zp w.w₀, w.rc⟩ : Readers)))
    (K1.placeJob PIw noI (K1.firstFold qFull) DI)
    (K1.placeJob (X := Unit) PWw (K1.lotNo OnBytes.secondHashFunction Zp ⟨1, none, 4, .K1⟩) (K1.wFold qFull.lin)
        (K13.wDataAt O.pile Zp Gr))
    ?hgI
    ?hgW
    1
    0
    4
    shIw
    shWw
    ?hτI
    ?hτW
    ?hWI
    ?hWW
    ?hjI
    ?hjW
    Readers
    (K1.firstJob (X := Unit) S' Zp Gr)
    (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => (⟨w.trace, I.weights Zp w.w₀, w.rc⟩ : Readers))
    senderI
    senderW
    ((firstsOf (shapesW (K1.firstJob (X := Unit) S' Zp Gr).P PWw ((jobOmega ⟨A.P, ((P5J.F0T
        OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.flatMap (·.rounds)).length + A.atPoint⟩).Q.sent.getD 0
            default).shape)).getD 0 (none, none))
    ((firstsOf (shapesW (K1.firstJob (X := Unit) S' Zp Gr).P PWw ((jobOmega ⟨A.P, ((P5J.F0T
        OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.flatMap (·.rounds)).length + A.atPoint⟩).Q.sent.getD 0
            default).shape)).getD 1 (none, none))
    ?hm₀
    ?hPI
    ?hrI
    ?hkI
    ?hposI
    ?hbkI
    PWw
    (K1.lotNo OnBytes.secondHashFunction Zp ⟨1, none, 4, .K1⟩)
    (K1.wFold qFull.lin)
    (K13.wDataAt O.pile Zp Gr)
    0
    ?hJW
    ?hm₁
    ?hheard
    ?h0W
    ?hposW
    ?hbkW
    ?hbkF
    ?hride
    ?hroom
    ?hdF
    ?hdue
    ?hinZ₀
    ?hnI
    ?hzI
    ?hmineI
    ?hmainI
    ?hbase₁
    ?hoffM
    ?hoffZ
    ?hinM
    ?hinZ
    ?hnM
    ?hnZ
    ?hdW
    ?hzC
    ?hzZ
    ?hzF
    ?hnF
    ?hmF
    ?hmineW
    prO
    bO
    tO
    ?hcutO
    ?hbO
    witO
    ?hgO
    ?hwO
    ?hjO
    ?hnotO
    ?hposO
    ?hbkO
    ?hatO
    ?ha2
    ?haskO
    ?hbaseO
    ?hoffO
    ?hinO
    ?hcO
    ?hmineO
    ?hmaskO
    ?hlines
  case hk =>
    rw [eS]
    exact n1
  case hQ =>
    exact o1
  case hm =>
    refine (congrArg ManyJob.mems eM).trans ?_
    show [memK1 _ _ _ ((K1.firstJob (X := Unit) S' Zp Gr).P.sent.size - 1) _, _, _] = _
    rw [h4]
    rfl
  case ht =>
    exact congrArg ManyJob.trees eM
  case hd =>
    unfold depthOf
    rw [first_head_W h]
    rfl
  case hsrc =>
    rw [first_head_W h]
    rfl
  case hcutI =>
    exact cI
  case hcutW =>
    exact cW
  case hbI =>
    exact neI
  case hbW =>
    exact neW
  case hgI =>
    rw [plI]
    exact hgI'
  case hgW =>
    rw [plW]
    exact hgW'
  case hτI =>
    exact i1
  case hτW =>
    exact w1
  case hWI =>
    exact i2
  case hWW =>
    exact w2
  case hjI =>
    exact jI
  case hjW =>
    exact jW
  case hm₀ =>
    rfl
  case hPI =>
    exact ePI
  case hrI =>
    exact eRI
  case hkI =>
    show 4 < PIw.sent.size
    rw [i3]
    decide
  case hposI =>
    exact i8
  case hbkI =>
    rw [plI]
    exact hbkI
  case hJW =>
    rfl
  case hm₁ =>
    rfl
  case hheard =>
    rw [lenW]
    exact hheard
  case h0W =>
    rw [w3]
    decide
  case hposW =>
    exact w14
  case hbkW =>
    rw [plW]
    exact hbkW
  case hbkF =>
    rw [plW]
    exact hbkF
  case hride =>
    rw [eS]
    exact w4
  case hroom =>
    rw [eS]
    exact n2
  case hdF =>
    exact w5
  case hdue =>
    rw [eS]
    exact w6
  case hinZ₀ =>
    show (memShape _ _).maskFirst + (memShape _ _).maskRows ≤ _
    rw [e0, eS, hH]
    decide
  case hnI =>
    show (shapeAt (K1.firstJob (X := Unit) S' Zp Gr).P 4).maskRows = (shapeAt PIw 4).maskRows
    rw [ePI]
  case hzI =>
    rw [eS]
    exact i6
  case hmineI =>
    exact i7
  case hmainI =>
    exact i4
  case hbase₁ =>
    show (memShape _ _).base = false
    rw [e1]
  case hoffM =>
    intro b
    show (memShape _ _).mainFirst ≤ b → b < (memShape _ _).mainFirst + (memShape _ _).mainRows →
      ¬ ((memShape _ _).mainFirst ≤ b ∧ b < (memShape _ _).mainFirst + (memShape _ _).mainRows)
    rw [e0, e1]
    intro _ _ hc
    exact absurd hc.2 (by simp)
  case hoffZ =>
    intro b
    show (memShape _ _).maskFirst ≤ b → b < (memShape _ _).maskFirst + (memShape _ _).maskRows →
      ¬ ((memShape _ _).maskFirst ≤ b ∧ b < (memShape _ _).maskFirst + (memShape _ _).maskRows)
    rw [e0, e1]
    intro h1 _ hc
    have h1' : 1 ≤ b := h1
    have h2' : b < 0 + 1 := hc.2
    omega
  case hinM =>
    show (memShape _ _).mainFirst + (memShape _ _).mainRows ≤ _
    rw [e1, eS, hK]
    decide
  case hinZ =>
    show (memShape _ _).maskFirst + (memShape _ _).maskRows ≤ _
    rw [e1, eS, hH]
    decide
  case hnM =>
    rfl
  case hnZ =>
    rfl
  case hdW =>
    exact w7
  case hzC =>
    rw [eS]
    exact w8
  case hzZ =>
    rw [eS]
    exact w9
  case hzF =>
    rw [eS]
    exact w10
  case hnF =>
    rw [eS]
    exact w11
  case hmF =>
    exact w12
  case hmineW =>
    exact w13
  case hcutO =>
    exact cO
  case hbO =>
    exact neO
  case hgO =>
    rw [plO]
    exact hgO
  case hwO =>
    exact o2
  case hjO =>
    exact jO
  case hnotO =>
    rw [plO]
    exact hnotO
  case hposO =>
    exact o6
  case hbkO =>
    rw [plO]
    exact hbkO
  case hatO =>
    rw [lenO]
    exact hatO
  case ha2 =>
    rw [hlen]
  case haskO =>
    exact haskO
  case hbaseO =>
    show (memShape _ _).base = false
    rw [e2]
  case hoffO =>
    intro y hy b
    show (memShape _ _).mainFirst ≤ b → b < (memShape _ _).mainFirst + (memShape _ _).mainRows → _
    rw [e2]
    intro _ hb
    have hb' : b < 0 + 12 := hb
    rcases List.mem_cons.1 hy with rfl | hy'
    · show ¬ ((memShape _ _).mainFirst ≤ b ∧
        b < (memShape _ _).mainFirst + (memShape _ _).mainRows)
      rw [e0]
      intro hc
      exact absurd hc.2 (by simp)
    · obtain rfl := List.mem_singleton.1 hy'
      show ¬ ((memShape _ _).mainFirst ≤ b ∧
        b < (memShape _ _).mainFirst + (memShape _ _).mainRows)
      rw [e1]
      intro hc
      have hc' : 16 ≤ b := hc.1
      omega
  case hinO =>
    show (memShape _ _).mainFirst + (memShape _ _).mainRows ≤ _
    rw [e2, eS, hK]
    decide
  case hcO =>
    rw [eS]
    exact o3
  case hmineO =>
    exact o4
  case hmaskO =>
    exact o5
  case hlines =>
    exact hlines

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.onAtRun_W_lines_numbers_paid
