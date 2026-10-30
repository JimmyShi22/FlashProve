-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the request's own test at a run: the clause trees from the three senders.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/ListWTrees.lean: CONDITIONAL. One definition, and one
statement
with its proof.

Can the hypotheses be met together at a real run? NOT KNOWN: as at Sim2/ListW.lean; and of the
premises that stand here for the clause trees no value is shown to meet them together.

What is here. `onAtRun_W` (Sim2/ListW.lean: `OnAtRun₃` at the list of the request's own proximity
test
on the proof file's last chain) WITH THE CLAUSE trees EXCHANGED FOR THE PREMISES OF
`trees_at_job_own_test` (Sim2/TreesOwnTestJob.lean): 71 premises over some 45 letters, NONE PAID AND
NONE EVALUATED HERE. Of `LeftAtOwn` asks alone is left at a stand.

  `AsksAtOwn`   the field asks of `LeftAtOwn`, by name: all thirteen clauses.
  `onAtRun_W_trees_from_the_senders`   the statement, at a free prover `G.prover H`. Nothing here is
      typed at a filling.

THE END IS `OnAtRun₃` ITSELF. hasks is asked at every m and ca under the rule's own hypotheses, as
hleft is in `onAtRun_W`.

THE PREMISES, SORTED. Those of `onAtRun_W`: see there. FOR trees, in `trees_at_job_own_test`'s own
names:
  WHAT THE JOB IS (5; at the filling's job `real_job_form`, Sim2/TreesOwnTestJob.lean, reads them
  off
      `jobRealW`): hm · ht · hm₀ · hm₁ · hJW.
  ON THE FILLING (6: which halves the search finds in the prover's lists, and how the members' jobs
      sit to the senders'): hgI · hPI · hrI (the first chain's first sender of the kind K1; the
      member's job has that sender's plan and ride: the two jobs' data are not compared) · hgW (W's
      sender) · hgO (the shared chain's sending of Omega) · haskO (that sending's reader at the
      run's
      common input is the job's at the run's own). By the text: hgI's form is
      the
      end of `k1_first_fill` (Honest/K1/Law/HalfAtFill.lean), whose two premises are not shown at
      the wide filling here; hgW's of `half_w_wM` (Honest/K1/Law/WSideAtFill.lean).
  ON THE BOOK (5: four Bool tests and one sentence): hbkI · hbkW · hbkF (`k1CutFits`)
  ·
      hbkO (`Light.cutFits`) · hnotO. They are, at letters, the five ends of
      `own_proof_at` (Sim2/OwnProofBook.lean; not called here).
  ON WHAT W's DATA HEARS (1): hheard, AT THE RUN's OWN INPUT.
  ON Omega's SENDER (2): hatO · ha'. ha' READS THE RUN's CHALLENGES: a' = ρ.first.length + a: at a
  due
      ρ that length is the first chain's count of rounds, which is what `jobRealW` lays.
  WHERE THE THREE SENDERS STAND IN THE DESCRIPTION (9): hcutI · hcutW · hcutO · hbI · hbW · hbO ·
  hjI ·
      hjW · hjO.
  PUBLIC NUMBERS AND SHAPES (43: by their types they read the job's first stage, the members'
  shapes,
      the senders' plans and the place's numbers: no input and no coin): hk · hQ · hd · hsrc · hτI ·
      hτW · hWI · hWW · hkI · hposI · h0W · hposW · hride · hroom · hdF · hdue · hinZ₀ · hnI · hzI ·
      hmineI · hmainI · hbase₁ · hoffM · hoffZ · hinM · hinZ · hnM · hnZ · hdW · hzC · hzZ · hzF ·
      hnF ·
      hmF · hmineW · hwO · hposO · hbaseO · hoffO · hinO · hcO · hmineO · hmaskO.

Limits. Those of Sim2/ListW.lean and of Sim2/TreesOwnTestJob.lean. Nothing on completeness,
soundness
or hiding.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListW
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesOwnTestJob

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain FileDescription Oracle Place)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open H2K.Member (codesFull piWFull)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open Johnson.Prover.Send (col shapeAt)
open Johnson.Prover.Link (packedN)
open OnBytes.Slice (GE codeOf)
open H2K.Pub (sgOf)
open Johnson.Prover.Send (mainSyms maskSyms Rows)
open ProofFile.Honest.K14 (SendJob jobOmega Ask columnOf sendingsFit)

variable {W₀ Rc Tr : Type}

/-- **The field asks of `LeftAtOwn`, at one stand**: all thirteen clauses of `ShapeAsksD` and
`DataAsks`. -/
def AsksAtOwn {Y : Type} (J : TestJob (Local W₀ Rc ProofFile.Inst Tr) Y) (K : OnBytes.Codes)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (mem : ℕ → Stretch) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y)
        : Prop :=
  ∃ Dp cc Rw, Dp.ts.length = os.length ∧
    ShapeAsksD J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) K Dp ∧
    DataAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) Dp cc Rw

/-- CONDITIONAL on all its premises. **The clause of the rule at the list of the request's own test,
the clause trees from the three senders.** -/
theorem onAtRun_W_trees_from_the_senders {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ :
            LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Ky X₀ Y' : Type} {Bk : ProverCoinCounts}
    {H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y'}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk W₀ Rc Ky Tr X₀ Y'} {w₀ : W₀} {rc : Rc}
    {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y'}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (T : ThreadsP (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k ρ = .ok r)
    -- the two jobs
    (M : ManyJob (Local W₀ Rc ProofFile.Inst Tr) Y') (hp : M.toRun.toTest.p = (fourOf Np).W) (f : Addr ×
              ℕ)
    (hfr : M.toRun.toTest.fresh = some f)
    (hrec : M.toRun.toTest.rec₀ =
      doorW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (·.x) enterOwn placeW idleT12)
    (Js : SimJob ProofFile.Inst) (hs : Js.p = (fourOf Np).W) (ho : Js.own = false)
    (hJs : Js.rec₀ = stateAtOwnTest OnBytes.secondHashFunction Zp Np cF)
    -- the list
    (L : Lettered Bk (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl
      (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y' ProofFile.Inst)
    (hL : IsListAtW L M.toRun.toTest Js (fourOf Np).W.nums.first)
    -- on the filling
    (hg : ((G.prover H).second.find? fun g => g.place == placeW) =
      some ((proverSideOfProximityTest M.toRun.toTest : Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr)
          Y').needsField))
    -- on the book: a test with code
    (hT : tiesB Bk placeW M.toRun.toTest.members.length = true)
    -- for the clause trees: the premises of trees_at_job_own_test
    -- the job
    (hk : M.s₀.h ≤ M.s₀.k)
    (Pq : Desc.K14.P14)
    (hQ : sendingsFit Pq = true)
    (a a' : ℕ)
    (m₀ m₁ : Mem (Local W₀ Rc ProofFile.Inst Tr) Y')
    (at_ : Addr)
    (fs : Option ℕ × Option ℕ)
    (ask : Local W₀ Rc ProofFile.Inst Tr → Ask)
    (hm : M.mems = [m₀, m₁, memOfSending (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none])
    (d₀ d₁ d₂ : ℕ)
    (ht : M.trees = [(d₀, [.mask 0]), (d₁, [.main 1, .mask 1, .fresh]), (d₂, [.main 2])])
    (hd : [d₀, d₁, d₂] = (fourOf Np).W.nums.first.map (·.1.a))
    (j₀ j₁ j₂ : ℕ)
    (hsrc : (fourOf Np).W.nums.first.map (fun o => ProofFile.Honest.srcOf 2 o.2) = [(0, j₀), (0, j₁), (1,
              j₂)])
    -- the first chain's two senders
    (preI preW : List (Block (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₁ (P5J.F0T OnBytes.secondHashFunction Zp Np
                    cF).Cl))
    (bI bW : Block (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl)
    (tI tW : List (Block (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl))
    (hcutI : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = preI ++ bI :: tI)
    (hcutW : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = preW ++ bW :: tW)
    (hbI : bI.rounds ≠ [])
    (hbW : bW.rounds ≠ [])
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst)
    (JI JW : K1.SendJob (K1.PlaceIn ProofFile.Inst) Y')
    (hgI : ((G.prover H).first.find? fun g => g.place == bI.place) =
      some (K1.placeHalf (V := Local W₀ Rc ProofFile.Inst Tr) wit JI))
    (hgW : ((G.prover H).first.find? fun g => g.place == bW.place) =
      some (K1.placeHalf (V := Local W₀ Rc ProofFile.Inst Tr) wit JW))
    (τI τW kI : ℕ)
    (shI shW : OnBytes.TreeShape)
    (hτI : JI.P.trees[τI]? = some shI)
    (hτW : JW.P.trees[τW]? = some shW)
    (hWI : columnWidth JI.P τI = shI.mainWidth + shI.maskWidth)
    (hWW : columnWidth JW.P τW = shW.mainWidth + shW.maskWidth)
    (hjI : treesTo (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder preI.length + τI = j₀)
    (hjW : treesTo (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder preW.length + τW = j₁)
    -- what the two members are
    (Rd : Type)
    (JIm : K1.SendJob Rd Y')
    (readers : Local W₀ Rc ProofFile.Inst Tr → Rd)
    (at₀ at₁ : Addr)
    (fs₀ fs₁ : Option ℕ × Option ℕ)
    (hm₀ : m₀ = memK1 JIm readers at₀ kI fs₀)
    (hPI : JIm.P = JI.P)
    (hrI : JIm.ride = JI.ride)
    (hkI : kI < JI.P.sent.size)
    (hposI : 0 < (K1.dueR JI.P JI.ride).f + (K1.dueR JI.P JI.ride).e)
    (hbkI : k1CutFits Bk ⟨placeW, 1⟩ 0 ⟨bI.place, 0⟩ JI.P JI.ride kI = true)
    (PW : VerifiableInference.Desc.K1.Par)
    (fW : ℕ)
    (foldW : Option (ℕ × OnBytes.FoldShape))
    (DW : RowDataOf ProofFile.Inst)
    (pW : ℕ)
    (hJW : JW = K1.placeJob PW fW foldW DW pW)
    (hm₁ : m₁ = memK1 (K1.placeJob (X := Y') PW fW foldW DW pW) wit at₁ 0 fs₁)
    (hheard : ∀ a', (DW (wit R.own).x).heardAt a' ≤ (preW.flatMap (·.rounds)).length)
    (h0W : 0 < PW.sent.size)
    (hposW : 0 < (K1.dueR PW (K1.rideOf foldW)).f + (K1.dueR PW (K1.rideOf foldW)).e)
    (hbkW : k1CutFits Bk ⟨placeW, 1⟩ 1 ⟨bW.place, 0⟩ PW (K1.rideOf foldW) 0 = true)
    (hbkF : k1CutFits Bk ⟨placeW, 1⟩ 3 ⟨bW.place, 0⟩ PW (K1.rideOf foldW) 1 = true)
    (hride : K1.rideOf foldW 1 = some ⟨M.s₀.k, M.s₀.h⟩)
    (hroom : 2 * M.s₀.k + 1 ≤ M.s₀.h + M.s₀.Z.l)
    (hdF : ((shapeAt PW 1).mainDeg == 3) = false)
    (hdue : 2 * M.s₀.k + 1 + 2 ^ M.s₀.h * M.s₀.Z.r ≤
      (K1.dueMsg PW.codes (shapeAt PW 1) (K1.rideOf foldW 1)).e)
    -- public, at the two senders
    (hinZ₀ : m₀.shape.maskFirst + m₀.shape.maskRows ≤ 2 ^ M.s₀.h)
    (hnI : m₀.shape.maskRows = (Johnson.Prover.Send.shapeAt JI.P kI).maskRows)
    (hzI : codeOf (JI.P.codes.mask.getD (Johnson.Prover.Send.shapeAt JI.P kI).maskCode default) =
      M.s₀.Z)
    (hmineI : (List.range JI.P.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade JI.P.codes JI.P.sent).getD {}).tree[k]? == some τI) =
        [kI])
    (hmainI : (Johnson.Prover.Send.shapeAt JI.P kI).mainRows = 0)
    (hbase₁ : m₁.shape.base = false)
    (hoffM : ∀ b, m₁.shape.mainFirst ≤ b → b < m₁.shape.mainFirst + m₁.shape.mainRows →
      ¬ (m₀.shape.mainFirst ≤ b ∧ b < m₀.shape.mainFirst + m₀.shape.mainRows))
    (hoffZ : ∀ b, m₁.shape.maskFirst ≤ b → b < m₁.shape.maskFirst + m₁.shape.maskRows →
      ¬ (m₀.shape.maskFirst ≤ b ∧ b < m₀.shape.maskFirst + m₀.shape.maskRows))
    (hinM : m₁.shape.mainFirst + m₁.shape.mainRows ≤ 2 ^ M.s₀.k)
    (hinZ : m₁.shape.maskFirst + m₁.shape.maskRows ≤ 2 ^ M.s₀.h)
    (hnM : m₁.shape.mainRows = (Johnson.Prover.Send.shapeAt JW.P 0).mainRows)
    (hnZ : m₁.shape.maskRows = (Johnson.Prover.Send.shapeAt JW.P 0).maskRows)
    (hdW : (Johnson.Prover.Send.shapeAt JW.P 0).mainDeg = 3)
    (hzC : codeOf (JW.P.codes.base.getD (Johnson.Prover.Send.shapeAt JW.P 0).code default) = M.s₀.C)
    (hzZ : codeOf (JW.P.codes.mask.getD (Johnson.Prover.Send.shapeAt JW.P 0).maskCode default) =
      M.s₀.Z)
    (hzF : codeOf (JW.P.codes.mask.getD (Johnson.Prover.Send.shapeAt JW.P 1).maskCode default) =
      M.s₀.Z)
    (hnF : (Johnson.Prover.Send.shapeAt JW.P 1).maskRows = 2 ^ M.s₀.h)
    (hmF : (Johnson.Prover.Send.shapeAt JW.P 1).mainRows = 0)
    (hmineW : (List.range JW.P.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade JW.P.codes JW.P.sent).getD {}).tree[k]? == some τW) =
        [0, 1])
    -- the shared chain's sender
    (preO : List (Block (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₂ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl))
    (bO : Block (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₂ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl)
    (tO : List (Block (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₂ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl))
    (hcutO : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = preO ++ bO :: tO)
    (hbO : bO.rounds ≠ [])
    (witO : Common W₀ Rc Ky → Ask)
    (hgO : ((G.prover H).shared.find? fun g => g.place == bO.place) =
      some ⟨bO.place, [(ProofFile.Honest.K14.liftSend witO (ProofFile.Honest.K14.sendingPart (jobOmega ⟨Pq, a⟩))
          :
        Part Empty (Common W₀ Rc Ky) X₀)]⟩)
    (hwO : widthFits (jobOmega ⟨Pq, a⟩) 0 = true)
    (hjO : Johnson.G.OfPlan.rootsOf (preO.flatMap (·.rounds)) + 0 = j₂)
    (hnotO : ∀ r ∈ Bk.first, r.1 ≠ ⟨bO.place, 0⟩)
    (hposO : 0 < (ProofFile.Honest.K14.takesOf (jobOmega ⟨Pq, a⟩).Q.codes (jobOmega ⟨Pq, a⟩).Q.sent
        (jobOmega ⟨Pq, a⟩).sort).f +
      (ProofFile.Honest.K14.takesOf (jobOmega ⟨Pq, a⟩).Q.codes (jobOmega ⟨Pq, a⟩).Q.sent
        (jobOmega ⟨Pq, a⟩).sort).e)
    (hbkO : Light.cutFits Bk ⟨placeW, 1⟩ 2 ⟨bO.place, 0⟩ (jobOmega ⟨Pq, a⟩) 0 = true)
    (hatO : a < (preO.flatMap (·.rounds)).length)
    (ha' : a' = ρ.first.length + a)
    (haskO : witO R.common = ask R.own)
    (hbaseO : (memOfSending (X := Y') (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.base = false)
    (hoffO : ∀ y ∈ [m₀, m₁], ∀ b,
      (memOfSending (X := Y') (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainFirst ≤ b →
      b < (memOfSending (X := Y') (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainFirst +
        (memOfSending (X := Y') (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainRows →
      ¬ (y.shape.mainFirst ≤ b ∧ b < y.shape.mainFirst + y.shape.mainRows))
    (hinO : (memOfSending (X := Y') (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainFirst +
      (memOfSending (X := Y') (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainRows ≤ 2 ^ M.s₀.k)
    (hcO : sameCode ((jobOmega ⟨Pq, a⟩).Q.codes.base.getD
      (Light.shapeAt (jobOmega ⟨Pq, a⟩) 0).code default) M.s₀.C = true)
    (hmineO : mineOf (jobOmega ⟨Pq, a⟩) 0 = [0])
    (hmaskO : (Light.shapeAt (jobOmega ⟨Pq, a⟩) 0).maskRows = 0)
    -- at every stand of the run: the clause on values
    (hasks : ∀ (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y')
      (ca : CsAll (restMember (V := Local W₀ Rc ProofFile.Inst Tr) M.toRun.toTest Js).part.carries)
      (σ : Side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl
        (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Y' ProofFile.Inst)
      (pre' t' pre t : List (Block (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl)),
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = pre' ++ σ.block :: t' →
      Side.seated (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder placeW
        (guardRow (testPairs M.toRun.toTest Js)) [] = some σ →
      StandsAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder R.second σ
        (restMember M.toRun.toTest Js).guarded pre t (firstLen M.toRun.toTest.p.nums.stages) →
      InsideOf .own Bk 2 (G.prover H).second σ.block (T.I₃ pre'.length) (σ.roundsTo 1) k m
        (envOf (H.storedWords w₀ rc) (taken₃ r.run.played.1 r.run.played.2.1)
          (r.run.played.2.2.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1))) →
      m.seen = roundsOf r.run.played.1 ++ roundsOf r.run.played.2.1 ++
        roundsOf (r.run.played.2.2.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1)) →
      r.called ⟨L.place, 1⟩ = true →
      carriedAt Bk k 2 ⟨L.place, 1⟩ (restMember (V := Local W₀ Rc ProofFile.Inst Tr) M.toRun.toTest
          Js).part =
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
      AsksAtOwn M.toRun.toTest codesFull (fourOf Np).W.nums.first (stretches _ ca) m) :
    OnAtRun₃ T ρ r L := by
  refine onAtRun_W h T hρ hR hrun M hp f hfr hrec Js hs ho hJs L hL hg hT ?_
  intro m ca σ pre' t' pre t hcut hσ₀ S hin hseen hc hca hmid hown F5 hdr hfr'
  refine ⟨hasks m ca σ pre' t' pre t hcut hσ₀ S hin hseen hc hca hmid hown F5 hdr hfr', ?_⟩
  have hσp : σ.block.place = placeW := by
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hσ₀
    simpa using List.find?_some hb
  have hLp : L.place = placeW := hL.place
  have hc' : r.called ⟨σ.block.place, (restMember (V := Local W₀ Rc ProofFile.Inst Tr) M.toRun.toTest
      Js).guarded.number⟩ =
      true := by
    rw [hσp, ← hLp]
    exact hc
  have hmid' : midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k ρ
      ⟨σ.block.place, (restMember (V := Local W₀ Rc ProofFile.Inst Tr) M.toRun.toTest Js).guarded.number⟩
          = .ok (some m) := by
    rw [hσp, ← hLp]
    exact hmid
  obtain ⟨cc, hlp, rfl⟩ : ∃ cc, lendPart Bk (Bk.rowsOf 2) (k.look 2)
      ⟨σ.block.place, (restMember (V := Local W₀ Rc ProofFile.Inst Tr) M.toRun.toTest Js).guarded.number⟩
      (restMember (V := Local W₀ Rc ProofFile.Inst Tr) M.toRun.toTest Js).part = .ok cc ∧ cc.2.2 = ca :=
          by
    rw [hσp, ← hLp]
    unfold carriedAt at hca
    cases hl : lendPart Bk (Bk.rowsOf 2) (k.look 2) ⟨L.place, 1⟩
        (restMember (V := Local W₀ Rc ProofFile.Inst Tr) M.toRun.toTest Js).part with
    | error e =>
      rw [hl] at hca
      cases hca
    | ok cc =>
      rw [hl] at hca
      exact ⟨cc, hl, Except.ok.inj hca⟩
  have hT' := trees_at_job_own_test h.laid.planOk hR hrun σ (restMember M.toRun.toTest Js).guarded
      pre t _ S
    hc' (storedShown (H.storedWords w₀ rc) r.run.storedAsked)
    M hk Pq hQ a a' m₀ m₁ at_ fs ask hm d₀ d₁ d₂ ht _ hd j₀ j₁ j₂ hsrc m hmid' rfl _ _ _ _ cc hlp
    preI preW bI bW tI tW hcutI hcutW hbI hbW wit JI JW hgI hgW τI τW kI shI shW hτI hτW hWI hWW
    hjI hjW Rd JIm readers at₀ at₁ fs₀ fs₁ hm₀ hPI hrI hkI hposI (by rw [hσp]; exact hbkI) PW fW
    foldW DW pW hJW hm₁ (by rw [hown]; exact hheard) h0W hposW (by rw [hσp]; exact hbkW)
    (by rw [hσp]; exact hbkF) hride hroom hdF hdue hinZ₀ hnI hzI hmineI hmainI hbase₁ hoffM hoffZ
    hinM hinZ hnM hnZ hdW hzC hzZ hzF hnF hmF hmineW preO bO tO hcutO hbO witO hgO hwO hjO hnotO
    hposO (by rw [hσp]; exact hbkO) hatO ha' (by rw [hown]; exact haskO) hbaseO hoffO hinO hcO
    hmineO hmaskO
  rw [hσp, ← hLp] at hT'
  exact hT'

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.AsksAtOwn
#print axioms ProofFile.Honest.K12.Sim2.onAtRun_W_trees_from_the_senders
