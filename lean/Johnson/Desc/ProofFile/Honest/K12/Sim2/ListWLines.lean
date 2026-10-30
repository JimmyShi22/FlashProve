-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the request's own test at a run: what is left, as tests and one sentence.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/ListWLines.lean: CONDITIONAL. One definition, and statements
with
their proofs.

Can the hypotheses be met together at a real run? NOT KNOWN: as at Sim2/ListW.lean and
Sim2/ListWTrees.lean.

What is here. `onAtRun_W_thin` (Sim2/ListWThin.lean: `OnAtRun₃` at the list of the request's own
proximity test on the proof file's last chain, trees from the senders, asks thinned) WITH THE THREE
EQUATIONS ON THE JOB's OWN TEXT PAID FROM ONE PUBLIC TEST, the plain data made, and `FrontAsksD`
brought down to tests on the state on
entry. No plain data stands in the premise any more.

  `LeftAtOwnLines`   what is left at one stand: seven fields, the rows' sentence last.
  `early_at_head_W`   under the head the place's numbers say "early".
  `thin_of_lines`   under the head: it gives `LeftAtOwnThin` at some plain data.
  `onAtRun_W_lines`   the statement, at a free prover `G.prover H`.

THE END IS `OnAtRun₃` ITSELF. hlines is asked at every m and ca under the rule's own hypotheses.

WHAT IS LEFT AT A STAND (`LeftAtOwnLines`). T: the job's state on entry at the stand's input and the
part's own front; by the clause door, which is paid, a function of the front; by
`own_test_door_returns` (Sim2/ListWCame.lean) what `enterOwn` returns at the state of the run's own
fold.
  five · fits · count   THREE TESTS WITH CODE ON T's SHAPE (`frontFiveB`, K12/FrontAtShape.lean;
      `manyFitsS`, K12/ManyFits.lean; `tsLenOf` = 3, K12/AsksAtHead.lean): together `linesB`
      at 3
      (K12/AtFile/WStand.lean). Of five's six conjuncts two are paid elsewhere and not joined here:
      "T holds a mask" (`came_at_called_part`, Sim2/ListWCame.lean), "T's pass is nothing"
      (`enterOwn`'s text).
  tidy · dense · claims   THREE TESTS THAT READ T's ROWS: the statement is tidy; the rows taken in
  are
      dense; the open rows pass. Beside it, not called: `rows_at_own`
      (K12/AtFile/WFrontAsks.lean), on records, from six sentences on the two earlier chains' ends.
  rowsSay   `SaysAt` (K12/AsksWhole.lean): THE ONE CLAUSE THAT TIES THE PROVER's HIDDEN WORDS TO THE
      VERIFIER's ROWS. HARMLESS IF AND ONLY IF IT IS A THEOREM AT ALL COINS. Not discharged here.
The first six read the state on entry alone, values of that state among them (`claimsB` reads values
by its own docstring): no index, no randomness, no coin. fits is `manyFitsS`, on the state's shape;
`dataThree_many` (K12/ManyFitsLaw.lean) has the three equations from `manyFitsB` at the plain data's
shape: the two were not held against each other here.

By the library's own: `frontAsksD_of_five` (K12/FrontAtShapeDense.lean) · `ts_of_frontD`
(K12/AsksAtHeadDense.lean) · `dataThree_of_frontD` (K12/ManyFitsAtDense.lean) · `alike_head_W`
(AtFullSide/K12/RestTiesAtHeadW.lean). The three are general in the job, the input and the front.
THEIR
HEADS, READ: no label on coins; two limits that bear here: "The state on entry is the job's own
rec₀.
It is not shown to be the verifier's" (at this test `own_test_door_returns` ties it to the run's own
fold) · "Only the case in which the fresh table has come earlier is served": that is this test's
case: hfr : the job's fresh = some f: the first fold spends a table that W's sender has sent.

Limits. Those of Sim2/ListW.lean, Sim2/ListWTrees.lean and Sim2/ListWThin.lean. Nothing on
completeness,
soundness or hiding.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListWThin
import Johnson.Desc.ProofFile.Honest.K12.FrontAtShapeDense
import Johnson.Desc.ProofFile.Honest.K12.AsksAtHeadDense
import Johnson.Desc.ProofFile.Honest.K12.ManyFitsAtDense

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

/-- **What is left at one stand, as tests on the state on entry and one sentence.** five, fits,
count:
tests with code on the state's shape. tidy, dense, claims: tests that read its rows. rowsSay: the
one
clause that ties the prover's hidden words to the verifier's rows. -/
structure LeftAtOwnLines {Y : Type} (M : ManyJob (Local W₀ Rc ProofFile.Inst Tr) Y) (K : OnBytes.Codes)
    (mem : ℕ → Stretch) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y) : Prop where
  five : frontFiveB M.toRun.toTest.p K (ProofFile.Honest.Sh.testSh (M.toRun.toTest.rec₀ m.st.input
            (restFront M.toRun.toTest m))) = true
  fits : manyFitsS M.p (M.mems.map (·.shape)) M.trees
    (ProofFile.Honest.Sh.thinOf (ProofFile.Honest.Sh.testSh (M.toRun.toTest.rec₀ m.st.input (restFront
                    M.toRun.toTest m)))) = true
  count : tsLenOf M.toRun.toTest.p
    (ProofFile.Honest.Sh.thinOf (ProofFile.Honest.Sh.testSh (M.toRun.toTest.rec₀ m.st.input (restFront
                    M.toRun.toTest m)))) = 3
  tidy : VerifiableInference.Desc.Ground.Sh.stTidyB (M.toRun.toTest.rec₀ m.st.input (restFront
      M.toRun.toTest m)).st = true
  dense : ∀ G, (M.toRun.toTest.rec₀ m.st.input (restFront M.toRun.toTest
      m)).st.groups[(M.toRun.toTest.rec₀ m.st.input (restFront M.toRun.toTest m)).g]? = some G →
    ∀ r ∈ (OnBytes.Slice.runRows (M.toRun.toTest.rec₀ m.st.input (restFront M.toRun.toTest m)).st
        G).toList, OnBytes.Slice.ProxRun.DenseRow r
  claims : ProofFile.Honest.Sh.claimsB (M.toRun.toTest.rec₀ m.st.input (restFront M.toRun.toTest m)) =
      true
  rowsSay : SaysAt M m.st.input (restFront M.toRun.toTest m) (carriedCoins M.toRun.toTest mem)

theorem early_written_W : piWFull.early = true := by decide

/-- Under the head the place's numbers say "early". -/
theorem early_at_head_W {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) : (fourOf Np).W.early = true :=
  (alike_head_W h).early.trans early_written_W

/-- CONDITIONAL on the head, hp and the seven. **The thin clauses, at some plain data.** -/
theorem thin_of_lines {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Y : Type}
    (M : ManyJob (Local W₀ Rc ProofFile.Inst Tr) Y) (hp : M.toRun.toTest.p = (fourOf Np).W)
    (K : OnBytes.Codes) (mem : ℕ → Stretch) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y)
    (Ll : LeftAtOwnLines M K mem m) : ∃ Dp, LeftAtOwnThin M K mem m Dp := by
  have he : M.toRun.toTest.p.early = true := by
    rw [hp]
    exact early_at_head_W h
  obtain ⟨Dp, S⟩ := frontAsksD_of_five M.toRun.toTest m.st.input (restFront M.toRun.toTest m) K he
    Ll.five Ll.tidy Ll.dense Ll.claims
  have hc := ts_of_frontD M.toRun.toTest m.st.input (restFront M.toRun.toTest m) K Dp he Ll.five S
  obtain ⟨t1, t2, t3⟩ := dataThree_of_frontD M m.st.input (restFront M.toRun.toTest m) K Dp he
    Ll.five S Ll.fits (carriedCoins M.toRun.toTest mem)
  exact ⟨Dp, hc.trans Ll.count, S, t1, t2, t3, Ll.rowsSay⟩

/-- CONDITIONAL on all its premises. **The clause of the rule at the list of the request's own test:
what is left is six tests on the state on entry and the rows' sentence.** -/
theorem onAtRun_W_lines {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
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
    -- at every stand of the run: what is left
    (hlines : ∀ (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y')
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
      LeftAtOwnLines M codesFull (stretches _ ca) m) :
    OnAtRun₃ T ρ r L := by
  refine onAtRun_W_thin h T hρ hR hrun M hp f hfr hrec Js hs ho hJs L hL hg hT
    hk Pq hQ a a' m₀ m₁ at_ fs ask hm d₀ d₁ d₂ ht hd j₀ j₁ j₂ hsrc preI preW bI bW tI tW hcutI
    hcutW hbI hbW wit JI JW hgI hgW τI τW kI shI shW hτI hτW hWI hWW hjI hjW Rd JIm readers at₀
    at₁ fs₀ fs₁ hm₀ hPI hrI hkI hposI hbkI PW fW foldW DW pW hJW hm₁ hheard h0W hposW hbkW hbkF
    hride hroom hdF hdue hinZ₀ hnI hzI hmineI hmainI hbase₁ hoffM hoffZ hinM hinZ hnM hnZ hdW hzC
    hzZ hzF hnF hmF hmineW preO bO tO hcutO hbO witO hgO hwO hjO hnotO hposO hbkO hatO ha' haskO
    hbaseO hoffO hinO hcO hmineO hmaskO ?_
  intro m ca σ pre' t' pre t hcut hσ₀ S hin hseen hc hca hmid hown F5 hdr hfr'
  exact thin_of_lines h M hp codesFull _ m
    (hlines m ca σ pre' t' pre t hcut hσ₀ S hin hseen hc hca hmid hown F5 hdr hfr')

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.LeftAtOwnLines
#print axioms ProofFile.Honest.K12.Sim2.early_at_head_W
#print axioms ProofFile.Honest.K12.Sim2.thin_of_lines
#print axioms ProofFile.Honest.K12.Sim2.onAtRun_W_lines
