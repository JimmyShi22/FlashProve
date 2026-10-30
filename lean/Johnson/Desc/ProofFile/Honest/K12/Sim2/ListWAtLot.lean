-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the request's own test at a run, at the row of the lot's value.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/ListWAtLot.lean: CONDITIONAL. Statements with their proofs;
no
definition.

Can the hypotheses be met together at a real run? NOT KNOWN: as at Sim2/ListW.lean and
Sim2/ListWTrees.lean.

What is here. THE LIST OF THE REQUEST's OWN PROXIMITY TEST TIED TO THE FILLING BY A LOT's VALUE:
index
privacy's `lotW` (Johnson/M1/SlotsUW.lean), whose rows' halves are what the filling's `secondW` lays
(`lotW_halves`, there). A list that bears a row of that lot is a list in the sense of `IsListAtW`
(Sim2/ListW.lean), at the term `simAtW` for the simulators' job: so `Good`, On at a
run, and (theirs: `rowW_owes`, Johnson/M1/SlotsSeat.lean) bud are said of one object.

  `real_job_letters`   what `jobRealW`'s job is: its numbers, that its first fold spends, its door.
  `row_of_lotW`   under the head a row of the lot is `rowAtW` at a job that `jobRealW` makes.
  `isListAtW_of_row`   a list that bears `rowAtW` at a job with the place's numbers meets
  `IsListAtW`.
  `good_at_lot_W`   `Good` at A := False at such a list's own On and bud (`good_at_list_W`).
  `onAtRun_W_lines_at_lot`   `onAtRun_W_lines` (Sim2/ListWLines.lean) at such a list: hp, hfr, hrec,
      hs, ho, hJs and the list's five equations are paid.

THE END IS `OnAtRun₃` ITSELF.

THE PREMISES of `onAtRun_W_lines_at_lot`, SORTED. PUBLIC: h. THE RUN: T · hρ · hR · hrun. WHICH
OBJECTS:
hM (M is the job that `jobRealW` makes at the head's public part and a ground Gr) · hq (the list
bears
the lot's row at M; `row_of_lotW` gives such an M for each row of the lot). ON THE FILLING: hg. ON
THE
BOOK: hT. FOR trees: as at Sim2/ListWTrees.lean, none paid. LEFT AT EVERY STAND: hlines
(`LeftAtOwnLines`, Sim2/ListWLines.lean).

Limits. Those of the files named. Johnson/M1/SlotsUW.lean's own head: "Nothing here says that the
values meet Good"; and on what lies beneath it by imports see that head. At the base filling's
types.
The ground Gr is a letter: that it is the maker's is not said here. Nothing on completeness,
soundness
or hiding.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListWLines
import Johnson.M1.SlotsUW

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

variable {W₀ : Type}

/-- **What `jobRealW`'s job is.** -/
theorem real_job_letters {Xi Rc Tr Y : Type} (S : OnBytes.HonestTrace.Sz) (Fd : FileDescription Xi)
    (enter : Fd.S₃ → Except String T12) (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf Xi)
    (no : Place → ℕ) (readers : Local W₀ Rc Xi Tr → Readers)
    (weights : Local W₀ Rc Xi Tr → Weights)
    (rand : Desc.K14.P14 → Local W₀ Rc Xi Tr → TableRand) (Z : ProofFile.Pub) (G : ProofFile.Ground)
    {M : ManyJob (Local W₀ Rc Xi Tr) Y}
    (hM : jobRealW S Fd enter pile no readers weights rand Z G = some M) :
    (∃ Fo, four Z = some Fo ∧ M.toRun.toTest.p = Fo.W) ∧ (∃ f, M.toRun.toTest.fresh = some f) ∧
      M.toRun.toTest.rec₀ = doorW Fd (·.x) enter placeW idleT12 := by
  unfold jobRealW at hM
  obtain ⟨Fo, hF, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨A, hA, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨msg, hmsg, rfl⟩ := Option.map_eq_some_iff.1 hM
  exact ⟨⟨Fo, hF, rfl⟩, ⟨_, rfl⟩, rfl⟩

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- Under the head the public part's four places are the head's. -/
theorem four_at_head (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) :
    four Zp = some (fourOf Np) := by
  unfold four
  rw [h.laid.places]

/-- CONDITIONAL on the head. **A row of the lot is `rowAtW` at a job that `jobRealW` makes.** -/
theorem row_of_lotW (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF)
    (φ : Face (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) ProofFile.Inst) (I : WiderIn
                          W₀) (S' : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Gr : ProofFile.Ground)
    (q : Unlettered (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (hq : q ∈ (lotW φ I OnBytes.secondHashFunction S' O).rows Zp Gr) :
    ∃ M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit,
      jobRealW S' (P5J.F0T OnBytes.secondHashFunction Zp Np cF) enterOwn O.pile (K1.lotNo OnBytes.secondHashFunction Zp)
      (fun w => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩) (fun w => I.weights Zp w.w₀)
      (fun P w => randAt P w.rc) Zp Gr = some M ∧
      q = rowAtW φ OnBytes.secondHashFunction Zp Np cF M.toRun.toTest := by
  have hq' : q ∈ rowsW φ I OnBytes.secondHashFunction S' O Zp Gr := hq
  unfold rowsW at hq'
  split at hq'
  · rename_i s N c h1 h2 h3
    obtain rfl : N = Np := Except.ok.inj (h2.symm.trans h.laid.places)
    obtain rfl : c = cF := Except.ok.inj (h3.symm.trans h.laid.chain)
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hq'
    have hJ' := Option.mem_toList.1 hJ
    unfold realW at hJ'
    obtain ⟨M, hM, rfl⟩ := Option.map_eq_some_iff.1 hJ'
    exact ⟨M, hM, rfl⟩
  · cases hq'

/-- **A list that bears the row meets `IsListAtW`**, at the term for the simulators'
job. -/
theorem isListAtW_of_row {Bk : ProverCoinCounts} {S Cl : Type}
    (L : Lettered Bk S Cl (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit
        ProofFile.Inst)
    (J : TestJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit) (hp : J.p = (fourOf Np).W)
    (hq : L.bare = rowAtW Face.own OnBytes.secondHashFunction Zp Np cF J) :
    IsListAtW L J (simAtW OnBytes.secondHashFunction Zp Np cF) (fourOf Np).W.nums.first where
  place := by
    have e : L.bare.place = J.p.place := by rw [hq]; rfl
    rw [hp] at e
    exact e.trans (p12At_place _ _)
  row := by
    have e : L.bare.row = guardRow (testPairs J (simAtW OnBytes.secondHashFunction Zp Np cF)) := by rw [hq]; rfl
    exact e
  on := by
    have e : L.bare.On = OnOwnTestEntry Face.own J (simAtW OnBytes.secondHashFunction Zp Np cF) codesFull 2
        J.p.nums.first := by
      rw [hq]
      rfl
    rw [hp] at e
    exact e
  bud := by
    have e : L.bare.bud = budBoth (simAtW OnBytes.secondHashFunction Zp Np cF) := by rw [hq]; rfl
    exact e
  opens := rfl

/-- CONDITIONAL on the head, hM, hq and hB. **`Good` at A := False at the list that bears the lot's
row**, at the list's own On and bud. hB: a test on the book. -/
theorem good_at_lot_W (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Bk : ProverCoinCounts}
    (I : WiderIn W₀) (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Gr : ProofFile.Ground)
    (M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (hM : jobRealW S' (P5J.F0T OnBytes.secondHashFunction Zp Np cF) enterOwn O.pile (K1.lotNo OnBytes.secondHashFunction Zp)
      (fun w => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩) (fun w => I.weights Zp w.w₀)
      (fun P w => randAt P w.rc) Zp Gr = some M)
    (L : Lettered Bk (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl
      (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (hq : L.bare = rowAtW Face.own OnBytes.secondHashFunction Zp Np cF M.toRun.toTest)
    (fs : List (Fall (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃))
    (σ : Side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl
      (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (hσ : L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder fs = some σ)
    (pre : List (ℕ × ℕ × List Fmt.DeclaredRound)) (ord : List Place) (firstTree : ℕ)
    (B : Coins Bk → (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit
        → Env → Prop)
    (hB : ∀ u ∈ σ.members, ProofFile.Honest.Small.noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    Good pre Face.own σ Bk ord 2 firstTree (fun _ _ _ _ => False) B L.On L.bud := by
  obtain ⟨⟨Fo, hF, hp⟩, ⟨f, hfr⟩, -⟩ := real_job_letters _ _ _ _ _ _ _ _ _ _ hM
  obtain rfl : Fo = fourOf Np := Option.some.inj (hF.symm.trans (four_at_head h))
  exact good_at_list_W h M.toRun.toTest (simAtW OnBytes.secondHashFunction Zp Np cF) hp (by rw [hfr]; rfl) rfl
      rfl L
    (isListAtW_of_row L _ hp hq) fs σ hσ pre ord firstTree B hB

/-- CONDITIONAL on all its premises. **The clause of the rule at the list that bears the lot's
row.**
-/
theorem onAtRun_W_lines_at_lot {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
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
    (M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (hM : jobRealW S' (P5J.F0T OnBytes.secondHashFunction Zp Np cF) enterOwn O.pile (K1.lotNo OnBytes.secondHashFunction Zp)
      (fun w => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩) (fun w => I.weights Zp w.w₀)
      (fun P w => randAt P w.rc) Zp Gr = some M)
    (L : Lettered Bk (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₃ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).Cl
      (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (hq : L.bare = rowAtW Face.own OnBytes.secondHashFunction Zp Np cF M.toRun.toTest)
    -- on the filling
    (hg : ((G.prover H).second.find? fun g => g.place == placeW) =
      some ((proverSideOfProximityTest M.toRun.toTest : Placed (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins
                                 ProofFile.Inst Cells) Unit).needsField))
    -- on the book: a test with code
    (hT : tiesB Bk placeW M.toRun.toTest.members.length = true)
    -- for the clause trees: the premises of trees_at_job_own_test
    -- the job
    (hk : M.s₀.h ≤ M.s₀.k)
    (Pq : Desc.K14.P14)
    (hQ : sendingsFit Pq = true)
    (a a' : ℕ)
    (m₀ m₁ : Mem (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (at_ : Addr)
    (fs : Option ℕ × Option ℕ)
    (ask : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Ask)
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
    (wit : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → K1.PlaceIn ProofFile.Inst)
    (JI JW : K1.SendJob (K1.PlaceIn ProofFile.Inst) Unit)
    (hgI : ((G.prover H).first.find? fun g => g.place == bI.place) =
      some (K1.placeHalf (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) wit JI))
    (hgW : ((G.prover H).first.find? fun g => g.place == bW.place) =
      some (K1.placeHalf (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) wit JW))
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
    (JIm : K1.SendJob Rd Unit)
    (readers : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Rd)
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
    (hm₁ : m₁ = memK1 (K1.placeJob (X := Unit) PW fW foldW DW pW) wit at₁ 0 fs₁)
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
    (witO : Common W₀ IndexCommitterCoins Ky → Ask)
    (hgO : ((G.prover H).shared.find? fun g => g.place == bO.place) =
      some ⟨bO.place, [(ProofFile.Honest.K14.liftSend witO (ProofFile.Honest.K14.sendingPart (jobOmega ⟨Pq, a⟩))
          :
        Part Empty (Common W₀ IndexCommitterCoins Ky) X₀)]⟩)
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
    (hbaseO : (memOfSending (X := Unit) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.base = false)
    (hoffO : ∀ y ∈ [m₀, m₁], ∀ b,
      (memOfSending (X := Unit) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainFirst ≤ b →
      b < (memOfSending (X := Unit) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainFirst +
        (memOfSending (X := Unit) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainRows →
      ¬ (y.shape.mainFirst ≤ b ∧ b < y.shape.mainFirst + y.shape.mainRows))
    (hinO : (memOfSending (X := Unit) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainFirst +
      (memOfSending (X := Unit) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainRows ≤ 2 ^ M.s₀.k)
    (hcO : sameCode ((jobOmega ⟨Pq, a⟩).Q.codes.base.getD
      (Light.shapeAt (jobOmega ⟨Pq, a⟩) 0).code default) M.s₀.C = true)
    (hmineO : mineOf (jobOmega ⟨Pq, a⟩) 0 = [0])
    (hmaskO : (Light.shapeAt (jobOmega ⟨Pq, a⟩) 0).maskRows = 0)
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
  obtain ⟨⟨Fo, hF, hp⟩, ⟨f, hfr⟩, hrec⟩ := real_job_letters _ _ _ _ _ _ _ _ _ _ hM
  obtain rfl : Fo = fourOf Np := Option.some.inj (hF.symm.trans (four_at_head h))
  exact onAtRun_W_lines h T hρ hR hrun M hp f hfr hrec (simAtW OnBytes.secondHashFunction Zp Np cF) rfl rfl rfl
      L
    (isListAtW_of_row L _ hp hq) hg hT
    hk Pq hQ a a' m₀ m₁ at_ fs ask hm d₀ d₁ d₂ ht hd j₀ j₁ j₂ hsrc preI preW bI bW tI tW hcutI
    hcutW hbI hbW wit JI JW hgI hgW τI τW kI shI shW hτI hτW hWI hWW hjI hjW Rd JIm readers at₀
    at₁ fs₀ fs₁ hm₀ hPI hrI hkI hposI hbkI PW fW foldW DW pW hJW hm₁ hheard h0W hposW hbkW hbkF
    hride hroom hdF hdue hinZ₀ hnI hzI hmineI hmainI hbase₁ hoffM hoffZ hinM hinZ hnM hnZ hdW hzC
    hzZ hzF hnF hmF hmineW preO bO tO hcutO hbO witO hgO hwO hjO hnotO hposO hbkO hatO ha' haskO
    hbaseO hoffO hinO hcO hmineO hmaskO hlines

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.real_job_letters
#print axioms ProofFile.Honest.K12.Sim2.four_at_head
#print axioms ProofFile.Honest.K12.Sim2.row_of_lotW
#print axioms ProofFile.Honest.K12.Sim2.isListAtW_of_row
#print axioms ProofFile.Honest.K12.Sim2.good_at_lot_W
#print axioms ProofFile.Honest.K12.Sim2.onAtRun_W_lines_at_lot
