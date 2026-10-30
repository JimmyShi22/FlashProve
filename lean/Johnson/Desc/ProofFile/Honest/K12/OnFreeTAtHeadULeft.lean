-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/OnFreeTAtHeadULeft.lean

A conditional: at no prover and no book is it shown that ready and runC return and that the part is
called, nor that a filling holds the halves spoken of.

`onFreeT_head_U_six` (OnFreeTAtHeadUSix.lean) with three of its six premises on values paid by what
the run has played (`shownU_at_run`, `shownO_at_run`, `shownMu_at_run`: Sim/ShownAtRun.lean), at a
free prover but for three halves of the shared chain. One structure; one theorem.

  `LeftAt`: what is left, by name: rows, coin; answers, columns; tie.
  `onFreeT_head_U_left`: the law.

What has turned against `onFreeT_head_U_six`. In hSix's stead: three premises on the filling (the
prover's halves at the two sendings' places and at the eighth sub-protocol's are the shared rounds'
authors' own); public facts on shapes and on the public data of "SPLIT"; and hLeft. What an honest
prover holds is no longer a letter under "there is": it is `heldAt` (Sim/ShownAtRun.lean) of the
input as the senders are handed it and of the coins that the book lends the two senders.

Limits.
- IT PAYS NOTHING OF `LeftAt`. That its five can be had together at a run is shown by no example
  here. hTrees, the law's other premise on values, stays.
- The field coin ties two parts' coins (what `heldAt` holds of o_sp is made of the second sender's;
  the scalar's coin is lent to "SPLIT"): a fact of the book. The field tie asks that the stretches
  carried to the test make the rows that the senders' coins make: a fact of the book too. Neither is
  shown here.
- The field answers stands at the instance's key, a letter: whoever pays it at the committer of
  Johnson/Bind/ForProver/ is bound by "A limit on the coins, before the others" in FiveAt.lean's
  head there (ValuesAtCommitter.lean quotes it).
- `SendShapes` under the head, and that any filling holds the three halves, are not shown here. The
  first is shown in HeldAtCommitter.lean (`sendShapes_head`); the three halves are found at one
  filling, under the library's stronger head and where that filling's maker returns: two by
  `sendings_found` (Honest/K12/Sim2/TreesSharedTest.lean), the third inside the proof of
  `onAtRun_U_at_return_paid` (AtFullSide/K12/OnAtRunUPaid.lean). What of `LeftAt` has a law:
  HeldAtCommitter.lean, ColumnsAtRun.lean, CoinAtLendings.lean, TieAtRun.lean.
- All limits of OnFreeTAtHeadUSix.lean's and Sim/ShownAtRun.lean's heads stand.
- The stand is the state that `midSharedAtW` (Honest/MidW.lean) returns. That `runC`'s own walk goes
  through that state is not said here.
- It moves no count. Nothing on completeness, on soundness or on what a view shows.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.OnFreeTAtHeadUSix
import Johnson.Desc.ProofFile.Honest.K12.Sim.ShownAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (E zeroE TableKey OracleNotice)
open OnBytes.Slice (rdE)
open OnBytes.Means (layoutOf)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc (K1.qAt)
open Johnson.G (codesFull2)
open Desc.K14 (P14 St blocks first)
open Desc.K14.Honest (Eight Seen8 States8 StepTo8 Inputs OwnAnswers OwnColumns words2 kappaOf
  flatOf_carried)
open H2K.Pub (sgOf)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Common StandsAt Face ready runC
  midSharedAtW carriedAt storedShown drawsFit Part RowCoins lendRow sharedLook coinsE Weights)
open ProofFile.Honest.K14 (Ask jobU jobOmega SendShapes sendPlace liftSend sendingPart Data liftK14
  splitPart entriesOf)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **What is left of the six at the test on G_u once the three on what was shown are theorems**, by
name, at a value H of the type of what an honest prover holds (that a prover holds it is said of no
prover): two premises that `shownMu_at_run` (Sim/ShownAtRun.lean) takes (rows, coin), the library's
two on the committed table and the key (answers, columns), and the tie of the words. A': the public
data of the part at "SPLIT"; wts, i₀: its reader of the index and the index; kE: the coin that the
book lends that part to spend. The field rows reads nothing of a run: it is a sentence on H's rows
and on that reader. -/
structure LeftAt {W₀ : Type} (Q : P14) (sentU : Array OracleNotice) (key : TableKey) (W : Seen8)
    (D8 : States8) (H : Inputs) (A' : Data) (wts : W₀ → Weights) (i₀ : W₀) (kE : E) {Wt X : Type}
    (A : ManyJob Wt X) (w : Wt) (fr : Front X) (C : TestCoins) : Prop where
  /-- at the places that hold the matrix, H's rows are the entries that "SPLIT"'s part is handed -/
  rows : ∀ r < Q.par.S.fold.index.rows, ∀ j < Q.par.S.matrixRows * 2 ^ Q.par.S.kLo,
    H.Rw r j = rdE.val (entriesOf A'.S (wts i₀) r j)
  /-- the entry number 0 of o_sp's mask row, as H holds it, is the coin that "SPLIT" spends -/
  coin : kappaOf H.cSp Q.par.S.sharedSplit.maskRows 0 = rdE.val kE
  /-- each answer of the key is its row's own -/
  answers : OwnAnswers Q key H
  /-- each column opened at "LOC" holds the rows' own symbols -/
  columns : OwnColumns Q W.view H
  /-- on the tables of G_u's members the honest words are what the job's own rows make at C -/
  tie : ∀ G, D8.d8.st.groups[D8.d8.loc.gU]? = some G →
    WordsTied D8.d8.st D8.d8.loc.gU G (words2 Q sentU (first Q.codes key) W.view.r1 H)
      (layoutOf D8.d8.st G) (plainMany A w fr C)

/-- **`onFreeT_head_U_six` with three of the six paid by what the run has played.** Its binders and
its conclusion are that law's, to the letter, but that in hSix's stead stand: three premises on the
filling (hgU, hgO, hgS: the prover's halves at the two sendings' places and at the eighth
sub-protocol's are the shared rounds' authors' own, the two sendings' at one reader wit of the
input); three public facts on the sendings' shapes (hSh) and three on "SPLIT"'s public data (hS, h0,
h6); and hLeft: at the run's stand, carried blocks, rounds and states, and at the coins cU, cO,
cS that the book lends these three halves: `LeftAt` at `heldAt` of the input as the senders are
handed it and of cU's and cO's coins. So what an honest prover holds is a term here, no letter under
"there is". hTrees stays. -/
theorem onFreeT_head_U_left {W₀ Rc Tr X₀ Y : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} (hα : ∀ x, P.key x = x.pub.key) {w₀ : W₀} {rc : Rc}
    {x : ProofFile.Inst}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst TableKey Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)}
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (u? : Option (Common W₀ Rc TableKey → Front X₀ → ℕ → OnBytes.E))
    (J : TestJob (Common W₀ Rc TableKey) X₀) (hJ : J = (jobHeadU Zp Np
        [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand u?).toRun.toTest)
    (Js : SimJob TableKey) (hJs : Js = (simHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8]))
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side St ProofFile.Cl Empty (Common W₀ Rc TableKey) X₀ TableKey)
    (pre t : List (Block St ProofFile.Cl))
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ (restMember J Js) pre t
      (firstLen J.p.nums.stages))
    (h9 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9)
    (hg : (P.shared.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J))
    (hlaid : σ.block.rounds.zip σ.block.oracles = J.laid)
    (hT : tiesB Bk J.p.place J.members.length = true)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (Dr : ℕ → Fmt.Drawn)
    (T : FirstTies J s next rest Dr
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)))
    (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hfit : drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) = true)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = true)
    (hSh : SendShapes (K1.qAt Zp Np)) (wit : Common W₀ Rc TableKey → Ask)
    (hgU : (P.shared.find? fun g => g.place == sendPlace 2) = some ⟨sendPlace 2,
      [(liftSend wit (sendingPart (jobU ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀)]⟩)
    (hgO : (P.shared.find? fun g => g.place == sendPlace 5) = some ⟨sendPlace 5,
      [(liftSend wit (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ Rc TableKey) X₀)]⟩)
    (A : Data) (wts : W₀ → Weights) (hS : A.S = (K1.qAt Zp Np).par.S) (h0 : A.atPoint = 0)
    (h6 : A.atZeta = 6)
    (hgS : (P.shared.find? fun g => g.place == b8.place) = some ⟨b8.place,
      [(liftK14 A wts (splitPart A) :
        Part Empty (Common W₀ Rc TableKey) X₀)]⟩)
    (hLeft : ∀ m ca (W : Seen8) (D8 : States8) (rest₈ : List Fmt.RoundView) (more : List OpenedColumn)
      (cU : RowCoins
        [(liftSend wit (sendingPart (jobU ⟨K1.qAt Zp Np, 0⟩)) :
          Part Empty (Common W₀ Rc TableKey) X₀)])
      (cO : RowCoins
        [(liftSend wit (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)) :
          Part Empty (Common W₀ Rc TableKey) X₀)])
      (cS : RowCoins
        [(liftK14 A wts (splitPart A) :
          Part Empty (Common W₀ Rc TableKey) X₀)]),
      midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ
        ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = .ok (some m) →
      carriedAt Bk k 1 ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩
          (restMember (V := Empty) J Js).part = .ok ca →
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first (K1.qAt Zp Np).codes x.pub.key)
        r.run.views.2.1.rounds r.run.views.2.1.opened = .ok (D8.d8, rest₈, more) →
      r.run.views.2.1.rounds =
        [W.R1, W.R2a, W.R2b, W.R4, W.R5a, W.R5b, W.R7, W.R8] ++ rest₈ →
      r.run.views.2.1.opened = W.cs ++ more →
      StepTo8 (⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ : Eight (K1.qAt Zp Np)) 0
        (first (K1.qAt Zp Np).codes x.pub.key) W D8 →
      lendRow Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) (sendPlace 2)
        [(liftSend wit (sendingPart (jobU ⟨K1.qAt Zp Np, 0⟩)) :
          Part Empty (Common W₀ Rc TableKey) X₀)] 0 = .ok cU →
      lendRow Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) (sendPlace 5)
        [(liftSend wit (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)) :
          Part Empty (Common W₀ Rc TableKey) X₀)] 0 = .ok cO →
      lendRow Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) b8.place
        [(liftK14 A wts (splitPart A) :
          Part Empty (Common W₀ Rc TableKey) X₀)] 0 = .ok cS →
      LeftAt (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) x.pub.key W D8
        (heldAt (K1.qAt Zp Np) (wit R.common) (coinsE cU.1.1).toArray (coinsE cO.1.1).toArray) A wts
        R.common.w₀ ((coinsE cS.1.2.1.1).headD zeroE)
        (jobHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand u?)
        m.st.input (restFront J m) (carriedCoins J (stretches _ ca)))
    (hTrees : ∀ m ca, midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ
        ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = .ok (some m) →
      carriedAt Bk k 1 ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩
          (restMember (V := Empty) J Js).part = .ok ca →
      (J.trees₀ m.st.input (restFront J m) (stretches _ ca) (rowsAt J (stretches _ ca) m)).map
          (·.1) = (fourOf Np).U.nums.first.map (·.1.a) ∧
        ∀ (i : ℕ) (o' : Fmt.Shape × Fmt.TreeSource) (Tr' : Tree), (fourOf Np).U.nums.first[i]?
            = some o' →
          (J.trees₀ m.st.input (restFront J m) (stretches _ ca)
            (rowsAt J (stretches _ ca) m))[i]? = some Tr' →
          ∃ cols, (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
              ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩).treeCols (ProofFile.Honest.srcOf 1
                  o'.2).1 (ProofFile.Honest.srcOf 1 o'.2).2 = some cols ∧
            ∀ q ∈ cols, q.2 = Tr'.2 q.1) :
    ∃ ca m, carriedAt Bk k 1 ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩
        (restMember (V := Empty) J Js).part = .ok ca ∧
      midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ
          ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = .ok (some m) ∧
      OnFreeT J Js codesFull2 1 (fourOf Np).U.nums.first (Face.shared.pub m.st.input)
          (stretches _ ca) m
        (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
            ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩) := by
  refine onFreeT_head_U_six h b1 b2 b3 b4 b5 b6 b7 b8 hb hα weights rand u? J hJ Js hJs hR σ pre t S
    h9 hg hlaid hT s next rest Dr T hk hfit hrun hc
    (fun m ca W D8 rest₈ more hm hca hfold hW hcols hst => ?_) hTrees
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, eF, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :=
    flatOf_carried (Cl := ProofFile.Cl) Zp.p.chains (K1.qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last hb
  obtain ⟨hSN, -, hU⟩ := facts_at_head h
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ :=
    lengths_eight _ _ b1 b2 b3 b4 b5 b6 b7 b8 hb hU hSN
  have eF' : (P5J.F0T o Zp Np cF).shared.blocksInOrder =
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl := eF
  have epre : pre = [x0, x1, x2, x3, x4, x5, x6, x7, x8] := by
    rw [h9, eF']
    rfl
  have hN : ([x0, x1, x2, x3, x4, x5, x6, x7, x8].flatMap (·.rounds)).length = 8 := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      l0.rounds, l1.rounds, l2.rounds, l3.rounds, l4.rounds, l5.rounds, l6.rounds, l7.rounds,
      l8.rounds, n1, n2, n3, n4, n5, n6, n7, n8]
    rfl
  have h8 : 8 ≤ (pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages := by
    rw [epre, hN]
    exact Nat.le_add_right _ _
  obtain ⟨cU, lU, sU⟩ := shownU_at_run h b1 b2 b3 b4 b5 b6 b7 b8 hb hR hrun σ (restMember J Js) pre
    t _ S hc (Nat.le_trans (by decide) h8) hSh wit hgU W D8 rest₈ hW hst
  obtain ⟨cO, lO, sO⟩ := shownO_at_run h b1 b2 b3 b4 b5 b6 b7 b8 hb hR hrun σ (restMember J Js) pre
    t _ S hc (Nat.le_trans (by decide) h8) hSh wit hgO W D8 rest₈ hW hst
  obtain ⟨cS, lS, sM⟩ := shownMu_at_run h b1 b2 b3 b4 b5 b6 b7 b8 hb hR hrun σ (restMember J Js)
    pre t _ S hc h8 A wts hS h0 h6 hgS W D8 rest₈ hW hst
  have L := hLeft m ca W D8 rest₈ more cU cO cS hm hca hfold hW hcols hst lU lO lS
  exact ⟨_, ⟨sU _, L.answers, L.columns, sO _, sM _ L.rows L.coin, L.tie⟩⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.LeftAt
#print axioms ProofFile.Honest.K12.Light.onFreeT_head_U_left
