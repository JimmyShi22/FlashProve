-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/OnFreeTAtHeadUPaid.lean

A conditional: nothing shows at the full size that ready or runC returns, that the part is called,
or that a filling holds the four halves spoken of.

OF WHAT KIND IT IS. Three of the laws that it calls (on the fields coin and tie and on the clause
trees) are ties between what one part is handed of a run's values and what another part is handed of
them.

`onFreeT_head_U_left` (Johnson/Desc/ProofFile/Honest/K12/OnFreeTAtHeadULeft.lean) with what has a
law laid in, under the head, at whatever book the maker returns. One theorem. In the side library,
because three of its payers are.

  `onFreeT_head_U_paid`: the statement.

What is paid, and by what. The book's ties: `hT_head_U` (TiesAtHeadU.lean in this folder).
`SendShapes`: `sendShapes_head` (…/K12/HeldAtCommitter.lean). Of `LeftAt`'s five fields: rows:
`rows_held` (there); columns: `columns_at_run` (…/K12/ColumnsAtRun.lean), from hst; coin:
`coin_head` (CutsAtHead.lean in this folder); tie: `tie_at_run` (…/K12/TieAtRun.lean), its premise
on the side's place by `place9_head` (…/K12/TreesAtHeadUPub.lean), its premise on the book by
`bookCutsU_head` (CutsAtHead.lean). The clause on the trees: `trees_head_U_pub`
(…/K12/TreesAtHeadUPub.lean), its premise on the book likewise.

Limits.
- OF THE PREMISES ON VALUES OF `onFreeT_head_U_left` ONE IS LEFT AS IT WAS AND IS PAID BY NOTHING
  HERE: hAns: each answer of the instance's key is its row's own, at the rows as the senders are
  handed them. `answers_held` (…/K12/HeldAtCommitter.lean) has that sentence at the key that the
  committer in Lean makes, a term; that an instance's key is that term is said of no instance. hAns
  has the key as a letter and stands at this run's own coins of the committer; what
  Johnson/Bind/ForProver/FiveAt.lean's head says under "A limit on the coins, before the others"
  bears on whoever pays it. At a key without seeds hAns is met for lack of a case.
- hst is a premise on the prover's stored table at this index and these coins of the committer: an
  equation on values too: the field columns is paid from it: there a premise gives way to a premise.
- hB: under the library's stronger head the shared rounds' authors have it as a conclusion
  (`bookWhole_returns_at_head_ahead`, AtFullSide/K14/WholeAheadAtHead.lean); not called here.
- The four halves (hg, hgU, hgO, hgS): three of them are found at one filling, under the stronger
  head and where its maker returns: two by `sendings_found` (…/K12/Sim2/TreesSharedTest.lean), the
  third inside the proof of `onAtRun_U_at_return_paid` (OnAtRunUPaid.lean here); not called here.
- The job's first member carries no vector of its own; one reader of the index serves the test, the
  two senders and "SPLIT".
- All limits of the files named above stand. The test on G_u alone. The full size alone. Of the walk
  (`runC`).
- The stand is the state that `midSharedAtW` (Honest/MidW.lean) returns. That `runC`'s own walk goes
  through that state is not said here.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.TiesAtHeadU
import AtFullSide.K12.CutsAtHead
import Johnson.Desc.ProofFile.Honest.K12.OnFreeTAtHeadULeft
import Johnson.Desc.ProofFile.Honest.K12.HeldAtCommitter
import Johnson.Desc.ProofFile.Honest.K12.ColumnsAtRun
import Johnson.Desc.ProofFile.Honest.K12.TieAtRun
import Johnson.Desc.ProofFile.Honest.K12.TreesAtHeadUPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open OnBytes (E TableKey)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc (K1.qAt)
open Johnson.G (codesFull2 proofSendsFull)
open Desc.K14 (St blocks first)
open Desc.K14.Honest (OwnAnswers)
open H2K.Pub (sgOf)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light
open ProofFile.Honest.K14 (jobU jobOmega sendPlace liftSend sendingPart Data liftK14 splitPart randNow)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **The condition at the second part's entry at the test on G_u, under the head, at the maker's
book: what is left.** `onFreeT_head_U_left`
(Johnson/Desc/ProofFile/Honest/K12/OnFreeTAtHeadULeft.lean), its conclusion to the letter, with what
has a law laid in. The job's first member carries no vector of its own; one reader wts of the index
serves the test, the two senders and "SPLIT"; the committer's coins are read as the filling reads
them (`randNow`). LEFT AS PREMISES. Public, on the plan's letters: hb, h9, hlaid; the stages'
letters s, next, rest with hk; A with hS, h0, h6. On the run's drawn challenges: Dr with T, and
hfit. On the book: hB (the maker returns it). On the prover: hα (the key that its shared parts are
given is the instance's); hst (its stored columns of the plan's item, as words, are the committer's
in Lean). On the filling: hR, S; hg, hgU, hgO, hgS (its halves at the test's place, at the two
sendings' places and at the eighth sub-protocol's). On the run: hrun, hc. ON VALUES: hAns: each
answer of the INSTANCE's key is its row's own, at the rows as the senders are handed them; and hst,
sorted above, is itself an equation on what the prover has stored at this index and these coins: at
the field columns a premise gives way to a premise. PAID HERE: the book's ties (`hT_head_U`);
`SendShapes`; four of `LeftAt`'s five fields: rows, columns, coin, tie; the clause on the trees
(`trees_head_U_pub`). OF WHAT KIND: the fields coin and tie and the clause on the trees are ties
between what one part is handed of a run's values and what another part is handed of them. -/
theorem onFreeT_head_U_paid {W₀ Tr X₀ Y : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    {P : Prover W₀ (ℕ → TableRand) ProofFile.Inst TableKey Tr X₀ Y} (hα : ∀ x, P.key x = x.pub.key)
    {w₀ : W₀} {rc : ℕ → TableRand} {x : ProofFile.Inst}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ (ℕ → TableRand) ProofFile.Inst TableKey Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)}
    (wts : W₀ → Weights)
    (J : TestJob (Common W₀ (ℕ → TableRand) TableKey) X₀) (hJ : J = (jobHeadU Zp Np
        [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords (fun c => wts c.w₀)
        (fun c => randNow (K1.qAt Zp Np) c.rc) none).toRun.toTest)
    (Js : SimJob TableKey) (hJs : Js = (simHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8]))
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side St ProofFile.Cl Empty (Common W₀ (ℕ → TableRand) TableKey) X₀ TableKey)
    (pre t : List (Block St ProofFile.Cl))
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ (restMember J Js) pre t
      (firstLen J.p.nums.stages))
    (h9 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9)
    (hg : (P.shared.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J))
    (hlaid : σ.block.rounds.zip σ.block.oracles = J.laid)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (Dr : ℕ → Fmt.Drawn)
    (T : FirstTies J s next rest Dr
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)))
    (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hfit : drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) = true)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = true)
    (hgU : (P.shared.find? fun g => g.place == sendPlace 2) = some ⟨sendPlace 2,
      [(liftSend (askOf ⟨K1.qAt Zp Np, 0⟩ (fun c => wts c.w₀)
        (fun c => randNow (K1.qAt Zp Np) c.rc))
        (sendingPart (jobU ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ (ℕ → TableRand) TableKey) X₀)]⟩)
    (hgO : (P.shared.find? fun g => g.place == sendPlace 5) = some ⟨sendPlace 5,
      [(liftSend (askOf ⟨K1.qAt Zp Np, 0⟩ (fun c => wts c.w₀)
        (fun c => randNow (K1.qAt Zp Np) c.rc))
        (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ (ℕ → TableRand) TableKey) X₀)]⟩)
    (A : Data) (hS : A.S = (K1.qAt Zp Np).par.S) (h0 : A.atPoint = 0)
    (h6 : A.atZeta = 6)
    (hgS : (P.shared.find? fun g => g.place == b8.place) = some ⟨b8.place,
      [(liftK14 A wts (splitPart A) :
        Part Empty (Common W₀ (ℕ → TableRand) TableKey) X₀)]⟩)
    (hst : ∀ y, P.storedWords w₀ rc (K1.qAt Zp Np).item y =
      Bind.ForProver.storedW Zp (wts w₀) rc (K1.qAt Zp Np).item y)
    (hAns : ∀ csU csO : Array E, OwnAnswers (K1.qAt Zp Np) x.pub.key
      (heldAt (K1.qAt Zp Np)
        (askOf ⟨K1.qAt Zp Np, 0⟩ (fun c => wts c.w₀) (fun c => randNow (K1.qAt Zp Np) c.rc)
          R.common) csU csO)) :
    ∃ ca m, carriedAt Bk k 1 ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩
        (restMember (V := Empty) J Js).part = .ok ca ∧
      midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ
          ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = .ok (some m) ∧
      OnFreeT J Js codesFull2 1 (fourOf Np).U.nums.first (Face.shared.pub m.st.input)
          (stretches _ ca) m
        (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
            ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩) := by
  subst hJ
  have hbk := bookCutsU_head h hB
  refine ProofFile.Honest.K12.Light.onFreeT_head_U_left h b1 b2 b3 b4 b5 b6 b7 b8 hb hα (fun c => wts
          c.w₀)
    (fun c => randNow (K1.qAt Zp Np) c.rc) none _ rfl Js hJs hR σ pre t S h9 hg hlaid
    (hT_head_U h hB _ _ (fun c => wts c.w₀) (fun c => randNow (K1.qAt Zp Np) c.rc) none) s next rest
      Dr T
    hk hfit hrun hc (sendShapes_head h)
    (askOf ⟨K1.qAt Zp Np, 0⟩ (fun c => wts c.w₀) (fun c => randNow (K1.qAt Zp Np) c.rc)) hgU hgO A
      wts hS h0 h6
    hgS ?_ ?_
  · intro m ca W D8 rest₈ more cU cO cS hm hca hfold hW hcols _ lU lO lS
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r _ j hj
      exact rows_held (K1.qAt Zp Np) A hS wts (randNow (K1.qAt Zp Np)) R.common _ _ r j hj
    · exact coin_head h b1 b2 b3 b4 b5 b6 b7 b8 hb hB A wts _ lS lO _ _
    · exact hAns _ _
    · exact columns_at_run h b1 b2 b3 b4 b5 b6 b7 b8 hb hR hrun σ _ pre t _ S h9 hc W D8.d8 rest₈
        more hfold hcols wts hst _ _
    · exact tie_at_run h b1 b2 b3 b4 b5 b6 b7 b8 hb (fun c => wts c.w₀)
        (fun c => randNow (K1.qAt Zp Np) c.rc) _ rfl Js hR σ pre t S h9 hrun hc
        (place9_head h pre t σ.block S.cut h9) hbk W D8.d8 rest₈ more cU cO hfold hW lU lO m ca hm
        hca
  · exact trees_head_U_pub h b1 b2 b3 b4 b5 b6 b7 b8 hb (fun c => wts c.w₀)
      (fun c => randNow (K1.qAt Zp Np) c.rc) _ rfl Js hR σ pre t S h9 hrun hc hgU hgO hbk

end AtFullSide.K12

#print axioms AtFullSide.K12.onFreeT_head_U_paid
