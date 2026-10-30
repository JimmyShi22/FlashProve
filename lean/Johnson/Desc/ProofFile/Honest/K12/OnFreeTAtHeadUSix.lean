-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/OnFreeTAtHeadUSix.lean

A conditional: at no prover and no book is it shown that ready and runC return and that the part is
called.

`onFreeT_head_U` (OnFreeTAtHeadU.lean: what is left of the condition at the second part's entry at
the proximity test on G_u, under the head, at a run) with its premise on the sentence on values
(`SaysAt`) replaced by six premises, each by name, at a free prover. One structure; one theorem.

  `SixAt`: the six: the library's five on what was shown (`ShownU`, `OwnAnswers`, `OwnColumns`,
      `ShownO`, `ShownMu`: Johnson/Desc/K14/Honest/ItemsEach.lean) and the tie of the words
      (`WordsTied`, SaysOfMet.lean).
  `onFreeT_head_U_six`: the law.

Why at a free prover. Laws of this folder take the filling as a letter. What the first five speak of
is made by the shared chain's other halves, the stored table and the key, whose texts lie in other
folders of the library; the sixth ties these to this folder's own job and to the book. Named
premises let each be worked at apart, where a filling is laid. These files show none of the six at a
run. A corollary at a named prover and book is not in this file.

By what. `saysAt_run_U_six` (SaysAtRunU.lean); `onFreeT_head_U`.

Limits.
- IT PAYS NONE OF THE SIX. That they can be had together at a run is shown by no example here.
  hTrees, the law's other premise on values, stays.
- hα comes beside that law's premises: the key that the prover's shared parts are given is the
  instance's.
- hSix is asked at every W, D8 that meet its six hypotheses. These pin the eight rounds and the
  columns; that they pin the eight states too is read off the text of `Block.step`, not proved here.
  The four other fields of D8 (x2, x5, ids2, ids5), which `SixAt` does not read, stay free.
- All limits of OnFreeTAtHeadU.lean's and SaysAtRunU.lean's heads stand. Of the first, to the
  letter: "No later law may take the condition as a hypothesis on a run and then speak of the random
  values as uniform."
- The stand is the state that `midSharedAtW` (Honest/MidW.lean) returns. That `runC`'s own walk goes
  through that state is not said here.
- It moves no count. Nothing on completeness, on soundness or on what a view shows.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.SaysAtRunU

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (TableKey OracleNotice)
open OnBytes.Means (layoutOf)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc (K1.qAt)
open Johnson.G (codesFull2)
open Desc.K14 (P14 St blocks first)
open Desc.K14.Honest (Eight Seen8 States8 StepTo8 Inputs ShownU OwnAnswers OwnColumns ShownO ShownMu
  words2)
open H2K.Pub (sgOf)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Common StandsAt Face ready runC
  midSharedAtW carriedAt storedShown drawsFit)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **The six premises on values at the test on G_u, by name**, at the shared chain's parameters Q,
the instance's key, the eight rounds W and states D8 of a run of steps, what an honest prover holds
H, a job A with its input w, front fr and coins C. The first five are the library's own
(Johnson/Desc/K14/Honest/ItemsEach.lean); the sixth is the tie of the words (`WordsTied`,
SaysOfMet.lean). -/
structure SixAt (Q : P14) (sentU : Array OracleNotice) (key : TableKey) (W : Seen8) (D8 : States8)
    (H : Inputs) {Wt X : Type} (A : ManyJob Wt X) (w : Wt) (fr : Front X) (C : TestCoins) :
    Prop where
  /-- the first sending's OOD answers are the honest ones -/
  shownU : ShownU Q sentU (first Q.codes key) W.view D8 H
  /-- each answer of the key is its row's own -/
  answers : OwnAnswers Q key H
  /-- each column opened at "LOC" holds the rows' own symbols -/
  columns : OwnColumns Q W.view H
  /-- the second sending's OOD answers are the honest ones -/
  shownO : ShownO Q sentU (first Q.codes key) W.view D8 H
  /-- the scalar shown at "SPLIT" is the honest one -/
  mu : ShownMu Q (first Q.codes key) W.view H
  /-- on the tables of G_u's members the honest words are what the job's own rows make at C -/
  tie : ∀ G, D8.d8.st.groups[D8.d8.loc.gU]? = some G →
    WordsTied D8.d8.st D8.d8.loc.gU G (words2 Q sentU (first Q.codes key) W.view.r1 H)
      (layoutOf D8.d8.st G) (plainMany A w fr C)

/-- **`onFreeT_head_U` (OnFreeTAtHeadU.lean) with its premise on `SaysAt` replaced by the six, at a
free prover.** Its binders and its conclusion are that law's, to the letter, but for two things: hα
comes (the key that the prover's shared parts are given is the instance's), and in hSays' stead
stands hSix: at the run's stand m and carried blocks ca, at the eight rounds W and states D8
into which the library's law cuts the shared view's fold: there is something H that an honest prover
may hold at which `SixAt` holds. Each of the six is a premise by name, to be paid where a filling is
laid. The field answers stands at the instance's key, a letter: whoever pays it at the committer of
Johnson/Bind/ForProver/ is bound by "A limit on the coins, before the others" in FiveAt.lean's head
there (ValuesAtCommitter.lean quotes it). hTrees stays. -/
theorem onFreeT_head_U_six {W₀ Rc Tr X₀ Y : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
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
    (hSix : ∀ m ca (W : Seen8) (D8 : States8) (rest₈ : List Fmt.RoundView) (more : List OpenedColumn),
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
      ∃ H : Inputs, SixAt (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) x.pub.key W D8 H
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
  refine onFreeT_head_U h b1 b2 b3 b4 b5 b6 b7 b8 hb weights rand u? J hJ Js hJs hR σ pre t S h9 hg
    hlaid hT s next rest Dr T hk hfit hrun hc (fun m ca hm hca => ?_) hTrees
  obtain ⟨m', d8, rest', more, W, D8, a1, -, a3, -, a5, a6, a7, a8, a9⟩ :=
    saysAt_run_U_six h b1 b2 b3 b4 b5 b6 b7 b8 hb hα weights rand u? J Js hR σ pre t S h9 hrun hc
  obtain rfl : m' = m := Option.some.inj (Except.ok.inj (a1.symm.trans hm))
  subst a7
  obtain ⟨H, X⟩ := hSix m' ca W D8 rest' more hm hca a3 a5 a6 a8
  exact (a9 H _ X.shownU X.answers X.columns X.shownO X.mu X.tie).2

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.SixAt
#print axioms ProofFile.Honest.K12.Light.onFreeT_head_U_six
