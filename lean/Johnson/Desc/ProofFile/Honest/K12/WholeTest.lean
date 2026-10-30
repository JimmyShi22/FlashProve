-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/WholeTest.lean: one statement for the whole proximity test: its
block accepts all that `testAll` shows. The theorem joins theorems of this folder and of
Johnson/Desc/K12/Honest/, in the order of the test: on the batching's values, on the first stage's
values, on the stages from the second on, by an invariant that is a free parameter, and on the
test's frame (Johnson/Desc/K12/Frame.lean). It is general in the job, the prover's input, what
precedes the test, the coins and the challenges, under the hypotheses below; the acceptances at the
door and at the first stage are among them. Statement and proof.

In the list: a job J (`TestJob`, Test.lean in this folder) is what a caller supplies for its test.
The place is `J.p` (`P12`, Frame.lean as above): the numbers of a place at which a proximity test
is, among them the list of stages (`Fmt.M1.Stage`): a is the first stage, next the second, rest the
list of the others. h and k are the fields of a, unless another stage is named, and g is k - h
(`sgOf`, Johnson/Desc/K12/Law/ChainOf.lean). w is the prover's input; fr is what precedes the test
(`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean). C: the coins that `testAll` reads, by number
(`TestCoins`). D: the sampled challenges by the round's number, "BAT" being round 0. The test's
block is `proximityTestKind guardedProximityTestParts J.p` (`proximityTestKind`: Frame.lean; `guardedProximityTestParts`: Johnson/Desc/K12/JoinGuarded.lean). It is
made of parts (`Parts`), with tests of its own between them: the front, which has no round; the
batching, with the round "BAT"; for each stage but the last a fold, a switch and the batching after
the switch; the base case. The door is what `DoorYes` (TestYes.lean in this folder) speaks of: the
front, the batching and the block's test that the group is the first stage's. The first stage is
what `FirstYes` (Johnson/Desc/K12/Honest/FirstYes.lean) speaks of: the first fold, the first switch
and the batching after it. The states of type `T12` (Johnson/Desc/K12/Join.lean): `J.rec₀ w fr` on
entry to the test, `J.recB w fr (D 0)` after the batching, `t1At` after the first fold, `t3At` after
the first stage (both FirstYes.lean). A part passes something on to the next in the field `pass`: a
batching a claim with its layout, a fold single rows. The states of type `PS`
(Johnson/Prover/Link/BodyState.lean): `J.first w fr C` at the first stage, `qAt` (FirstYes.lean)
after it. `ClaimTrue` (Johnson/Desc/K12/Honest/ClaimTrue.lean), at a state of each type: whatever
claim the first passes is true at the second's message. The group is the group of oracle messages
under test.

  `test_accepts`: under the hypotheses below there is a state t' with `Post t'` such that the
    block's decision (`Block.decide`, Johnson/Desc/Block.lean) at `J.rec₀ w fr`, at the rounds of
    `testAll J w fr C D` without their digests (`noDigest`) and at its groups of opened columns
    returns `.ok t'`. The field `tr` of what `testAll` returns, the trees' columns, is no argument
    of a decision

By what. `bat_claimTrue_state` (Johnson/Desc/K12/Honest/BatState.lean) gives `ClaimTrue` after the
batching, at `J.first w fr C`. From it `first_claimTrue` (Johnson/Desc/K12/Honest/FirstJoins.lean)
gives `ClaimTrue` after the first stage, at `t3At` and `qAt`; its hypothesis on the fresh table of
`J.first w fr C` is `first_packs` (FreshCols.lean in this folder). hI then gives Inv there, and
`stages_yes` (TestYes.lean) gives that the stages' block accepts, with Post. `test_yes`
(TestYes.lean) joins this with the door along the test's frame. `getD_of_ok`
(Johnson/Prover/Link/BodyYes.lean) turns `J.recB w fr (D 0)` into the state that the batching
returns.

Hypotheses.
- The place: it has two stages or more, rounds and oracle messages; the public clauses of `first_V`
  (Johnson/Desc/K12/Honest/FirstValues.lean). By name, together with the hypotheses of `first_V` on
  the layout's numbers and on room: hst: the list of stages is `a :: next :: rest`. hrd, hor:
  `H2U.roundsOfNums` and `H2U.testOracles` (Johnson/Desc/K12/TestEntries.lean) return lists. he, h1:
  the place's fields `early` and `answers` (Frame.lean) are `true` and 1. hp: the state after the
  batching passes a claim, the row `row` with the layout L. hD, hok: `gpOf` returns the plain data
  Dp on the group at that state, and every clause of `gpL` at Dp is true (both
  Johnson/Desc/K12/Law/FirstOk.lean). hhk, hhk': h ≤ k at a and at next. hs: `(sg a).Sized`
  (OnBytes/Slice/Numbers.lean), on the sizes of the stage's two codes. hcu, hnx: `stageAt`
  (Join.lean) returns cu for a and nx for next. hf: a fits next (`CsFit`,
  OnBytes/Slice/CsData.lean). hLk, hLh: `L.k` is h + g and `L.h` is h. hroom: h + 2 g + 1 ≤ `a.Z.l`.
  hZl: in `t1At` the mask code with the number `cu.maskCode` has the message length `a.Z.l`. hOld:
  whatever single rows `t1At` passes meet `OldOk` (FirstValues.lean).
- The place and the layout, beyond `first_V`. hLl, hLz: 2 ^ `L.logEll` is `a.C.l` and
  2 ^ `L.logEllZk` is `a.Z.l`. hfit: from next on, each stage fits the one after it (`FitAll`,
  Johnson/Desc/K12/Honest/Stages.lean).
- Acceptances at the door and the first stage. Y0: `DoorYes`: the front and the batching accept; the
  batching's block has one round and no opening; the group after the batching is the first stage's.
  Y: `FirstYes`: the first fold, the first switch and the batching after it accept; its field
  `came`; four numbers of the block's cuts, the switch having as many openings as there are trees.
- The prover's data. R: plain rows (`PlainRows`, Johnson/Desc/K12/Honest/FirstRows.lean). hsay:
  every row that the test takes in (`runRows`, OnBytes/Slice/BlkBegin.lean, at the group under test
  in the state after the front) says its claim of the words that the plain rows make (`AllSay`,
  Johnson/Desc/Means/Says.lean, at `wordsAt`, Johnson/Desc/K12/Honest/LaidState.lean). hS: the first
  stage's state holds the plain rows at the layout's blocks (`StateAt`,
  Johnson/Desc/K12/Honest/FirstState.lean). hC: the trees' columns c hold the plain rows' symbols
  (`ColsAt`, FirstRows.lean). htr: the job's trees (`J.trees₀`) are the group's trees in the book's
  order (`groupTrees`, Johnson/Desc/K12/Honest/GroupState.lean, at the list `Dp.ts`, the depths in
  `Dp.book`, a `TreeBook` of OnBytes/Iop/Ground.lean, and c).
- From the second stage on. Inv and Post are free parameters. hstep, hbase: the two hypotheses of
  `body_yes_of` (BodyYes.lean) on them: at a stage that is not the last, Inv gives `StageYes` and
  Inv after the stage; at the last, Inv gives that the base case accepts and returns a state with
  Post. hI: Inv holds after the first stage where the claim that is passed there is true
  (`ClaimTrue`).
- The challenges. ht, hr: round 1 + 2 + (h + g), the first switch's second, has as many positions as
  stated (`a.t`), in range (below 2 ^ `a.C.a`). hwords: the seed's factor's words are below the
  prime (`okE`, OnBytes/Field/Ext.lean). The factor is the element with the number `bitsAt`
  (FirstValues.lean) among those of round 1 + 1 + (h + g), the first switch's first; `zeroE` where
  there is none.

Limits. Every clause above is a hypothesis; none is shown here at any place. No values that meet the
whole list of hypotheses are given. `J.rec₀` is a field of the job, a function of w and fr; it is
compared with nothing here, and `J.recB w fr (D 0)`, `t1At` and `t3At` are computed from it. Of the
clauses that are called public above, hp, hD, hok, hZl and hOld read these states: that the states
depend neither on the prover's input nor on the coins is not stated. Nothing on completeness, on
soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.TestYes
import Johnson.Desc.ProofFile.Honest.K12.FreshCols
import Johnson.Desc.K12.Honest.BatState

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {W X : Type}

/-- **The proximity test's block accepts all that `testAll` shows**, under the hypotheses that the
file's head lists. -/
theorem test_accepts (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (ds : List Fmt.DeclaredRound)
    (os : List (List (ℕ × ℕ))) (hst : J.p.nums.stages = a :: next :: rest)
    (hrd : H2U.roundsOfNums J.p.nums = some ds) (hor : H2U.testOracles J.p.nums = some os)
    (he : J.p.early = true) (h1 : J.p.answers = 1)
    (Y0 : DoorYes J w fr (D 0) a)
    (row : GroupRow) (L : GroupLayout) (hp : (J.recB w fr (D 0)).pass = .claim row L)
    (Dp : Plain) (hD : gpOf J.p (J.recB w fr (D 0)) a L = some Dp)
    (hok : ok (gpL J.p a row Dp) = true)
    (hhk : a.h ≤ a.k) (hhk' : next.h ≤ next.k) (hs : (sg a).Sized)
    (cu nx : IoppStage) (hcu : stageAt J.p 0 a = some cu) (hnx : stageAt J.p 1 next = some nx)
    (c : ℕ → ℕ → List UInt64) (R : PlainRows) (hC : ColsAt a Dp c R)
    (hS : StateAt a Dp (J.first w fr C) R)
    (htr : J.trees₀ w fr C.mem (J.first w fr C) = groupTrees Dp.ts (logAt Dp.book) c)
    (Y : FirstYes J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next (J.laid.drop 1) 1
      (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D)
    (hr : ∀ x ∈ (D (1 + 2 + ((sgOf a).h + (sgOf a).g))).poss, x < 2 ^ a.C.a)
    (ht : (D (1 + 2 + ((sgOf a).h + (sgOf a).g))).poss.length = a.t)
    (hf : CsFit (sgOf a) (sgOf next)) (hfit : FitAll next rest)
    (hLk : L.k = (sgOf a).h + (sgOf a).g) (hLh : L.h = (sgOf a).h)
    (hLl : 2 ^ L.logEll = a.C.l) (hLz : 2 ^ L.logEllZk = a.Z.l)
    (hsay : ∀ G, (((guardedProximityTestParts.front J.p).decide (J.rec₀ w fr) [] []).toOption.getD
        (J.rec₀ w fr)).st.groups[(((guardedProximityTestParts.front J.p).decide (J.rec₀ w fr) [] []).toOption.getD
        (J.rec₀ w fr)).g]? = some G →
      AllSay rdE (J.recB w fr (D 0)).st (runRows (((guardedProximityTestParts.front J.p).decide (J.rec₀ w fr) []
        []).toOption.getD (J.rec₀ w fr)).st G).toList (wordsAt (J.recB w fr (D 0)).st L R))
    (hroom : (sgOf a).h + 2 * (sgOf a).g + 1 ≤ (sgOf a).Z.l)
    (hZl : ((t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (J.laid.drop 1) 1
      (J.recB w fr (D 0)) (J.first w fr C) D).st.codes.mask.getD cu.maskCode default).ell = a.Z.l)
    (hOld : ∀ rows gp, (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (J.laid.drop 1) 1
      (J.recB w fr (D 0)) (J.first w fr C) D).pass = .single rows gp →
      OldOk (sgOf a) (sgOf next) (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a
        (J.laid.drop 1) 1 (J.recB w fr (D 0)) (J.first w fr C) D).st.codes rows nx.code
        nx.maskCode)
    (hwords : okE (((D (1 + 1 + ((sgOf a).h + (sgOf a).g))).elems.map E.ofTriple).getD
      (bitsAt J.p 0 next (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (J.laid.drop 1) 1
        (J.recB w fr (D 0)) (J.first w fr C) D)) zeroE) = true)
    (Inv : List Fmt.M1.Stage → ℕ → Fmt.M1.Stage → Laid → ℕ → T12 → PS → (ℕ → List UInt64) → Prop)
    (Post : T12 → Prop)
    (hstep : ∀ next rest j cur l o t P col, Inv (next :: rest) j cur l o t P col →
      StageYes J.p (coinsOf J.p.nums.stages C.hide C.rest) rest j cur next l o t P col D ∧
        Inv rest (j + 1) next (l.drop (cur.k + 3)) (o + ((sgOf cur).h + (sgOf cur).g) + 3)
          (sT3 J.p (coinsOf J.p.nums.stages C.hide C.rest) rest.isEmpty j cur next l o t P col
            (Johnson.Prover.Link.rowOf t) D)
          (sNext (coinsOf J.p.nums.stages C.hide C.rest) rest.isEmpty j cur next o P
            (Johnson.Prover.Link.rowOf t) D)
          (sCol (coinsOf J.p.nums.stages C.hide C.rest) rest.isEmpty j cur next o P
            (Johnson.Prover.Link.rowOf t) D))
    (hbase : ∀ j cur l o t P col, Inv [] j cur l o t P col →
      ∃ t', (guardedProximityTestParts.base J.p j cur (l.map (·.1))).decide t
        ((lastOut J.p j cur o t P col (Johnson.Prover.Link.rowOf t) D).rs.map noDigest)
        (lastOut J.p j cur o t P col (Johnson.Prover.Link.rowOf t) D).gs = .ok t' ∧ Post t')
    (hI : ClaimTrue (sgOf next)
        (t3At J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next (J.laid.drop 1) 1
          (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D)
        (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1 (J.first w fr C) D) →
      Inv rest 1 next ((J.laid.drop 1).drop (a.k + 3)) (1 + ((sgOf a).h + (sgOf a).g) + 3)
        (t3At J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next (J.laid.drop 1) 1
          (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D)
        (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1 (J.first w fr C) D)
        (aCol rest.isEmpty next
          (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1 (J.first w fr C) D))) :
    ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ w fr)
      ((testAll J w fr C D).rs.map noDigest) (testAll J w fr C D).gs = .ok t' ∧ Post t' := by
  obtain ⟨tB, hB⟩ := Y0.bat
  have eB : J.recB w fr (D 0) = tB := getD_of_ok hB
  have hs0 : J.s₀ = a := by
    unfold TestJob.s₀
    rw [hst]
    rfl
  -- the claim that is passed after the batching is true
  have hcl0 : ClaimTrue (sgOf a) (J.recB w fr (D 0)) (J.first w fr C) := by
    rw [eB] at hp hD hsay ⊢
    exact bat_claimTrue_state J.p he _ _ tB _ hB a row L hp Dp hD hLk hLh hLl hLz (J.first w fr C) R
      hS hsay
  -- the claim that is passed after the first stage is true
  have hpk := first_packs J w fr C
  rw [hs0] at hpk
  have hcl1 := first_claimTrue J.p (coinsOf J.p.nums.stages C.hide C.rest) rest a next
    (J.laid.drop 1) 1 (J.recB w fr (D 0)) (J.first w fr C) D he h1 rfl row L hp Dp hD hok hhk hhk'
    hs cu nx hcu hnx c R hC hS Y hr ht hf hLk hLh hcl0 hroom hpk hZl hOld hwords
  -- the stages' block accepts (`stages_yes`); then the whole block does (`test_yes`)
  obtain ⟨t', h3, hP⟩ := stages_yes J.p (coinsOf J.p.nums.stages C.hide C.rest) D Inv Post hstep
    hbase rest 0 a next (J.laid.drop 1) 1 (J.recB w fr (D 0)) (J.first w fr C) _ Y hfit (hI hcl1)
  refine ⟨t', test_yes J w fr C D a (next :: rest) ds os hst hrd hor Y0 t' ?_, hP⟩
  rw [htr]
  exact h3

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.test_accepts
