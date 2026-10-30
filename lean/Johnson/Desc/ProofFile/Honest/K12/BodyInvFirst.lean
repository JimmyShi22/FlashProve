-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/BodyInvFirst.lean: after the first stage of a proximity test the
invariant of the later stages holds (`BodyInv`, Johnson/Prover/Link/BodyInv.lean), at the values
that `testAll` (Test.lean in this folder) computes there, under the hypotheses of `test_accepts_all`
(WholeAll.lean in this folder). The proof of that theorem, with the proofs of the theorems that it
calls, derives this statement on its way; none of them states it. Here it is stated, with the three
values named: a state of the verifier's type, a state of the prover's type and the new tree's
column. General in the job, the prover's input, the front, the coins and the challenges. A
definition, a theorem and its proof.

In the list: a job J (`TestJob`, Test.lean) is what a caller supplies for its test. Among its fields
are the place `J.p` (`P12`, Johnson/Desc/K12/Frame.lean: the numbers of a place that holds a
proximity test, among them its list of stages, `Fmt.M1.Stage`) and three functions of the prover's
input w and the front fr (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean: what precedes the test).
One of the three gives the state on entry, `J.rec₀ w fr`. a, next, rest: the first stage, the
second, the list of the others. Before the stages comes the batching (the round "BAT"). The first
stage is the first fold, the first code switch and the batching after the switch. C: the coins that
`testAll` reads (`TestCoins`, Test.lean). K is short for `coinsOf J.p.nums.stages C.hide C.rest`
(Coins.lean in this folder), of the type `BCoins` (Johnson/Prover/Link/BodyAll.lean). D: the sampled
challenges by the round's number, "BAT" being round 0. Dp: the library's plain data on the group of
oracle messages under test (`Plain`, Johnson/Desc/K12/Law/FirstOk.lean). c: a tree's column at a
position, as words. The group's trees are `groupTrees Dp.ts (logAt Dp.book) c`
(Johnson/Desc/K12/Honest/GroupState.lean): for each tree's number in `Dp.ts`, its depth by `Dp.book`
and its column by c.

  `bodyInv_behind_first`: under the hypotheses of `test_accepts_all`, the same binders in the same
    order: `Wanted J w fr C D a next rest Dp c`
  `Wanted J w fr C D a next rest Dp c`: a definition: `BodyInv J.p K (PlanAll J.p) D` (`PlanAll`,
    Johnson/Prover/Link/BodyCloseB.lean) before the second stage. Its eight arguments: the list
    rest; the stage's number 0 + 1; the stage next; the declared rounds from the second stage on,
    `(laidS J.p).drop (a.k + 3)` (`laidS`, Johnson/Desc/K12/Law/ReadsK.lean); the number of that
    stage's first round, 1 + (h + g) + 3 with h and g of `sgOf a`
    (Johnson/Desc/K12/Law/ChainOf.lean); and the three values. The first is `t3At`
    (Johnson/Desc/K12/Honest/FirstYes.lean), of the type `T12` of the verifier's state inside a test
    (Johnson/Desc/K12/Join.lean): what the decisions of the first fold, the first switch and the
    batching after it return in turn, from the job's state after "BAT", `J.recB w fr (D 0)`, on the
    first stage's rounds and on the columns of the group's trees at the sampled positions; where a
    decision rejects, the state before it is kept. The second is `qAt` (FirstYes.lean), of the type
    `PS` of what a prover holds at a stage (Johnson/Prover/Link/BodyState.lean): the state after the
    switch, computed from the job's first state `J.first w fr C`, K and D. The third is `aCol`
    (Johnson/Desc/K12/Honest/Stages.lean) at `qAt`: the written column of the tree that the switch
    sends

By what. `bodyInv_first_all` (Johnson/Prover/Link/BodyBehindAll.lean) gives `Wanted` where the claim
that is passed after the first stage is true (`ClaimTrue`, Johnson/Desc/K12/Honest/ClaimTrue.lean).
It takes `FirstYes` (FirstYes.lean), which `first_of_shape`
(Johnson/Desc/K12/Honest/Shape/FirstTerm.lean) gives; `SwitchIn`
(Johnson/Prover/Link/FormBehindAny.lean), which `switchIn_shape`
(Johnson/Desc/K12/Honest/Shape/SwitchInShape.lean) gives; and Sp, hPlan and hFit. `recB_eq`
(WholeShape.lean in this folder) rewrites the job's state after "BAT". Up to here the proof is that
of `test_accepts_all`. That the claim is true is proved inside the proof of `test_accepts`
(WholeTest.lean in this folder) and is not in its conclusion. `test_accepts_shape`
(WholeShape.lean), which calls `test_accepts` through `accepts_of_first`, is general in its
invariant Inv and in Post, what holds of the state at the end. The proof calls `test_accepts_shape`
with Inv set to `BodyInv` together with `Wanted`, and Post to `Wanted`; `Wanted` depends on no
argument of Inv or of Post. After the first stage, where the claim is true, both clauses of Inv are
what `bodyInv_first_all` gives. `hstep_at` (Johnson/Prover/Link/BodyCloseS.lean) and `hbase_at`
(BodyCloseB.lean) prove for `BodyInv` the hypotheses hstep and hbase of `test_accepts_shape`: on a
stage that is not the last, and on the last. The second clause is handed on unchanged and comes out
as Post. The acceptance that `test_accepts_shape` concludes with it is dropped.

Hypotheses. hst: the place's stages are a, next and the list rest. hrd, hor: the place's numbers
give rounds ds (`roundsOfNums`) and oracle messages os (`testOracles`; both
Johnson/Desc/K12/TestEntries.lean). h: the test `Sh.doorB`
(Johnson/Desc/K12/Honest/Shape/TestDoor.lean) passes at the shape (`testSh`,
Johnson/Desc/K12/Honest/Shape/Test.lean) of the state on entry; i and n give the numbers of the
first two stages' codes. hm: that state's field `mask` is `some id`: the fresh table has come
earlier. htidy, hv: `stTidyB` (Johnson/Desc/Ground/Shape/Marks.lean) passes at that state's
statement, `claimsB` (TestDoor.lean) at the state. hpl: no row that the test takes in has a
written-out factor (`PlainRow`, OnBytes/Slice/BlkPlain.lean). Pl: `SwitchPub`
(Johnson/Desc/K12/Honest/Shape/TestSwitch.lean) at the first switch, with its two declared rounds dS
and dC. hB, hF: `batCut` (Johnson/Prover/Link/FormBat.lean) and `foldCut`
(Johnson/Prover/Link/FormFold.lean) pass at the declared rounds of the batching and of the first
fold. fB: what "BAT" sampled has the declared form (`roundsFit`, Johnson/Desc/Block.lean). A:
`TermAsks` (FirstTerm.lean) at the state after "BAT". nB, oB: the batching's block has one round and
no opening. V: `RestAsks` (WholeShape.lean), with the prover's rows as plain functions R
(`PlainRows`, Johnson/Desc/K12/Honest/FirstRows.lean), at whatever claim is passed after "BAT". Sp:
what is public at the first switch (`FirstSwitchPlan`, BodyBehindAll.lean). hPlan: `PlanAll` from
the second stage on. Sp and hPlan are at the codes of the state after the first fold (`t1At`,
FirstYes.lean). hFit: the form of the challenges from the second stage's first round on (`FitFrom`,
Johnson/Prover/Link/BodyFit.lean).

Limits.
- Those of WholeAll.lean: none of the hypotheses is proved here.
- The hypotheses cannot be met where the first fold sends its own table: `PlanAll` asks that the
  place has none (`p.nums.ownMask = false`, in `PlanFrom`, Johnson/Prover/Link/FormStepPlan.lean).
- Nor can they be met where a row that the test takes in has a written-out factor (hpl).
- Values that meet them all together: those that the limits of WholeAll.lean name, at small made-up
  places of three stages or more each. BodyInvMember.lean in this folder calls this theorem at the
  places of ToyAll.lean and ToyCame.lean. At exactly two stages no value is given that meets them.
- The job's three functions are free parameters. `t3At` is computed from the state on entry,
  `J.rec₀ w fr`: no statement that this state is the verifier's, and so none that `t3At` is. `qAt`
  is computed from what the caller's function `rows₀` returns. No honest prover is defined here.
- "The values that `testAll` computes there" is read off the definitions: `testAll` calls
  `stagesAll` (Stages.lean), which goes on to the second stage at these values. No theorem here
  states it. `testAll` calls it at the trees `J.trees₀ w fr C.mem (J.first w fr C)`, and `Wanted`
  has the group's trees: that the two lists are equal is the clause `trees` of `RestAsks`, in V.
- No acceptance is concluded here.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.WholeAll
import Johnson.Desc.K12.Honest.Shape.SwitchInShape
import Johnson.Prover.Link.BodyBehindAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (tBat TermAsks first_of_shape switchIn_shape SwitchPub claimsB testSh)

variable {W X : Type}

/-- The statement of `bodyInv_behind_first`: `BodyInv` over `PlanAll` before the second stage, at
`t3At` (of the type `T12`, after the first stage), at `qAt` (of the type `PS`, after the first
switch) and at `aCol` (the written column of the tree that the switch sends). -/
def Wanted (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (Dp : Plain) (c : ℕ → ℕ → List UInt64) :
    Prop :=
  BodyInv J.p (coinsOf J.p.nums.stages C.hide C.rest) (PlanAll J.p) D rest (0 + 1) next
    ((laidS J.p).drop (a.k + 3)) (1 + ((sgOf a).h + (sgOf a).g) + 3)
    (t3At J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next (laidS J.p) 1
      (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D)
    (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1 (J.first w fr C) D)
    (aCol rest.isEmpty next
      (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1 (J.first w fr C) D))

/-- **`BodyInv` holds after the first stage**, at the values of `Wanted`, under the hypotheses of
`test_accepts_all` (WholeAll.lean in this folder). None of them is proved here. -/
theorem bodyInv_behind_first (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (ds : List Fmt.DeclaredRound) (os : List (List (ℕ × ℕ)))
    (hst : J.p.nums.stages = a :: next :: rest)
    (hrd : H2U.roundsOfNums J.p.nums = some ds) (hor : H2U.testOracles J.p.nums = some os)
    (Dp : Plain) (c : ℕ → ℕ → List UInt64) (i : ℕ × ℕ) (n : IoppStage) (id : ℕ)
    (dS dC : Fmt.DeclaredRound)
    (h : Sh.doorB J.p a next (((laidOf J.p).take 1).map (·.1)) i (n.code, n.maskCode)
      (testSh (J.rec₀ w fr)) = true)
    (hm : (J.rec₀ w fr).mask = some id) (htidy : stTidyB (J.rec₀ w fr).st = true)
    (hpl : ∀ G, (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? = some G →
      ∀ r ∈ (runRows (J.rec₀ w fr).st G).toList, PlainRow r)
    (hv : claimsB (J.rec₀ w fr) = true)
    (Pl : SwitchPub J.p (J.rec₀ w fr).st.codes 0 a next rest.isEmpty
      ⟨i.1, i.2, a.k, a.h⟩ n dS dC)
    (hB : batCut (((laidOf J.p).take 1).map (·.1)) = true)
    (hF : foldCut a.k (((laidS J.p).take (1 + a.k)).map (·.1)) = true)
    (fB : roundsFit (((laidOf J.p).take 1).map (·.1)) [⟨[], D 0⟩] = true)
    (A : TermAsks J.p (coinsOf J.p.nums.stages C.hide C.rest) rest a next 1
      (J.recB w fr (D 0)) (J.first w fr C) D Dp c ⟨i.1, i.2, a.k, a.h⟩ dS dC)
    (nB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).rounds.length = 1)
    (oB : (batAt guardedProximityTestParts J.p J.laid : Block T12 Unit).openings = 0)
    (R : PlainRows)
    (V : ∀ row L, (J.recB w fr (D 0)).pass = .claim row L →
      RestAsks J w fr C D a next rest Dp c R row L ⟨i.1, i.2, a.k, a.h⟩ n)
    (Sp : FirstSwitchPlan J.p (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS J.p) 1
      (J.recB w fr (D 0)) (J.first w fr C) D).st.codes 0 a next n rest)
    (hPlan : PlanAll J.p rest (0 + 1) next ((laidS J.p).drop (a.k + 3))
      (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS J.p) 1 (J.recB w fr (D 0))
        (J.first w fr C) D).st.codes)
    (hFit : FitFrom D ((laidS J.p).drop (a.k + 3)) (1 + ((sgOf a).h + (sgOf a).g) + 3)) :
    Wanted J w fr C D a next rest Dp c := by
  have eR := recB_eq J w fr (D 0)
  obtain ⟨-, -, -, -, Y⟩ := first_of_shape J.p (coinsOf J.p.nums.stages C.hide C.rest)
    rest a next 1 (J.rec₀ w fr) (J.first w fr C) D (D 0) Dp c i n id dS dC h hm htidy hpl
    hv Pl hB hF fB (by rw [← eR]; exact A)
  obtain ⟨rows, In, hst1⟩ := switchIn_shape J.p (coinsOf J.p.nums.stages C.hide C.rest) rest a
    next 1 (J.rec₀ w fr) (J.first w fr C) D (D 0) Dp c i n id dS dC h hm htidy hpl hv Pl hB hF fB
    (by rw [← eR]; exact A)
    (noDigest ⟨[.answer (ofE (aAns J.p 0 a next 1 D (t1At J.p
      (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS J.p) 1 (J.recB w fr (D 0))
      (J.first w fr C) D) (qAt (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next 1
      (J.first w fr C) D)))], D (1 + 2 + ((sgOf a).h + (sgOf a).g))⟩) rfl
  rw [← eR] at Y In hst1
  have hI := bodyInv_first_all J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next
    (laidS J.p) 1 (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D n _
    rows Y Sp In hPlan hFit
  -- `test_accepts_shape` is general in its invariant: `Wanted` goes into it as a second clause
  obtain ⟨_, -, hG⟩ := test_accepts_shape J w fr C D a next rest ds os hst hrd hor Dp c i n id dS dC
    h hm htidy hpl hv Pl hB hF fB A nB oB R V
    (fun rest' j cur l o t P col =>
      BodyInv J.p (coinsOf J.p.nums.stages C.hide C.rest) (PlanAll J.p) D rest' j cur l o t P col ∧
        Wanted J w fr C D a next rest Dp c)
    (fun _ => Wanted J w fr C D a next rest Dp c)
    (fun next' rest' j cur l o t P col x =>
      ⟨(hstep_at J.p (coinsOf J.p.nums.stages C.hide C.rest) D next' rest' j cur l o t P col
          x.1).1,
        (hstep_at J.p (coinsOf J.p.nums.stages C.hide C.rest) D next' rest' j cur l o t P col
          x.1).2, x.2⟩)
    (fun j cur l o t P col x => by
      obtain ⟨t', e⟩ := hbase_at J.p (coinsOf J.p.nums.stages C.hide C.rest) D j cur l o t P col x.1
      exact ⟨t', e, x.2⟩)
    (fun hc => ⟨hI hc, hI hc⟩)
  exact hG

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.bodyInv_behind_first
#print axioms ProofFile.Honest.K12.Wanted
