-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/WholeAll.lean: the decision of a proximity test's block accepts
all that `testAll` (Test.lean in this folder) shows at a job whose functions are the caller's, with
no acceptance asked anywhere, where the first fold's fresh table has come earlier. That is: no
hypothesis says that a `decide` returns `.ok`. `test_accepts_shape` (WholeShape.lean in this folder)
states the same with the invariant of the stages from the second on as a free parameter. Here that
parameter is set to `BodyInv` (Johnson/Prover/Link/BodyInv.lean). General in the job, the prover's
input, the front, the coins and the challenges. Two theorems with their proofs; no definition.

In the list: a job J (`TestJob`, Test.lean) is what a caller supplies for its test. Among its fields
are the place `J.p` (`P12`, Johnson/Desc/K12/Frame.lean: the numbers of a place that holds a
proximity test, among them its list of stages, `Fmt.M1.Stage`) and three functions of the prover's
input w and the front fr (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean: what precedes the test).
One of the three gives the state on entry, `J.rec₀ w fr`. C: the coins that `testAll` reads
(`TestCoins`). D: the sampled challenges by the round's number. The block is `proximityTestKind guardedProximityTestParts J.p`
(`Block`, Johnson/Desc/Block.lean; `proximityTestKind`, Frame.lean). It has a part without rounds, the batching
(the round "BAT"), then the stages. A stage that is not the last has a fold, a code switch and the
batching after the switch.

  `test_accepts_all`: at two stages or more, under the hypotheses below: the block's `decide`, run
    from `J.rec₀ w fr` on the rounds of `testAll J w fr C D`, each without its digest (`noDigest`),
    and on its groups of opened columns (`gs`), returns `.ok`. Nothing is asked or said on what is
    left untested
  `test_left_all`: under the same hypotheses and hleft (nothing is left untested after the
    batching): it returns `.ok t'`, and nothing is left untested at the statement of t'

By what. Both proofs call `test_accepts_shape`. `test_accepts_all` sets its invariant to `BodyInv`
over `PlanAll` (Johnson/Prover/Link/BodyCloseB.lean); `test_left_all` to that together with
`ChainEnd.NothingLeft` at the state's statement. That a stage which is not the last accepts under
`BodyInv` and keeps it: `hstep_at`; that it keeps `NothingLeft`: `hstep_left` (both
Johnson/Prover/Link/BodyCloseS.lean). The same for the last stage: `hbase_at`, `hbase_left`
(BodyCloseB.lean). That `BodyInv` holds after the first switch, where the claim that is passed there
is true (`ClaimTrue`, Johnson/Desc/K12/Honest/ClaimTrue.lean): `bodyInv_first_all`
(Johnson/Prover/Link/BodyBehindAll.lean), from `FirstYes`, which `first_of_shape`
(Johnson/Desc/K12/Honest/Shape/FirstTerm.lean) gives, and from `SwitchIn`
(Johnson/Prover/Link/FormBehindAny.lean), which `switchIn_shape`
(Johnson/Desc/K12/Honest/Shape/SwitchInShape.lean) derives. `recB_eq` (WholeShape.lean) rewrites the
job's state after the batching. In `test_left_all`, `left_any` (FormBehindAny.lean) gives
`NothingLeft` after the first switch from hleft; the two acceptances that it takes come from
`FirstYes`, by `ranged_ok` (Johnson/Desc/K12/Law/BaseGives.lean) and `getD_of_ok`
(Johnson/Prover/Link/BodyYes.lean).

Hypotheses. Those from hst to V are the hypotheses of `test_accepts_shape` but for those on its two
free parameters, the invariant and what holds at the end. hst: the place's stages are a, next and
the list rest. hrd, hor: the place's numbers give rounds (`roundsOfNums`) and oracle messages
(`testOracles`). h: the test `Sh.doorB` (Johnson/Desc/K12/Honest/Shape/TestDoor.lean) passes at the
shape (`testSh`) of the state on entry. hm: that state's field `mask` is `some id`: the fresh table
has come earlier. htidy, hv: `stTidyB` passes at that state's statement, `claimsB` at the state.
hpl: no row that the test takes in has a written-out factor (`PlainRow`,
OnBytes/Slice/BlkPlain.lean). Pl: `SwitchPub` (Johnson/Desc/K12/Honest/Shape/TestSwitch.lean) at the
first switch. hB, hF: `batCut` and `foldCut` pass at the declared rounds of the batching and of the
first fold. fB: what "BAT" sampled has the declared form (`roundsFit`). A: `TermAsks`
(FirstTerm.lean) at the state after the batching. nB, oB: the batching's block has one round and no
opening. V: `RestAsks` (WholeShape.lean) at whatever claim is passed after the batching; of the
claim it reads the layout L only: no field of `RestAsks` reads row. Sp: what is public at the first
switch (`FirstSwitchPlan`, BodyBehindAll.lean). hPlan: the plan of the later stages (`PlanAll`). Sp
and hPlan are at the codes of the state after the first fold. hFit: the later challenges' form
(`FitFrom`, Johnson/Prover/Link/BodyFit.lean). hleft, in `test_left_all` only:
`ChainEnd.NothingLeft` at the statement after the batching.

Limits.
- None of the hypotheses is proved here.
- A, V, Sp, hPlan and hleft are stated at `J.recB w fr (D 0)` (Test.lean) or at `t1At`
  (Johnson/Desc/K12/Honest/FirstYes.lean). These terms run the `decide` functions of the front, the
  batching and the first fold, and keep the state before a part that rejects.
- Values that meet all of them together, by the Boolean test `allB` (AllB.lean), from which they are
  derived: ToyAll.lean, ToyCame.lean and ToyLate.lean in this folder, each at a small made-up place
  of three stages or more. At exactly two stages no value is given that meets them: the Boolean
  tests `coreB` (AllB.lean) and `planB` (PlanB.lean) ask three.
- Both theorems depend on three files of Johnson/Prover/Link/: BodyBehindAll.lean,
  BodyBehindFirst.lean and LastBehindFirst.lean.
- The hypotheses cannot be met where the first fold sends its own table: `PlanAll` asks that the
  place has none (`p.nums.ownMask = false`, in `PlanFrom`, Johnson/Prover/Link/FormStepPlan.lean),
  and the clause of `SwitchIn` on the roots is false there.
- Nor can they be met where a row taken in has a written-out factor.
- "Accepts" is `Block.decide ... = .ok`: `planOk` and the two tests of `Block.step` before the
  decision are not concluded here (see SaysYesK12.lean).
- The decision is handed the rounds and the groups of opened columns of `testAll`, not its trees'
  columns (`tr`).
- The job's three functions are free parameters. The decision is run from `J.rec₀ w fr`: no
  statement that this state is the verifier's. No honest prover is defined here.
- "Nothing is left untested" is the library's mark "a test has begun on every group, and every
  sampled oracle message is in such a group" (`ChainEnd.NothingLeft`,
  Johnson/Desc/ChainEndLaw.lean): the hypothesis hleft of `test_left_all` cannot be met where a
  group's test is still to come, or a sampled message is in no group whose test has begun.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.WholeShape
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

/-- **The decision of the test's block accepts the rounds and the opened columns of `testAll`.** No
hypothesis says that a `decide` returns `.ok`; nothing is asked or said on what is left untested. -/
theorem test_accepts_all (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
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
    ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ w fr)
      ((testAll J w fr C D).rs.map noDigest) (testAll J w fr C D).gs = .ok t' := by
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
  obtain ⟨t', e, -⟩ := test_accepts_shape J w fr C D a next rest ds os hst hrd hor Dp c i n id dS dC
    h hm htidy hpl hv Pl hB hF fB A nB oB R V
    (BodyInv J.p (coinsOf J.p.nums.stages C.hide C.rest) (PlanAll J.p) D) (fun _ => True)
    (hstep_at J.p (coinsOf J.p.nums.stages C.hide C.rest) D)
    (fun j cur l o t P col x => by
      obtain ⟨t', e⟩ := hbase_at J.p (coinsOf J.p.nums.stages C.hide C.rest) D j cur l o t P col x
      exact ⟨t', e, trivial⟩)
    hI
  exact ⟨t', e⟩

/-- **The same, and nothing is left untested after it, where nothing is left untested after the
batching** (`ChainEnd.NothingLeft`; the hypothesis hleft). -/
theorem test_left_all (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
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
    (hleft : ChainEnd.NothingLeft (J.recB w fr (D 0)).st)
    (Sp : FirstSwitchPlan J.p (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS J.p) 1
      (J.recB w fr (D 0)) (J.first w fr C) D).st.codes 0 a next n rest)
    (hPlan : PlanAll J.p rest (0 + 1) next ((laidS J.p).drop (a.k + 3))
      (t1At J.p (coinsOf J.p.nums.stages C.hide C.rest) 0 a (laidS J.p) 1 (J.recB w fr (D 0))
        (J.first w fr C) D).st.codes)
    (hFit : FitFrom D ((laidS J.p).drop (a.k + 3)) (1 + ((sgOf a).h + (sgOf a).g) + 3)) :
    ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ w fr)
      ((testAll J w fr C D).rs.map noDigest) (testAll J w fr C D).gs = .ok t' ∧
      ChainEnd.NothingLeft t'.st := by
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
  -- `NothingLeft` holds after the first switch and the batching after it
  have hl3 : ChainEnd.NothingLeft (t3At J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next
      (laidS J.p) 1 (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c)
      D).st := by
    obtain ⟨t₂, hs2⟩ := Y.switch
    obtain ⟨t₃, hs3⟩ := Y.behind
    have e2 : aRec2 J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next (laidS J.p) 1
        (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D = t₂ :=
      getD_of_ok hs2
    have e3 : t3At J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 a next (laidS J.p) 1
        (J.recB w fr (D 0)) (J.first w fr C) (groupTrees Dp.ts (logAt Dp.book) c) D = t₃ :=
      getD_of_ok hs3
    rw [e2] at hs3
    have h2 := (ranged_ok _ _ _ _ _ _ hs2).1
    have h3 : (behindJ J.p (0 + 1) next ((((laidS J.p).drop (1 + a.k)).take 2).map (·.1))).decide
        t₂ [] [] = .ok t₃ := hs3
    rw [e3]
    exact left_any Pl.early Pl.one Pl.stageN In.pass hst1 hleft h2 h3
  exact test_accepts_shape J w fr C D a next rest ds os hst hrd hor Dp c i n id dS dC
    h hm htidy hpl hv Pl hB hF fB A nB oB R V
    (fun rest j cur l o t P col =>
      BodyInv J.p (coinsOf J.p.nums.stages C.hide C.rest) (PlanAll J.p) D rest j cur l o t P col ∧
        ChainEnd.NothingLeft t.st)
    (fun t' => ChainEnd.NothingLeft t'.st)
    (fun next rest j cur l o t P col x =>
      ⟨(hstep_at J.p (coinsOf J.p.nums.stages C.hide C.rest) D next rest j cur l o t P col x.1).1,
        (hstep_at J.p (coinsOf J.p.nums.stages C.hide C.rest) D next rest j cur l o t P col x.1).2,
        hstep_left J.p (coinsOf J.p.nums.stages C.hide C.rest) D next rest j cur l o t P col x.1
          x.2⟩)
    (fun j cur l o t P col x =>
      hbase_left J.p (coinsOf J.p.nums.stages C.hide C.rest) D j cur l o t P col x.1 x.2)
    (fun hc => ⟨hI hc, hl3⟩)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.test_accepts_all
#print axioms ProofFile.Honest.K12.test_left_all
